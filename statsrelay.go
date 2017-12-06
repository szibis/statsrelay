package main

import (
	"bytes"
	"errors"
	"expvar"
	"flag"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	_ "net/http/pprof"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/fsnotify/fsnotify"
	"github.com/jpillora/backoff"
	//"github.com/kr/pretty"
	"github.com/paulbellamy/ratecounter"
	zerolog "github.com/rs/zerolog"
	log "github.com/rs/zerolog/log"
	"github.com/spf13/viper"
	"github.com/tevjef/go-runtime-metrics/influxdb"
	validator "gopkg.in/go-playground/validator.v9"
)

// VERSION shows statsrelay version
const VERSION string = "0.2.0"

// BUFFERSIZE controls the size of the [...]byte array used to read UDP data
// off the wire and into local memory.  Metrics are separated by \n
// characters.  This buffer is passed to a handler to proxy out the metrics
// to the real statsd daemons.
const BUFFERSIZE int = 1 * 1024 * 1024 // 1MiB

// prefix is the string that will be prefixed onto self generated stats.
// Such as <prefix>.statsProcessed.  Default is "statsrelay"
var prefix string

// udpAddr is a mapping of HOST:PORT:INSTANCE to a UDPAddr object
var udpAddr = make(map[string]*net.UDPAddr)

// tcpAddr is a mapping of HOST:PORT:INSTANCE to a TCPAddr object
var tcpAddr = make(map[string]*net.TCPAddr)

// mirror is a HOST:PORT address for mirroring raw statsd metrics
var mirror string

// hashRing is our consistent hashing ring.
var hashRing = NewJumpHashRing(1)

// totalMetrics tracks the totall number of metrics processed
var totalMetrics uint32

// Time we began
var epochTime int64

// loglevel string for setting log level in statsrelay with available options:
// Debug, Info, Warn, Error, Fatal, Panic and Quiet for quiet mode
var logLevel string

// Log-only mode
var logonly bool

// IP protocol set for sending data target
var sendproto string

// IP protocol set for sending data target to mirrored statsd original trafic
var mirrorproto string

// packetLen is the size in bytes of data we stuff into one packet before
// sending it to statsd. This must be lower than the MTU, IPv4 header size
// and UDP header size to avoid fragmentation and data loss.
var packetLen int

// Maximum size of buffer
var bufferMaxSize int

// TCPtimeout duration value for for remote TCP connection
var TCPtimeout time.Duration

// profiling bool value to enable disable http endpoint for profiling
var profiling bool

// profilingBind string value for pprof http host:port data
var profilingBind string

// version bool value for print version only
var version bool

// maxprocs int value to set GOMAXPROCS
var maxprocs int

// TCPMaxRetries int value for number of retries in dial tcp
var TCPMaxRetries int

// TCPMinBackoff duration value for minimal backoff limit time
var TCPMinBackoff time.Duration

// TCPMaxBackoff duration value for maximum backoff limit time
var TCPMaxBackoff time.Duration

// TCPFactorBackoff float64 value for backoff factor
var TCPFactorBackoff float64

// Definitions []string set of strings
var Definitions []string

// defaultPolicy string value for setting default rules policy
// Available options are: drop or pass or log (log-only)
var defaultPolicy string

// rulesConfig string value for config file name with match rules
var rulesConfig string

// testRulesConfig bool value for testing rules config validity
var rulesValidationTest bool

// watchRulesConfig bool value for enabling watching config changes and reloading runtime values
var watchRulesConfig bool

// counter int for rate per second of all processed metics
var counter *ratecounter.RateCounter

var isConsole bool

type rulesDef struct {
	Rules []struct {
		Name      string   `mapstructure:"name" validate:"required,gt=0"`
		Match     string   `mapstructure:"match" validate:"required,gt=0"`
		Replace   string   `mapstructure:"replace" validate:"-"`
		Policy    string   `mapstructure:"policy" validate:"eq=pass|eq=drop"`
		StopMatch bool     `mapstructure:"stop_match" validate:"-"`
		Tags      []string `mapstructure:"tags" validate:"unique"`
		reMatch   *regexp.Regexp
	} `mapstructure:"rules"`
}

type replaceStruct struct {
	Replaced   string
	countMatch int
	lastPolicy string
}

// Rules to rulesDef struct
var Rules rulesDef

// use a single instance of Validate, it caches struct info
var validate *validator.Validate

// sockBufferMaxSize() returns the maximum size that the UDP receive buffer
// in the kernel can be set to.  In bytes.
func getSockBufferMaxSize() (int, error) {

	// XXX: This is Linux-only most likely
	data, err := ioutil.ReadFile("/proc/sys/net/core/rmem_max")
	if err != nil {
		return -1, err
	}

	data = bytes.TrimRight(data, "\n\r")
	i, err := strconv.Atoi(string(data))
	if err != nil {
		log.Error().
			Msgf("Could not parse /proc/sys/net/core/rmem_max")
		return -1, err
	}

	return i, nil
}

// metricMatchReplace() matches metric based on regexp definition rules
func metricMatchReplace(metric string, rules *rulesDef, policyDefault string) replaceStruct {
	var (
		matchRule         string
		replaceRule       string
		policy            string
		lastMatchedPolicy string
		replaced          string
		matched           int
		countMatch        int
		stopMatch         bool = false
		tagMetric         string
		sumElapsed        time.Duration
		elapsed           time.Duration
		//returnStruct      replaceStruct
	)

	//areplace := make([]string, 0)
	ruleNames := make([]string, 0)
	sumStart := time.Now()
	rrules := rules.Rules
	for i := range rrules {
		if rrules[i].reMatch == nil {
			rrules[i].reMatch = regexp.MustCompile(rrules[i].Match)
		}

		re := rrules[i].reMatch

		if rrules[i].Policy != "" {
			policy = rrules[i].Policy
		} else {
			policy = policyDefault
		}
		if replaced == "" {
			log.Info().
				Msgf("metric before: %s", metric)
			start := time.Now()
			match := re.FindAllString(metric, -1)
			// send unchanged metric if no match and go to next rule
			if match == nil {
				stopMatch = false
				continue
			}
			if match != nil {
				matched++
				if rrules[i].Tags != nil {
					tagMetric = genTags(metric, rrules[i].Tags, rrules[i].Replace)
				}
				if tagMetric != "" {
					replaced = re.ReplaceAllString(metric, tagMetric)
				} else {
					replaced = re.ReplaceAllString(metric, rrules[i].Replace)
				}
			}
			log.Info().
				Msgf("metric after replace: %s", metric)
			elapsed = time.Since(start)
			// TODO: review below conditions and try to simplify them
			if policy == "drop" {
				// drop and stop processing
				if rrules[i].StopMatch && match != nil {
					replaced = ""
					stopMatch = true
					break
				}
				// return replaced metric and and go to next rule
				if match != nil {
					stopMatch = false
					continue
				}
				// return unchanged metric if no match and go tu next rule
				stopMatch = false
				continue
			}
			// stop processing next rules
			if rrules[i].StopMatch {
				stopMatch = true
				break
			}
			// replace and go to next rule
			ruleNames = append(ruleNames, rrules[i].Name)
			lastMatchedPolicy = policy
			// if metric was replaced before use it against next rules
		} else {
			log.Info().
				Msgf("replace before replace: %s", replaced)
			start := time.Now()
			match := re.FindAllString(replaced, -1)
			// send unchanged metric if no match and go to next rule
			if match == nil {
				stopMatch = false
				continue
			}
			if match != nil {
				matched++
				if rrules[i].Tags != nil {
					tagMetric = genTags(replaced, rrules[i].Tags, rrules[i].Replace)
				}
				if tagMetric != "" {
					replaced = re.ReplaceAllString(replaced, tagMetric)
				} else {
					replaced = re.ReplaceAllString(replaced, rrules[i].Replace)
				}
			}
			log.Info().
				Msgf("replace after replace: %s", replaced)
			// TODO: review below conditions and try to simplify them
			if policy == "drop" {
				// drop and stop processing
				if rrules[i].StopMatch && match != nil {
					replaced = ""
					stopMatch = true
					break
				}
				// return replaced metric and and go to next rule
				if match != nil {
					stopMatch = false
					continue
				}
				// return unchanged metric if no match and go tu next rule
				stopMatch = false
				continue
			}
			// stop processing next rules
			if rrules[i].StopMatch {
				stopMatch = true
				break
			}
			// replace and go to next rule
			ruleNames = append(ruleNames, rrules[i].Name)
			lastMatchedPolicy = policy
			elapsed = time.Since(start)
		}
		countMatch = len(ruleNames)
		if countMatch == 0 {
			policy = policyDefault
		}
		// per match log info
		log.Debug().
			Str("policy", strings.ToUpper(policy)).
			Str("rule-matched", matchRule).
			Str("replace-rule", replaceRule).
			Str("replaced", replaced).
			Int("matches", countMatch).
			Dur("replace-time", elapsed).
			Msg("Single rule match")
			//log.Print("[%s] MatchRule: %s Rule: %s, Final: %s, Match: %d in [%s]", strings.ToUpper(policy), matchRule, replaceRule, replaced, countMatch, elapsed)
		// don't process next rules
		if stopMatch {
			break
		}
	}
	// use default policy for unmatched metrics
	if len(ruleNames) == 0 {
		lastMatchedPolicy = defaultPolicy
	}
	sumElapsed = time.Since(sumStart)
	// summary log info per metric with all matches and replaces
	log.Info().
		Str("policy", strings.ToUpper(policy)).
		Str("rules-matched", strings.Join(ruleNames, ",")).
		Str("replaced", replaced).
		Int("matches", countMatch).
		Dur("replace-time", sumElapsed).
		Msg("All rules match")
	//areplace[0] = replaced
	//log.Info().
	//	Msgf("areplace: %s", replaced)
	return replaceStruct{Replaced: replaced, countMatch: countMatch, lastPolicy: lastMatchedPolicy}
}

// getMetricName() parses the given []byte metric as a string, extracts
// the metric key name and returns it as a string.
func getMetricName(metric []byte) (string, error) {
	// statsd metrics are of the form:
	//    KEY:VALUE|TYPE|RATE or KEY:VALUE|TYPE|RATE|#tags
	length := bytes.IndexByte(metric, byte(':'))
	if length == -1 {
		return "error", errors.New("Length of -1, must be invalid StatsD data")
	}
	return string(metric[:length]), nil
}

// genTags() add metric []byte and metricTags string, return string
// of metrics with additional tags
func genTags(metric string, metricTags []string, metricReplace string) string {
	// statsd metrics are of the form:
	// KEY:VALUE|TYPE|RATE or KEY:VALUE|TYPE|RATE|#tags
	// This function add or extend #tags in metric
	tagsTmp := strings.Join(metricTags, ",")
	if strings.Contains(metric, "|#") {
		return fmt.Sprintf("%s,%s", metricReplace, tagsTmp)
	}
	if tagsTmp != "" {
		return fmt.Sprintf("%s|#%s", metricReplace, tagsTmp)
	}
	return metricReplace
}

// sendPacket takes a []byte and writes that directly to a UDP socket
// that was assigned for target.
func sendPacket(buff []byte, target string, sendproto string, TCPtimeout time.Duration, boff *backoff.Backoff, logonly bool) {
	switch sendproto {
	case "UDP":
		if !logonly {
			conn, err := net.ListenUDP("udp", nil)
			if err != nil {
				log.Panic().
					Err(err)
				//log.Panicln(err)
			}
			conn.WriteToUDP(buff, udpAddr[target])
			conn.Close()
		}
	case "TCP":
		if !logonly {
			for i := 0; i < TCPMaxRetries; i++ {
				conn, err := net.DialTimeout("tcp", target, TCPtimeout)
				if err != nil {
					doff := boff.Duration()
					log.Warn().
						Msgf("TCP error for %s - %s [Reconnecting in %s, retries left %d/%d]",
							target, err, doff, TCPMaxRetries-i, TCPMaxRetries)
					time.Sleep(doff)
					continue
				}
				conn.Write(buff)
				boff.Reset()
				conn.Close()
				break
			}
		}
	case "TEST":
		log.Debug().
			Msgf("Debug: Would have sent packet of %d bytes to %s", len(buff), target)
	default:
		log.Fatal().
			Msgf("Illegal send protocol %s", sendproto)
		//log.Fatalf("Illegal send protocol %s", sendproto)
	}
}

// buildPacketMap() is a helper function to initialize a map that represents
// a UDP packet currently being built for each destination we proxy to.  As
// Go forbids taking the address of an object in a map or array so the
// bytes.Buffer object must be stored in the map as a pointer rather than
// a direct object in order to call the pointer methods on it.
func buildPacketMap() map[string]*bytes.Buffer {
	members := hashRing.Nodes()
	hash := make(map[string]*bytes.Buffer, len(members))

	for _, n := range members {
		hash[n.Server] = new(bytes.Buffer)
	}

	return hash
}

// handleBuff() sorts through a full buffer of metrics and batches metrics
// to remote statsd daemons using a consistent hash.
func handleBuff(buff []byte) {
	handleStart := time.Now()
	packets := buildPacketMap()
	mirrorPackets := make(map[string]*bytes.Buffer)
	if mirror != "" {
		mirrorPackets[mirror] = new(bytes.Buffer)
	}
	sep := []byte("\n")
	numMetrics := uint32(0)
	numMetricsDropped := uint32(0)
	mirrorNumMetrics := uint32(0)
	statsMetric := prefix + ".statsProcessed"
	statsMetricDropped := prefix + ".statsDropped"
	policy := defaultPolicy
	var replacedStruct replaceStruct

	boff := &backoff.Backoff{
		Min:    TCPMinBackoff,
		Max:    TCPMaxBackoff,
		Factor: TCPFactorBackoff,
		Jitter: false,
	}

	for offset := 0; offset < len(buff); {
	loop:
		for offset < len(buff) {
			// Find our next value
			switch buff[offset] {
			case '\n':
				offset++
			case '\r':
				offset++
			case 0:
				offset++
			default:
				break loop
			}
		}

		size := bytes.IndexByte(buff[offset:], '\n')
		if size == -1 {
			// last metric in buffer
			size = len(buff) - offset
		}
		if size == 0 {
			// no more metrics
			break
		}

		// Check to ensure we get a metric, and not an invalid Byte sequence
		metric, err := getMetricName(buff[offset : offset+size])

		if err == nil {

			target := hashRing.GetNode(metric).Server

			// prepare packets for mirroring
			if mirror != "" {
				// check built packet size and send if metric doesn't fit
				if mirrorPackets[mirror].Len()+size > packetLen {
					go sendPacket(mirrorPackets[mirror].Bytes(), mirror, mirrorproto, TCPtimeout, boff, false)
					mirrorPackets[mirror].Reset()
				}
			}
			// check built packet size and send if metric doesn't fit
			if packets[target].Len()+size > packetLen {
				go sendPacket(packets[target].Bytes(), target, sendproto, TCPtimeout, boff, logonly)
				packets[target].Reset()
			}
			// add to packet
			if len(Rules.Rules) != 0 {
				go func() {
					replacedStruct = metricMatchReplace(string(buff[offset:offset+size]), &Rules, policy)
				}()
				//buffNewstr := fmt.Sprintf("%s", replacedStruct.Replaced)
				if replacedStruct.countMatch > 0 {
					if replacedStruct.lastPolicy == "pass" {
						log.Info().
							Str("metric", replacedStruct.Replaced).
							Str("target", target).
							Msg("sending")
					} else if replacedStruct.lastPolicy == "drop" {
						log.Info().
							Str("metric", replacedStruct.Replaced).
							Msgf("dropping")
						numMetricsDropped++
					}
				} else {
					// don't replace metric if there's no rule match
					if replacedStruct.lastPolicy == "pass" {
						log.Info().
							Str("metric", replacedStruct.Replaced).
							Str("target", target).
							Msg("sending")
					} else if replacedStruct.lastPolicy == "drop" {
						log.Info().
							Str("metric", replacedStruct.Replaced).
							Msgf("dropping")
						numMetricsDropped++
					}
				}
				if replacedStruct.lastPolicy == "pass" {
					packets[target].Write([]byte(replacedStruct.Replaced))
					packets[target].Write(sep)
				} else if replacedStruct.lastPolicy == "drop" {
					numMetricsDropped++
				}
				// send unchanged metric
			} else {
				if policy == "drop" {
					log.Debug().
						Str("metric", metric).
						Msgf("dropping")
					numMetricsDropped++
				} else if policy == "pass" {
					log.Info().
						Str("metric", metric).
						Str("target", target).
						Msg("sending")
					packets[target].Write(buff[offset : offset+size])
					packets[target].Write(sep)
				}
			}

			if mirror != "" {
				log.Debug().
					Str("metric", string(buff[offset:offset+size])).
					Str("target", target).
					Msgf("mirror sending")
				mirrorPackets[mirror].Write(buff[offset : offset+size])
				mirrorPackets[mirror].Write(sep)
				mirrorNumMetrics++
			}
			numMetrics++
			offset = offset + size + 1
		}
	}

	// Handle reporting our own stats
	stats := fmt.Sprintf("%s:%d|c\n", statsMetric, numMetrics-numMetricsDropped)
	statsdropped := fmt.Sprintf("%s:%d|c\n", statsMetricDropped, numMetricsDropped)
	target := hashRing.GetNode(statsMetric).Server
	// make stats independent from main buffer to fix sliced metrics
	sendPacket([]byte(stats+statsdropped), target, sendproto, TCPtimeout, boff, logonly)

	if mirror != "" {
		stats := fmt.Sprintf("%s:%d|c\n", statsMetric, mirrorNumMetrics)
		sendPacket([]byte(stats), mirror, mirrorproto, TCPtimeout, boff, false)
	}

	if numMetrics == 0 {
		// if we haven't handled any metrics, then don't update counters/stats
		// or send packets
		return
	}

	// Update internal counter
	atomic.AddUint32(&totalMetrics, numMetrics)

	// Empty out any remaining data
	if mirror != "" {
		if mirrorPackets[mirror].Len() > 0 {
			sendPacket(mirrorPackets[mirror].Bytes(), mirror, mirrorproto, TCPtimeout, boff, false)
		}
	}
	for _, target := range hashRing.Nodes() {
		if packets[target.Server].Len() > 0 {
			sendPacket(packets[target.Server].Bytes(), target.Server, sendproto, TCPtimeout, boff, logonly)
			packets[target.Server].Reset()
		}
	}
	handleElapsed := time.Since(handleStart)

	//counter = ratecounter.NewRateCounter(1 * time.Second)

	if time.Now().Unix()-epochTime > 0 {
		rate := int64(totalMetrics) / (time.Now().Unix() - epochTime)
		log.Warn().
			Uint32("processed", numMetrics-numMetricsDropped).
			Dur("processing-time", handleElapsed).
			Uint32("dropped", numMetricsDropped).
			Uint32("processed-total", totalMetrics).
			Int64("rate", rate).
			//Int32("rate", int32(counter)).
			Msg("Processing stats")
		//Msgf("Processed %d metrics in %s. Dropped %d metrics. Running total: %d. Metrics/sec: %d",
		//	numMetrics-numMetricsDropped, handleElapsed, numMetricsDropped, totalMetrics,
		//	int64(totalMetrics)/(time.Now().Unix()-epochTime))
	}
}

// readUDP() a goroutine that just reads data off of a UDP socket and fills
// buffers.  Once a buffer is full, it passes it to handleBuff().
//func readUDP(ip string, port int, handler func([]byte)) {
func readUDP(ip string, port int, c chan []byte) {
	var offset int
	var timeout bool
	var addr = net.UDPAddr{
		Port: port,
		IP:   net.ParseIP(ip),
	}

	log.Warn().
		Msgf("Setting up log to %s level", logLevel)

	log.Warn().
		Msgf("Starting version %s", VERSION)
	log.Warn().
		Msgf("Listening on %s:%d", ip, port)
	sock, err := net.ListenUDP("udp", &addr)
	if err != nil {
		log.Fatal().
			Err(err).
			Msgf("Error opening UDP socket.")
		//log.Fatalln(err)
	}
	defer sock.Close()

	log.Warn().
		Msgf("Setting socket read buffer size to: %d", bufferMaxSize)

	err = sock.SetReadBuffer(bufferMaxSize)
	if err != nil {
		err = sock.SetDeadline(time.Now().Add(time.Second))
		log.Error().
			Err(err).
			Msg("Unable to set read buffer size on socket.  Non-fatal.")
	}

	if sendproto == "TCP" {
		log.Warn().
			Msgf("TCP send timeout set to %s", TCPtimeout)
		log.Warn().
			Msgf("TCP Backoff set Min: %s Max: %s Factor: %f Retries: %d", TCPMinBackoff, TCPMaxBackoff, TCPFactorBackoff, TCPMaxRetries)
	}

	if logonly {
		log.Warn().
			Msgf("Log Only for rules Eanbled")
	}

	log.Warn().
		Msgf("Rock and Roll!")

	buff := make([]byte, BUFFERSIZE)
	for {
		sock.SetReadDeadline(time.Now().Add(time.Second))
		i, err := sock.Read(buff[offset : BUFFERSIZE-1])
		if err == nil {
			buff[offset+i] = '\n'
			offset = offset + i + 1
		} else if err.(net.Error).Timeout() {
			timeout = true
		} else {
			log.Error().
				Err(err).
				Msgf("Read Error")
			continue
		}

		if offset > BUFFERSIZE-4096 || timeout {
			// Approaching make buff size
			// we use a 4KiB margin
			//handler(buff[:offset])
			c <- buff[:offset]
			offset = 0
			timeout = false
		}
	}
}

// runServer() runs and manages this daemon, deals with OS signals, and handles
// communication channels.
func runServer(host string, port int) {
	var c = make(chan []byte, BUFFERSIZE)
	// Set up channel on which to send signal notifications.
	// We must use a buffered channel or risk missing the signal
	// if we're not ready to receive when the signal is sent.
	var sig = make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt, os.Kill, syscall.SIGTERM)

	// read incoming UDP packets
	//readUDP(host, port, handleBuff)
	go readUDP(host, port, c)

	for {
		select {
		case buff := <-c:
			//fmt.Print("Handling %d length buffer...\n", len(buff))
			handleBuff(buff)
		case <-sig:
			log.Warn().
				Msg("Signal received.  Shutting down...")
			log.Warn().
				Msgf("Received %d metrics.\n", totalMetrics)
			return
		}
	}
}

// validateHost() checks if given HOST:PORT:INSTANCE address is in proper format
func validateHost(address string) (*net.UDPAddr, error) {
	var addr *net.UDPAddr
	var err error
	host := strings.Split(address, ":")

	switch len(host) {
	case 1:
		log.Error().
			Msgf("Invalid statsd location: %s", address)
		log.Fatal().
			Msgf("Must be of the form HOST:PORT or HOST:PORT:INSTANCE")
		//log.Fatal("Must be of the form HOST:PORT or HOST:PORT:INSTANCE\n")
	case 2:
		addr, err = net.ResolveUDPAddr("udp", address)
		if err != nil {
			log.Error().
				Msgf("Error parsing HOST:PORT \"%s\"", address)
			log.Fatal().
				Msgf("%s", err.Error())
			//log.Fatal("%s\n", err.Error())
		}
	case 3:
		addr, err = net.ResolveUDPAddr("udp", host[0]+":"+host[1])
		if err != nil {
			log.Error().
				Msgf("Error parsing HOST:PORT:INSTANCE \"%s\"", address)
			log.Fatal().
				Msgf("%s", err.Error())
			//log.Fatalf("%s\n", err.Error())
		}
	default:
		log.Fatal().
			Msgf("Unrecongnized host specification: %s", address)
		//log.Fatalf("Unrecongnized host specification: %s\n", address)
	}
	return addr, err
}

// validatePolicy() checks if default policy has proper value
func validatePolicy(policy string) {
	validate := validator.New()
	err := validate.Var(policy, "eq=pass|eq=drop")
	if err != nil {
		log.Fatal().
			Msgf("Policy must equal \"pass\" or \"drop\"")
		//log.Fatal("Policy must equal \"pass\" or \"drop\"")
	}
}

// validateRules() checks every field in rules definition for its validity
func validateRules(rulesFile string, rulesDir string, exitOnErrors bool) map[string][]string {
	var rulesValidator rulesDef
	// keep slice of errors for each rule
	rulesErrors := make(map[string][]string)

	validate = validator.New()

	rules := viper.New()
	rules.SetConfigName(strings.Split(rulesFile, ".")[0])
	rules.AddConfigPath(rulesDir)
	rules.SetConfigType("yaml")

	err := rules.ReadInConfig()
	if err != nil {
		rulesErrors["config_parsing"] = []string{err.Error()}
		log.Error().
			Err(err).
			Msgf("Fatal error wile reading rules config")
	}

	err = rules.Unmarshal(&rulesValidator)
	if err != nil {
		rulesErrors["config_unmarshall"] = []string{err.Error()}
		log.Error().
			Err(err).
			Msgf("Fatal error while loading rules")
	}

	for _, r := range rulesValidator.Rules {
		err := validate.Struct(r)
		if err != nil {
			if _, ok := err.(*validator.InvalidValidationError); ok {
				log.Error().
					Err(err)
			}
			var errorArr []string
			for _, err := range err.(validator.ValidationErrors) {
				// field - which field is wrong configured
				// validation - validation rule
				// value - current value
				errorMsg := fmt.Sprintf("field=%s validation=%s value=%s",
					err.Namespace(), err.Tag(), err.Value())
				errorArr = append(errorArr, errorMsg)
			}
			rulesErrors[r.Name] = errorArr
		}
	}
	// log misconfigured rules
	if len(rulesErrors) > 0 {
		log.Error().
			Msg("Rules config has errors. Fix below rule definitions:")
		for ruleName, errors := range rulesErrors {
			log.Warn().
				Msgf("\tRule: %s", ruleName)
			for _, err := range errors {
				log.Error().
					Msgf("\t\t %s", err)
			}
		}
		if exitOnErrors {
			os.Exit(len(rulesErrors))
		}
	}
	return rulesErrors
}

func main() {
	var bindAddress string
	var port int

	flag.IntVar(&port, "port", 9125, "Port to listen on")
	flag.IntVar(&port, "p", 9125, "Port to listen on")

	flag.StringVar(&bindAddress, "bind", "0.0.0.0", "IP Address to listen on")
	flag.StringVar(&bindAddress, "b", "0.0.0.0", "IP Address to listen on")

	flag.StringVar(&mirror, "mirror", "", "Address to mirror (forward) raw stats  (HOST:PORT format)")
	flag.StringVar(&mirror, "m", "", "Address to mirror (forward) raw stats (HOST:PORT format)")

	flag.StringVar(&mirrorproto, "mirrorproto", "UDP", "IP Protocol for forwarding original data to local statsd: TCP, UDP, or TEST")

	flag.StringVar(&prefix, "prefix", "statsrelay", "The prefix to use with self generated stats")

	flag.IntVar(&maxprocs, "maxprocs", 0, "Set GOMAXPROCS in runtime. If not defined then Golang defaults.")

	flag.StringVar(&logLevel, "loglevel", "info", "Available options: debug, info, warn, error, fatal, panic and quiet for quiet mode")

	flag.BoolVar(&logonly, "log-only", false, "Log-only mode: doesn't send metrics, just logs the output")
	flag.BoolVar(&logonly, "l", false, "Log-only mode: doesn't send metrics, just logs the output")

	flag.StringVar(&sendproto, "sendproto", "UDP", "IP Protocol for sending data: TCP, UDP, or TEST")
	flag.IntVar(&packetLen, "packetlen", 1400, "Max packet length. Must be lower than MTU plus IPv4 and UDP headers to avoid fragmentation.")

	flag.DurationVar(&TCPtimeout, "tcptimeout", 1*time.Second, "Timeout for TCP client remote connections")
	flag.DurationVar(&TCPtimeout, "t", 1*time.Second, "Timeout for TCP client remote connections")

	flag.BoolVar(&profiling, "pprof", false, "Enable HTTP endpoint for pprof")
	flag.StringVar(&profilingBind, "pprof-bind", ":6060", "Bind for pprof HTTP endpoint")

	flag.IntVar(&TCPMaxRetries, "backoff-retries", 3, "Maximum number of retries in backoff for TCP dial when sendproto set to TCP")
	flag.DurationVar(&TCPMinBackoff, "backoff-min", 50*time.Millisecond, "Backoff minimal (integer) time in Millisecond")
	flag.DurationVar(&TCPMaxBackoff, "backoff-max", 1000*time.Millisecond, "Backoff maximal (integer) time in Millisecond")
	flag.Float64Var(&TCPFactorBackoff, "backoff-factor", 1.5, "Backoff factor (float)")

	flag.StringVar(&rulesConfig, "rules", "", "Config file for statsrelay with matching rules for metrics")
	flag.StringVar(&rulesConfig, "r", "", "Config file for statsrelay with matching rules for metrics")

	flag.BoolVar(&rulesValidationTest, "validate-rules", false, "Validates rules configuration and exits")

	flag.BoolVar(&watchRulesConfig, "watch-rules", false, "Watches for rules config changes and updates runtime values")

	flag.StringVar(&defaultPolicy, "default-policy", "drop", "Default rules policy. Options: drop|pass")
	flag.StringVar(&defaultPolicy, "d", "drop", "Default rules policy. Options: drop|pass")

	flag.BoolVar(&isConsole, "consoleout", false, "Statsrelay console out without JSON production formatting")

	flag.BoolVar(&version, "version", false, "Statsrelay version")

	defaultBufferSize, err := getSockBufferMaxSize()
	if err != nil {
		defaultBufferSize = 32 * 1024
	}

	flag.IntVar(&bufferMaxSize, "bufsize", defaultBufferSize, "Read buffer size")

	flag.Parse()

	if version {
		fmt.Print("%s\n", VERSION)
		os.Exit(0)
	}

	switch logLevel {
	case "debug":
		zerolog.SetGlobalLevel(zerolog.DebugLevel)
	case "info":
		zerolog.SetGlobalLevel(zerolog.InfoLevel)
	case "warn":
		zerolog.SetGlobalLevel(zerolog.WarnLevel)
	case "error":
		zerolog.SetGlobalLevel(zerolog.ErrorLevel)
	case "fatal":
		zerolog.SetGlobalLevel(zerolog.FatalLevel)
	case "panic":
		zerolog.SetGlobalLevel(zerolog.PanicLevel)
	case "quiet":
		zerolog.SetGlobalLevel(zerolog.NoLevel)
	default:
		zerolog.SetGlobalLevel(zerolog.InfoLevel)
	}
	zerolog.DurationFieldUnit = time.Second
	zerolog.DurationFieldInteger = false

	//if isConsole {
	//	log := zerolog.New(os.Stdout).Output(zerolog.ConsoleWriter{Out: os.Stdout})
	//	//log.Logger = log.Output(zerolog.ConsoleWriter{Out: os.Stdout})
	//}

	// viper config rules loading
	if rulesConfig != "" {
		validatePolicy(defaultPolicy)

		// get the config name
		rulesFile := filepath.Base(rulesConfig)
		// get the path
		rulesDir := filepath.Dir(rulesConfig)

		// validate and exit in case of errors
		if len(validateRules(rulesFile, rulesDir, true)) != 0 {
			os.Exit(1)
		}
		if rulesValidationTest {
			log.Warn().
				Msgf("All rules in %s are correct.", rulesConfig)
			os.Exit(0)
		}

		log.Warn().
			Msgf("Setting rules config file: %s", rulesConfig)
		viper.SetConfigType("yaml")
		viper.SetConfigName(strings.Split(rulesFile, ".")[0])
		viper.AddConfigPath(rulesDir)

		err = viper.ReadInConfig()
		if err != nil {
			log.Fatal().
				Msgf("Error reading rules file: %s", err)
			//log.Fatalf("Error reading rules file: %s \n", err)
		}
		if err := viper.Unmarshal(&Rules); err != nil {
			log.Fatal().
				Msgf("Fatal error loading rules: %s", err)
			//log.Fatalf("Fatal error loading rules: %s \n", err)
		}
		//if logLevel == "DebugLevel" {
		//	pretty.Print(Rules)
		//}

		// config watch and live reload
		if watchRulesConfig {
			viper.WatchConfig()
			viper.OnConfigChange(func(e fsnotify.Event) {
				log.Info().
					Msgf("Config file changed:", e.Name)
				// reread config if no errors, use old config otherwise
				if len(validateRules(rulesFile, rulesDir, false)) == 0 {
					// create temporary variable for assigning its value to main Rules
					// needed in case when unmarshal fails and we don't want to sacrifice
					// our current rules
					tmpRules := rulesDef{}
					err := viper.Unmarshal(&tmpRules)
					if err != nil {
						log.Fatal().
							Err(err).
							Msgf("Fatal error loading rules")
						//log.Fatalf("Fatal error loading rules: %s \n", err)
					}
					Rules = tmpRules
					//if logLevel == "DebugLevel" {
					//	pretty.Print(Rules)
					//}
				} else {
					log.Info().
						Msgf("Using old rules config. Fix above errors to apply new config.")
				}
			})
		}
	}

	if len(flag.Args()) == 0 {
		log.Fatal().
			Msgf("One or more host specifications are needed to locate statsd daemons.")
		//log.Fatalf("One or more host specifications are needed to locate statsd daemons.\n")
	}

	if maxprocs != 0 {
		log.Info().
			Msgf("Using GOMAXPROCS %d", maxprocs)
		runtime.GOMAXPROCS(maxprocs)
	}

	if profiling {
		// profiling web server
		go func() {
			log.Print(http.ListenAndServe(profilingBind, nil))
		}()

		// /debug/vars endpoint on profiling web server
		expvar.Publish("stats", influxdb.Metrics("statsrelay_internals"))
		//              expvar.Publish("ProcessedPerSecond", counter)
		//		expvar.Publish("Processed", numMetrics-numMetricsDropped)
		//		expvar.Publish("Dropped", numMetricsDropped)
		//		expvar.Publlish("ProcessedTotal", totalMetrics)
		//		expvar.Publlish("ProcessingTime", handleElapsed)

		if err != nil {
			log.Fatal().
				Msgf("Unable to set /debug/vars metrics internals endpoint on %s with error: %q", profilingBind, err)
			//log.Fatalf("Unable to set /debug/vars metrics internals endpoint on %s with error: %q", profilingBind, err)
		}
	}

	// HOST:PORT:INSTANCE validation
	if mirror != "" {
		addr, _ := validateHost(mirror)
		if addr != nil {
			udpAddr[mirror] = addr
		}
		log.Warn().
			Msgf("Setting up mirroring to %s", mirror)
	}
	for _, v := range flag.Args() {
		addr, _ := validateHost(v)
		if addr != nil {
			udpAddr[v] = addr
			hashRing.AddNode(Node{v, ""})
		}
	}

	epochTime = time.Now().Unix()
	runServer(bindAddress, port)

	log.Warn().
		Msgf("Normal shutdown.")
}
