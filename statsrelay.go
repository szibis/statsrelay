package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/http"
	_ "net/http/pprof"
	"os"
	"os/signal"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/jpillora/backoff"
	"github.com/kr/pretty"
	"github.com/spf13/viper"
)

const VERSION string = "0.0.7"

// BUFFERSIZE controls the size of the [...]byte array used to read UDP data
// off the wire and into local memory.  Metrics are separated by \n
// characters.  This buffer is passed to a handler to proxy out the metrics
// to the real statsd daemons.
const BUFFERSIZE int = 1 * 1024 * 1024 // 1MiB

// prefix is the string that will be prefixed onto self generated stats.
// Such as <prefix>.statsProcessed.  Default is "statsrelay"
var prefix string

// metricsPrefix is the string that will be prefixed onto each metric passed
// through statsrelay. This is especialy usefull with docker passing
// env, appname automatic from docker environment to app metri
// Such as <metricsPrefix>.mytest.service.metric.count  Default is empty
var metricsPrefix string

// metricTags is the string that will be used as tags into each metric passed
// through statsrelay.
// This is especialy usefull with datadog statsd metrics passing.
// Such as my.prefix.myinc:1|c|@1.000000|#baz,foo:bar
// Default is empty
var metricTags string

// udpAddr is a mapping of HOST:PORT:INSTANCE to a UDPAddr object
var udpAddr = make(map[string]*net.UDPAddr)

// tcpAddr is a mapping of HOST:PORT:INSTANCE to a TCPAddr object
var tcpAddr = make(map[string]*net.TCPAddr)

// mirror is a HOST:PORT address for mirroring raw statsd metrics
var mirror string

// hashRing is our consistent hashing ring.
var hashRing = NewJumpHashRing(1)

// totalMetrics tracks the totall number of metrics processed
var totalMetrics int = 0

// totalMetricsLock is a mutex gaurding totalMetrics
var totalMetricsLock sync.Mutex

// Time we began
var epochTime int64

// Verbose/Debug output
var verbose bool

// IP protocol set for sending data target
var sendproto string

// packetLen is the size in bytes of data we stuff into one packet before
// sending it to statsd. This must be lower than the MTU, IPv4 header size
// and UDP header size to avoid fragmentation and data loss.
var packetLen int

// Maximum size of buffer
var bufferMaxSize int

// Timeout value for remote TCP connection
var TCPtimeout time.Duration

// profiling bool value to enable disable http endpoint for profiling
var profiling bool

// profilingBind string value for pprof http host:port data
var profilingBind string

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

// rulesConfig string value for config file name with match rules
var rulesConfig string

type rulesDef struct {
	Rules []struct {
		Name    string   `yaml:name`
		Match   string   `yaml:"match"`
		Replace string   `yaml:"replace"`
		Tags    []string `yaml:"tags"`
	} `yaml:"rules"`
}

// Rules to rules Def
var Rules rulesDef

//var replaced string

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
		log.Printf("Could not parse /proc/sys/net/core/rmem_max\n")
		return -1, err
	}

	return i, nil
}

// matchMetric() match metric based on regexp definition match
func metricMatchReplace(metric []byte, rules *rulesDef) ([]byte, int) {
	var replaced string
	var match []string
	var tagMetric string
	var matched int
	for _, r := range rules.Rules {
		re := regexp.MustCompile(r.Match)
		if replaced == "" {
			match = re.FindAllString(string(metric), -1)
			if match != nil {
				matched++
			}
			if r.Tags != nil {
				tagMetric = genTags(metric, r.Tags, r.Replace)
			}
			if tagMetric != "" {
				replaced = re.ReplaceAllString(string(metric), tagMetric)
			} else {
				replaced = re.ReplaceAllString(string(metric), r.Replace)
			}
		} else {
			match = re.FindAllString(replaced, -1)
			if match != nil {
				matched++
			}
			if r.Tags != nil {
				tagMetric = genTags([]byte(replaced), r.Tags, r.Replace)
			}
			if tagMetric != "" {
				replaced = re.ReplaceAllString(replaced, tagMetric)
			} else {
				replaced = re.ReplaceAllString(replaced, r.Replace)
			}
		}
		if verbose && match != nil && matched != 0 {
			log.Printf("Replacing Match: %s Rule: %s, Replaced: %s", r.Match, r.Replace, replaced)
		}
	}
	return []byte(replaced), matched

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

//func splitTags(tags string) []string {
//	tag := strings.Split(tags, ",")
//	return tag
//}

// genTags() add metric []byte and metricTags string, return string
// of metrics with additional tags
func genTags(metric []byte, metricTags []string, metricReplace string) string {
	// statsd metrics are of the form:
	// KEY:VALUE|TYPE|RATE or KEY:VALUE|TYPE|RATE|#tags
	// This function add or extend #tags in metric
	tagsTmp := strings.Join(metricTags, ",")
	if strings.Contains((string(metric)), "|#") {
		return fmt.Sprintf("%s,%s", metricReplace, tagsTmp)
	}
	if tagsTmp != "" {
		return fmt.Sprintf("%s|#%s", metricReplace, tagsTmp)
	}
	return metricReplace
}

// sendPacket takes a []byte and writes that directly to a UDP socket
// that was assigned for target.
func sendPacket(buff []byte, target string, sendproto string, TCPtimeout time.Duration, boff *backoff.Backoff) {
	switch sendproto {
	case "UDP":
		conn, err := net.ListenUDP("udp", nil)
		if err != nil {
			log.Panicln(err)
		}
		conn.WriteToUDP(buff, udpAddr[target])
		conn.Close()
	case "TCP":
		for i := 0; i < TCPMaxRetries; i++ {
			conn, err := net.DialTimeout("tcp", target, TCPtimeout)
			if err != nil {
				doff := boff.Duration()
				log.Printf("TCP error for %s - %s [Reconnecting in %s, retries left %d/%d]\n",
					target, err, doff, TCPMaxRetries-i, TCPMaxRetries)
				time.Sleep(doff)
				continue
			}
			conn.Write(buff)
			boff.Reset()
			defer conn.Close()
			break
		}
	case "TEST":
		if verbose {
			log.Printf("Debug: Would have sent packet of %d bytes to %s",
				len(buff), target)
		}
	default:
		log.Fatalf("Illegal send protocol %s", sendproto)
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
	packets := buildPacketMap()
	mirrorPackets := make(map[string]*bytes.Buffer)
	if mirror != "" {
		mirrorPackets[mirror] = new(bytes.Buffer)
	}
	sep := []byte("\n")
	numMetrics := 0
	numMetricsDropped := 0
	statsMetric := prefix + ".statsProcessed"
	statsMetricDropped := prefix + ".statsDropped"

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
					go sendPacket(mirrorPackets[mirror].Bytes(), mirror, sendproto, TCPtimeout, boff)
					mirrorPackets[mirror].Reset()
				}
			}
			// check built packet size and send if metric doesn't fit
			if packets[target].Len()+size > packetLen {
				go sendPacket(packets[target].Bytes(), target, sendproto, TCPtimeout, boff)
				packets[target].Reset()
			}
			// add to packet
			var countMatchDropped int = 0 // check this is weird
			if len(Rules.Rules) != 0 {
				countMatchDropped := 0
				buffNew, matched := metricMatchReplace(buff[offset:offset+size], &Rules)
				//log.Printf("matched %s, buffnew %q", matched, buffNew)
				if matched > 0 {
					packets[target].Write(buffNew)
					countMatchDropped := 0
					if verbose && countMatchDropped == 0 {
						log.Printf("Sending %s to %s", buffNew, target)
					}
				}
				if matched == 0 {
					countMatchDropped++
				}
				if verbose && countMatchDropped != 0 {
					log.Printf("No match for %s - skipping", string(metric))
					numMetricsDropped++
				}
			} else {
				if verbose {
					log.Printf("Sending %s to %s", metric, target)
				}
				packets[target].Write(buff[offset : offset+size])
			}
			if countMatchDropped == 0 {
				packets[target].Write(sep)
				offset = offset + size + 1
			}
			if mirror != "" {
				mirrorPackets[mirror].Write(buff[offset : offset+size])
				mirrorPackets[mirror].Write(sep)
			}
			numMetrics++
		}
	}

	if numMetrics == 0 {
		// if we haven't handled any metrics, then don't update counters/stats
		// or send packets
		return
	}

	// Update internal counter
	totalMetricsLock.Lock()
	totalMetrics = totalMetrics + numMetrics
	totalMetricsLock.Unlock()

	// Handle reporting our own stats
	stats := fmt.Sprintf("%s:%d|c\n", statsMetric, numMetrics-numMetricsDropped)
	statsdropped := fmt.Sprintf("%s:%d|c\n", statsMetricDropped, numMetricsDropped)
	target := hashRing.GetNode(statsMetric).Server
	targetdropped := hashRing.GetNode(statsMetricDropped).Server
	if mirror != "" {
		if mirrorPackets[mirror].Len()+len(stats) > packetLen {
			go sendPacket(mirrorPackets[mirror].Bytes(), mirror, sendproto, TCPtimeout, boff)
			mirrorPackets[mirror].Reset()
		}
	}
	if packets[target].Len()+len(stats) > packetLen {
		sendPacket(packets[target].Bytes(), target, sendproto, TCPtimeout, boff)
		packets[target].Reset()
	}
	if packets[target].Len()+len(statsdropped) > packetLen {
		sendPacket(packets[targetdropped].Bytes(), targetdropped, sendproto, TCPtimeout, boff)
		packets[targetdropped].Reset()
	}
	if mirror != "" {
		mirrorPackets[mirror].Write([]byte(stats))
	}
	packets[target].Write([]byte(stats))
	packets[target].Write([]byte(statsdropped))

	// Empty out any remaining data
	if mirror != "" {
		if mirrorPackets[mirror].Len() > 0 {
			sendPacket(mirrorPackets[mirror].Bytes(), mirror, sendproto, TCPtimeout, boff)
		}
	}
	for _, target := range hashRing.Nodes() {
		if packets[target.Server].Len() > 0 {
			sendPacket(packets[target.Server].Bytes(), target.Server, sendproto, TCPtimeout, boff)
			packets[target.Server].Reset()
		}
	}
	for _, targetdropped := range hashRing.Nodes() {
		if packets[targetdropped.Server].Len() > 0 {
			sendPacket(packets[targetdropped.Server].Bytes(), targetdropped.Server, sendproto, TCPtimeout, boff)
			packets[targetdropped.Server].Reset()
		}
	}

	if verbose && time.Now().Unix()-epochTime > 0 {
		log.Printf("Processed %d metrics. Dropped %d metrics. Running total: %d. Metrics/sec: %d\n",
			numMetrics-numMetricsDropped, numMetricsDropped, totalMetrics,
			int64(totalMetrics)/(time.Now().Unix()-epochTime))
	}
}

// readUDP() a goroutine that just reads data off of a UDP socket and fills
// buffers.  Once a buffer is full, it passes it to handleBuff().
func readUDP(ip string, port int, c chan []byte) {
	var buff *[BUFFERSIZE]byte
	var offset int
	var timeout bool
	var addr = net.UDPAddr{
		Port: port,
		IP:   net.ParseIP(ip),
	}

	log.Printf("Starting version %s", VERSION)
	log.Printf("Listening on %s:%d\n", ip, port)
	sock, err := net.ListenUDP("udp", &addr)
	if err != nil {
		log.Printf("Error opening UDP socket.\n")
		log.Fatalln(err)
	}
	defer sock.Close()

	log.Printf("Setting socket read buffer size to: %d\n", bufferMaxSize)
	err = sock.SetReadBuffer(bufferMaxSize)
	if err != nil {
		log.Printf("Unable to set read buffer size on socket.  Non-fatal.")
		log.Println(err)
	}
	err = sock.SetDeadline(time.Now().Add(time.Second))
	if err != nil {
		log.Printf("Unable to set timeout on socket.\n")
		log.Fatalln(err)
	}

	if sendproto == "TCP" {
		log.Printf("TCP send timeout set to %s", TCPtimeout)
		log.Printf("TCP Backoff set Min: %s Max: %s Factor: %f Retries: %d", TCPMinBackoff, TCPMaxBackoff, TCPFactorBackoff, TCPMaxRetries)
	}

	if len(metricsPrefix) != 0 {
		log.Printf("Metrics prefix set to %s", metricsPrefix)
	}

	if len(metricTags) != 0 {
		log.Printf("Metrics tags set to %s", metricTags)
	}

	if verbose {
		log.Printf("Rock and Roll!\n")
	}

	for {
		if buff == nil {
			buff = new([BUFFERSIZE]byte)
			offset = 0
			timeout = false
		}

		i, err := sock.Read(buff[offset : BUFFERSIZE-1])
		if err == nil {
			buff[offset+i] = '\n'
			offset = offset + i + 1
		} else if err.(net.Error).Timeout() {
			timeout = true
			err = sock.SetDeadline(time.Now().Add(time.Second))
			if err != nil {
				log.Panicln(err)
			}
		} else {
			log.Printf("Read Error: %s\n", err)
			continue
		}

		if offset > BUFFERSIZE-4096 || timeout {
			// Approaching make buff size
			// we use a 4KiB margin
			c <- buff[:offset]
			buff = nil
		}
	}
}

// runServer() runs and manages this daemon, deals with OS signals, and handles
// communication channels.
func runServer(host string, port int) {
	var c chan []byte = make(chan []byte, 256)
	// Set up channel on which to send signal notifications.
	// We must use a buffered channel or risk missing the signal
	// if we're not ready to receive when the signal is sent.
	var sig chan os.Signal = make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt, os.Kill, syscall.SIGTERM)

	// read incoming UDP packets
	go readUDP(host, port, c)

	for {
		select {
		case buff := <-c:
			//fmt.Printf("Handling %d length buffer...\n", len(buff))
			go handleBuff(buff)
		case <-sig:
			log.Printf("Signal received.  Shutting down...\n")
			log.Printf("Received %d metrics.\n", totalMetrics)
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
		log.Printf("Invalid statsd location: %s\n", address)
		log.Fatalf("Must be of the form HOST:PORT or HOST:PORT:INSTANCE\n")
	case 2:
		addr, err = net.ResolveUDPAddr("udp", address)
		if err != nil {
			log.Printf("Error parsing HOST:PORT \"%s\"\n", address)
			log.Fatalf("%s\n", err.Error())
		}
	case 3:
		addr, err = net.ResolveUDPAddr("udp", host[0]+":"+host[1])
		if err != nil {
			log.Printf("Error parsing HOST:PORT:INSTANCE \"%s\"\n", address)
			log.Fatalf("%s\n", err.Error())
		}
	default:
		log.Fatalf("Unrecongnized host specification: %s\n", address)
	}
	return addr, err
}

func main() {
	var bindAddress string
	var port int

	flag.IntVar(&port, "port", 9125, "Port to listen on")
	flag.IntVar(&port, "p", 9125, "Port to listen on")

	flag.StringVar(&bindAddress, "bind", "0.0.0.0", "IP Address to listen on")
	flag.StringVar(&bindAddress, "b", "0.0.0.0", "IP Address to listen on")

	flag.StringVar(&mirror, "mirror", "", "Address to mirror raw stats (HOST:PORT format)")
	flag.StringVar(&mirror, "m", "", "Address to mirror raw stats (HOST:PORT format)")

	flag.StringVar(&prefix, "prefix", "statsrelay", "The prefix to use with self generated stats")
	flag.StringVar(&metricsPrefix, "metrics-prefix", "", "The prefix to use with metrics passed through statsrelay")

	flag.StringVar(&metricTags, "metrics-tags", "", "Comma separated tags for each relayed metric. Example: foo:bar,test,test2:bar")

	flag.IntVar(&maxprocs, "maxprocs", 0, "Set GOMAXPROCS in runtime. If not defined then Golang defaults.")

	flag.BoolVar(&verbose, "verbose", false, "Verbose output")
	flag.BoolVar(&verbose, "v", false, "Verbose output")

	flag.StringVar(&sendproto, "sendproto", "UDP", "IP Protocol for sending data: TCP, UDP, or TEST")
	flag.IntVar(&packetLen, "packetlen", 1400, "Max packet length. Must be lower than MTU plus IPv4 and UDP headers to avoid fragmentation.")

	flag.DurationVar(&TCPtimeout, "tcptimeout", 1*time.Second, "Timeout for TCP client remote connections")
	flag.DurationVar(&TCPtimeout, "t", 1*time.Second, "Timeout for TCP client remote connections")

	flag.BoolVar(&profiling, "pprof", false, "Enable HTTP endpoint for pprof")
	flag.StringVar(&profilingBind, "pprof-bind", ":8080", "Bind for pprof HTTP endpoint")

	flag.IntVar(&TCPMaxRetries, "backoff-retries", 3, "Maximum number of retries in backoff for TCP dial when sendproto set to TCP")
	flag.DurationVar(&TCPMinBackoff, "backoff-min", 50*time.Millisecond, "Backoff minimal (integer) time in Millisecond")
	flag.DurationVar(&TCPMaxBackoff, "backoff-max", 1000*time.Millisecond, "Backoff maximal (integer) time in Millisecond")
	flag.Float64Var(&TCPFactorBackoff, "backoff-factor", 1.5, "Backoff factor (float)")
	flag.StringVar(&rulesConfig, "rules", "statsrelay.yml", "Config file for statsrelay with matching rules for metrics")
	flag.StringVar(&rulesConfig, "r", "statsrelay.yml", "Config file for statsrelay with matching rules for metrics")

	flag.Parse()

	defaultBufferSize, err := getSockBufferMaxSize()
	if err != nil {
		defaultBufferSize = 32 * 1024
	}

	// viper config rules loading
	log.Printf("Setting rules config file: %s \n", rulesConfig)
	viper.SetConfigFile(rulesConfig)
	viper.AddConfigPath(".")
	viper.SetConfigType("yaml")

	err = viper.ReadInConfig()

	if err != nil {
		log.Fatalf("Error reading rules file: %s \n", err)
		//viper.SetDefault("rules", "All (.*) pass")
	}

	if err := viper.Unmarshal(&Rules); err != nil {
		log.Fatalf("Fatal error loading rules: %s \n", err)
		//viper.SetDefault("rules", "All (.*) pass")
	}

	fmt.Printf("%# v\n", pretty.Formatter(Rules))
	// end viper config for rules

	flag.IntVar(&bufferMaxSize, "bufsize", defaultBufferSize, "Read buffer size")

	if len(flag.Args()) == 0 {
		log.Fatalf("One or more host specifications are needed to locate statsd daemons.\n")
	}

	if maxprocs != 0 {
		log.Printf("Using GOMAXPROCS %d", maxprocs)
		runtime.GOMAXPROCS(maxprocs)
	}

	if profiling {
		go func() {
			log.Println(http.ListenAndServe(profilingBind, nil))
		}()
	}

	// HOST:PORT:INSTANCE validation
	if mirror != "" {
		_, _ = validateHost(mirror)
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

	log.Printf("Normal shutdown.\n")

}
