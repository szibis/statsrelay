package main

import "testing"

// genTags()
func BenchmarkGenTagsWithTag(b *testing.B) {
	for n := 0; n < b.N; n++ {
		b.SetBytes(2)
		b.ReportAllocs()
		genTags([]byte("test.metric.gauge:100|g|#test:foo,test2:bar"), []string{"env:sandbox", "region:us-east-1", "type:cluster"}, "${new_prefix}.metric.gauge:100|g|#test:foo,test2:bar")
	}
}
func BenchmarkGenTagsWithoutTag(b *testing.B) {
	for n := 0; n < b.N; n++ {
		b.SetBytes(2)
		b.ReportAllocs()
		genTags([]byte("prefixtest.metric.gauge:1000|g"), []string{"env:sandbox", "region:us-east-1", "type:cluster"}, "${new_prefix}test.metric.gauge:1000|g")
	}
}

// getMetricName
func BenchmarkGetMetricName(b *testing.B) {
	for n := 0; n < b.N; n++ {
		b.SetBytes(2)
		b.ReportAllocs()
		getMetricName([]byte("test.metric.gauge:100|g"))
	}
}
