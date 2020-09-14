#!/bin/bash
set -ex
#docker pull akanner/centos7:tla-bin_tex
docker run -it --rm -v `git rev-parse --show-toplevel`:/ipes-model \
	-e JAVA_OPTS='-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -d64 -Xmx10g -Xms1g -Xss1g -XX:MaxPermSize=10g' \
	akanner/centos7:tla-bin_tex /bin/bash -c \
	"cd /ipes-model && tlc -workers 6 -dfid 6 ipes.tla > result-dfid6.log 2>&1"
#	"cd /ipes-model && tlc -workers 6 -dfid 7 ipes.tla > result-dfid7.log 2>&1"
#	"cd /ipes-model && tlc -workers 6 -coverage 25 -dfid 6 ipes.tla > ipes-model-check.log 2>&1"
