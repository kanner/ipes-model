#!/bin/bash
set -ex
#docker pull akanner/centos7:tla-bin_tex
docker run -it --rm -v `git rev-parse --show-toplevel`:/ipes-model akanner/centos7:tla-bin_tex /bin/bash -c \
	"cd /ipes-model && time tlc -workers 6 -coverage 25 -dfid 6 ipes.tla > ipes-model-check.log 2>&1"
