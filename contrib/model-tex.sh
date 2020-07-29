#!/bin/bash
set -ex
#docker pull akanner/centos7:tla-bin_tex
docker run -it --rm -v `git rev-parse --show-toplevel`:/ipes-model akanner/centos7:tla-bin_tex /bin/bash -c \
	"cd /ipes-model && for tla_file in \`ls ./*.tla\`; do tlatex -latexCommand pdflatex \$tla_file; done; rm -rf ./*.{log,dvi,aux}"
