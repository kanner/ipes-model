FROM centos:centos7
ADD tla-sty-cyrillic.patch /
RUN yum update -y centos-release ; yum -y upgrade
# requirements
RUN yum install -y git java-11-openjdk-devel zip unzip patch && \
	# tla-bin
	git clone https://github.com/pmer/tla-bin.git && \
	cd tla-bin && \
	./download_or_update_tla.sh && \
	# patch for cyrillic support
	unzip tla2tools.jar && \
	patch -p1 --binary < /tla-sty-cyrillic.patch && \
	zip -r tla2tools.jar ./* && \
	# install and clean
	./install.sh && \
	cd - && rm -rf tla-bin tla-sty-cyrillic.patch && \
	yum clean all
# latex
RUN yum -y install epel-release && \
	yum -y install texlive texlive-latex texlive-collection-latex texlive-collection-latexrecommended texlive-collection-langcyrillic && \
	yum clean all
# cyrillic encoding
RUN localedef -i ru_RU -f UTF-8 ru_RU.UTF-8 && \
	echo "LANG=ru_RU.UTF-8" > /etc/locale.conf
ENV LANG ru_RU.UTF-8
