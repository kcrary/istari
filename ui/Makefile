
include ../Makefile.inc

all : batch-nolib server-nolib istaritags batch server

.PHONY : generated
generated : lexrepl-nj.cmlex.sml

%.cmlex.sml : %.cmlex
	cmlex $<

.PHONY : smlnj

server : generated
	cd ../prover; make smlnj
	echo "export true;" | $(SMLNJ) export-server.sml

server-nolib : generated
	cd ../prover; make smlnj
	echo "export false;" | $(SMLNJ) export-server.sml

batch : generated
	cd ../prover; make smlnj
	echo "export true;" | $(SMLNJ) export-batch.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin istari-heapimg istari

batch-nolib : generated
	cd ../prover; make smlnj
	echo "export false;" | $(SMLNJ) export-batch.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin istari-nolib-heapimg istari-nolib

procdoc :
	cd ../prover; make smlnj
	echo "export ();" | $(SMLNJ) export-procdoc.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin procdoc-heapimg procdoc

istaritags :
	$(SMLNJ) export-tags.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin istaritags-heapimg istaritags

.PHONY : install
install :
	cp bin/istari bin/istari-nolib bin/istaritags $(INSTALLDIR)

clean :
	rm -rf .cm

veryclean : clean
	rm *.cmlex.sml
