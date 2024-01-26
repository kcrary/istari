
include ../Makefile.inc

all : batch-nolib server-nolib batch server

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

.PHONY : install
install :
	cp bin/istari bin/istari-nolib $(INSTALLDIR)

clean :
	rm -rf .cm

veryclean : clean
	rm *.cmlex.sml
