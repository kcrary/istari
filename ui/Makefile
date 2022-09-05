
include ../Makefile.inc

all : server batch server-nolib batch-nolib

.PHONY : generated
generated : lexrepl-nj.cmlex.sml

%.cmlex.sml : %.cmlex
	cmlex $<

.PHONY : smlnj

server : generated
	cd ../prover; make smlnj
	echo "export true;" | sml export-repl.sml

server-nolib : generated
	cd ../prover; make smlnj
	echo "export false;" | sml export-repl.sml

batch : generated
	cd ../prover; make smlnj
	echo "export true;" | sml export-batch.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin istari-heapimg istari

batch-nolib : generated
	cd ../prover; make smlnj
	echo "export false;" | sml export-batch.sml
	../ipp/bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin istari-nolib-heapimg istari-nolib

.PHONY : install
install :
	cp bin/istari bin/istari-nolib $(INSTALLDIR)

clean :
	rm -rf .cm

veryclean : clean
	rm *.cmlex.sml
