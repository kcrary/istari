
include ../Makefile.inc

all : batch-nolib server-nolib istaritags batch server

.PHONY : generated
generated : lexrepl-nj.cmlex.sml

%.cmlex.sml : %.cmlex
	cmlex $<

.PHONY : smlnj

server : generated
	cd ../prover; make smlnj
	echo "exportServer \"../library/prelude.iml\" \"Libraries loaded.\\n\" \"bin/istarisrv-heapimg\";" | $(SMLNJ) export.sml

server-nolib : generated
	cd ../prover; make smlnj
	echo "exportServer \"empty.iml\" \"\" \"bin/istarisrv-nolib-heapimg\";" | $(SMLNJ) export.sml

batch : generated
	cd ../prover; make smlnj
	echo "exportBatch \"../library/prelude.iml\" \"Libraries loaded.\\n\" \"bin/istari-heapimg\";" | $(SMLNJ) export.sml

batch-nolib : generated
	cd ../prover; make smlnj
	echo "exportBatch \"empty.iml\" \"\" \"bin/istari-nolib-heapimg\";" | $(SMLNJ) export.sml

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
