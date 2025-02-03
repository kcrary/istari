
include ../Makefile.inc

all : smlnj

.PHONY : generated
generated : lexmain.cmlex.sml parsemain.cmyacc.sml the-basis.sml

%.cmlex.sml : %.cmlex
	cmlex $<

%.cmyacc.sml : %.cmyacc
	cmyacc $<

.PHONY : smlnj
smlnj : generated
	$(SMLNJ) export-smlnj.sml
	bin/$(MKNJEXEC) $(SMLNJ) `pwd`/bin ipp-heapimg ipp

the-basis.sml : ../basis/BASIS
	$(SMLNJ) make-basis.sml

.PHONY : install
install :
	cp bin/ipp $(INSTALLDIR)

clean :
	rm -rf .cm

veryclean : clean
	rm -f *.cmyacc.sml
	rm -f *.cmlex.sml
