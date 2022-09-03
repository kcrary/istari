
include ../Makefile.inc

.PHONY : rules generated clean

rules : generated
	$(SMLNJ) compile-rules.sml

generated : lexmain.cmlex.sml parsemain.cmyacc.sml

%.cmlex.sml : %.cmlex
	cmlex $<

%.cmyacc.sml : %.cmyacc
	cmyacc $<

clean :
	rm -r .cm
	rm *.cmyacc.sml
	rm *.cmlex.sml
