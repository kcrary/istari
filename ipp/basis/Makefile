
include ../../Makefile.inc

## order is significant
SOURCES = order stringbasis word64 wordn word8 word32 word62 basis_sig basis smlbasis_sig smlbasis

INTFS = $(foreach i, $(SOURCES), $(i).cmi)
IMPLS = $(foreach i, $(SOURCES), $(i).cmo)
ZARITH = +zarith

.PHONY : all ocaml smlnj

all : smlnj ocaml

ocaml : $(INTFS) basis.cma

basis.cma : $(IMPLS)
	ocamlc -a -o basis.cma -I $(ZARITH) zarith.cma $(IMPLS)

basis_sig.cmo basis_sig.cmi : basis_sig.ml
	ocamlc -c -I $(ZARITH) $<

smlbasis_sig.cmo smlbasis_sig.cmi : smlbasis_sig.ml
	ocamlc -c -I $(ZARITH) $<

%.cmi : %.mli
	ocamlc -c -I $(ZARITH) $<

%.cmo : %.ml %.cmi
	ocamlc -c -I $(ZARITH) $<

smlnj :
	echo 'CM.make "basis.cm"; (OS.Process.exit OS.Process.success) : unit;' | $(SMLNJ)

clean : 
	rm -f *.cmi *.cmo *.cma
	rm -rf .cm

word64.cmo word64.cmi : order.cmi stringbasis.cmi
wordn.cmi wordn.cmi : order.cmi word64.cmi stringbasis.cmi
word8.cmo word8.cmi : order.cmi wordn.cmi
word32.cmo word32.cmi : order.cmi wordn.cmi
word62.cmo word62.cmi : order.cmi wordn.cmi
basis.cmo basis.cmi : order.cmi word8.cmi word32.cmi word62.cmi word62.cmi basis_sig.cmo
smlbasis.cmo smlbasis.cmi : basis.cmi smlbasis_sig.cmo
