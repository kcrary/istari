
include ../Makefile.inc

IPP=../ipp/bin/ipp

.PHONY : all smlnj ocaml ocaml-generated clean

all : smlnj ocaml

smlnj :
	$(IPP) -t sml -build -B ../basis cmlib.proj
	echo 'val _ = CM.make "cmlib.cm"; val _ = OS.Process.exit OS.Process.success;' | $(SMLNJ)

ocaml-generated cmlib.make :
	$(IPP) -t ocaml -build -B ../basis cmlib.proj

ocaml : ocaml-generated cmlib.make
	make -f Makefile.ocaml ocaml

clean :
	rm -f *.iml.sml *.iml-ml *.sml.sml *.sml-ml *.cmi *.cmo *.ipds *.ipdo cmlib.cm cmlib.make cmlib.cma
	rm -rf .cm
	rm -rf ../cmlib/.cm
