
IPP=../ipp/bin/ipp

.PHONY : sml ocaml ocaml-generated clean

smlnj :
	$(IPP) -t sml -build -B ../ipp/basis prover.proj

ocaml-generated prover.make :
	$(IPP) -t ocaml -build -B ../ipp/basis prover.proj

ocaml : ocaml-generated prover.make
	make -f Makefile.ocaml ocaml

clean :
	rm -f *.iml.sml *.iml-ml *.sml.sml *.sml-ml *.cmi *.cmo *.cma *.ipds *.ipdo prover.cm prover.make
	rm -rf .cm
