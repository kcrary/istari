
IPP=../ipp/bin/ipp

.PHONY : sml ocaml ocaml-generated clean

trusted/the-rules.iml : trusted/RULES
	cd ../rulegen; make rules

smlnj : trusted/the-rules.iml
	$(IPP) -t sml -build -B ../ipp/basis prover.proj

ocaml-generated prover.make :
	$(IPP) -t ocaml -build -B ../ipp/basis prover.proj

ocaml : ocaml-generated prover.make
	make -f Makefile.ocaml ocaml

clean :
	rm -f *.iml.sml *.iml-ml *.sml.sml *.sml-ml *.cmi *.cmo *.cma *.ipds *.ipdo prover.cm prover.make
	rm -rf .cm
