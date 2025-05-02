
.PHONY : testbasis
testbasis :
	ipp -t ocaml -I ../basis testbasis.iml
	ocamlc -c -error-style short -I ../basis -impl testbasis.iml-ml
	ocamlc ../basis/basis.cma testbasis.cmo
