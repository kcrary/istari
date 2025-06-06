
.PHONY: all
all: smlnj


.PHONY : smlnj
smlnj :
	cd basis; make smlnj
	cd ipp; make smlnj
	cd cmlibi; make smlnj
	cd ui; mkdir -p bin; make batch-nolib
	cd core; make
	cd ui; make server batch server-nolib istaritags
	cd library; make

.PHONY : install
install :
	cd ipp; make install
	cd ui; make install

## Note: there is no UI for the OCaml version yet.
.PHONY : ocaml
ocaml :
	cd ipp/basis; make ocaml
	cd cmlibi; make ocaml
	cd prover; make ocaml

.PHONY : clean
clean :
	cd basis; make clean
	cd ipp; make clean
	cd cmlibi; make clean
	cd prover; make clean
	cd ui; make clean
	cd core; make clean
	cd library; make clean

