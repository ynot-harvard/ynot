ROOT=./../..

OCAMLC=ocamlc.opt
OCAMLOPT=ocamlopt.opt

EXEC=`basename \`pwd\``

COMPFLAGS=-I ./ml -I .extract -I $(ROOT)/src/ml/

EXTRACTED=$(wildcard .extract/*.ml)

ml: main.byte main.native

main.byte: $(ROOT)/src/ml/ynot.cma ml/main.cmo $(EXTRACTED:%.ml=%.cmo)
	ocamlc $(COMPFLAGS) -o main.byte $(ROOT)/src/ml/ynot.cma .extract/*.cmo ml/main.cmo

main.native: $(ROOT)/src/ml/ynot.cmxa ml/main.cmx  $(EXTRACTED:%.ml=%.cmx)
	ocamlopt.opt $(COMPFLAGS) -o main.native $(ROOT)/src/ml/ynot.cmxa .extract/*.cmx ml/main.cmx

clean:
	rm -f main.byte main.native
	rm -f ml/*.cmo ml/*.cmi ml/*.cmx

include ../Makefile.ynot
include .depend
