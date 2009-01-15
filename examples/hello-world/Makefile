#Path to the Ynot Root
ROOT=./../..

COQTOP=coqtop.opt
COQC=coqc
R=-R $(ROOT)/src/coq Ynot

OCAMLC=ocamlc

LIBRARIES=

MODULES_T=$(wildcard *.v)
MODULES=$(filter-out Extract.v,$(MODULES_T))

EXTRACT_NAME=HelloWorld

all: coq

coq: Makefile.coq $(MODULES)
	$(MAKE)  -f Makefile.coq

Makefile.coq: $(MODULES)
	coq_makefile $(R) -o Makefile.coq $(MODULES)

.extract/$(EXTRACT_NAME).ml: coq
	mkdir -p .extract
	coqc -I . $(R) Extract.v

build: .extract/$(EXTRACT_NAME).ml
	mkdir -p .extract
	ocamldep.opt -I $(ROOT)/src/ml/ -I .extract -I ml .extract/*.ml  ml/*.ml ../../src/ml/*.ml > .depend
	ocamldep.opt -I $(ROOT)/src/ml/ -I .extract -I ml .extract/*.mli ml/*.mli $(ROOT)/src/ml/*.mli >> .depend
	$(MAKE)  -f Makefile.ml

.SUFFIXES: .v .vo .ml .mli .cmo .cmi

clean:
	touch .depend
	$(MAKE)  -f Makefile.ml clean
	rm -rf .extract/
	rm -f *.vo
	rm -f .depend Makefile.coq	

include ../Makefile.ynot