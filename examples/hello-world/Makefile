#Path to the Ynot Root
ROOT=./../..

COQTOP=coqtop
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

Makefile.coq: $(ROOT)/src/coq/Ynot.vo $(MODULES)
	coq_makefile $(R) -o Makefile.coq $(MODULES)

.SUFFIXES: .v .vo .ml .mli .cmo .cmi

clean:
	touch .depend
	$(MAKE)  -f Makefile.ocaml clean
	rm -rf .extract/
	rm -f *.vo
	rm -f .depend Makefile.coq	

include ../Makefile.ynot