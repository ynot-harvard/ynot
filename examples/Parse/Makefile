ROOT    := ../..

VS      := Charset.v Stream.v Parsec.v ParsecCombinators.v Packrat.v
MODULES := $(VS:%.v=%)

include ../Makefile.ynot

#.SUFFIXES: .v .vo

#.PHONY: coq clean

#coq: Makefile.coq
#	$(MAKE) -f Makefile.coq

#R := -R ../../src/coq Ynot -R ../Data Data -R . Parse

#Makefile.coq: Makefile $(VS)
#	coq_makefile $(VS) \
#		COQC = "coqc $(R)" \
#		COQDEP = "coqdep $(R)" \
#		-o Makefile.coq

#clean:: Makefile.coq
#	$(MAKE) -f Makefile.coq clean
#	rm -f Makefile.coq .depend

#.v.vo: $.v
#	coqc $(R) -q  -I . $(<:.v=)
