VS      := $(wildcard *.v)
MODULES := $(VS:%.v=%)

.SUFFIXES: .v .vo

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

R := -R ../../src/coq Ynot -R . Parse

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc $(R)" \
		COQDEP = "coqdep $(R)" \
		-o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

.v.vo: $.v
	coqc $(R) -q  -I . $(<:.v=)
