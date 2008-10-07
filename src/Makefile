MODULES    := Axioms Util Heap Hprop ST STsep Separation Ynot
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	make -f Makefile.coq

R := -R . Ynot

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc $(R)" \
		COQDEP = "coqdep $(R)" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend
