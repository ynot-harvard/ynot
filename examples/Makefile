MODULES    := Counter Stack Queue LinkedList Array Stream FiniteMap RefFiniteMap HashTable FiniteMap2
# Parse Parse2 
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	make -f Makefile.coq

R := -R ../src Ynot -R . Examples

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc $(R)" \
		COQDEP = "coqdep $(R)" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend
