MODULES    := Counter Stack Queue Array Stream AssocListModel AssocListOrdModel FiniteMap RefFiniteMap HashTable BinarySearchTree JahobAssocList BinomialTree LinkedListSeg Parse2
VS         := $(MODULES:%=%.v)

.SUFFIXES: .v .vo

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

.v.vo: $.v
	coqc -R ../src Ynot -R . Examples  -q  -I . $(<:.v=) > /dev/null