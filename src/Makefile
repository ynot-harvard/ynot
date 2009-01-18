.PHONY: coq clean

coq: coq/Makefile.coq
	(cd coq; $(MAKE) -f Makefile.coq)

R := -R . Ynot

coq/Makefile.coq: Makefile $(VS:%=coq/%)
	(cd coq; coq_makefile $(VS) \
	             COQC = "coqc $(R)" \
		     COQDEP = "coqdep $(R)" \
		     -o Makefile.coq)

clean:: coq/Makefile.coq
	(cd coq; $(MAKE) -f Makefile.coq clean)
	rm -f coq/Makefile.coq coq/.depend
	rm -f ocaml/*.{cmo,cmi,cmx,o,cma,cmxa,a}
