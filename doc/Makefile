MODULES := Intro
VS      := $(MODULES:%=%.v)
VOS     := $(MODULES:%=%.vo)
GLOBALS := .coq_globals

.PHONY: coq clean doc html

doc: Tutorial.dvi Tutorial.pdf html

coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -impredicative-set -dump-glob $(GLOBALS)" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend $(GLOBALS)

Tutorial.tex: coq Makefile $(VOS)
	coqdoc --latex -s $(VS) -o Tutorial.tex \
		-p "\usepackage{url}" \
		-p "\title{The Ynot Tutorial}" \
		-p "\author{Adam Chlipala}" \
		-p "\iffalse"

Tutorial.dvi: Tutorial.tex
	latex Tutorial ; latex Tutorial

Tutorial.pdf: Tutorial.dvi
	pdflatex Tutorial

html: coq Makefile $(VOS)
	coqdoc $(VS) --glob-from $(GLOBALS) -d html/
