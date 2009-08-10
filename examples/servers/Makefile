ROOT         := ../..

COQTOP=coqtop.opt
COQC=coqc

OCAMLBUILD=ocamlbuild
OCAMLC=ocamlc

LIBRARIES=-lib unix -lib `pwd`/../../mllib/ynot -lib `ocamlfind query ssl`/ssl
LIBRARY_PATH=-I,`ocamlfind query ssl`
CFLAGS=-cflags -I,`pwd`/../../mllib/ -cflags -I,`ocamlfind query ssl`
LFLAGS=-lflags -I,`ocamlfind query ssl`

R=-R $(ROOT)/src/coq Ynot -R $(ROOT)/examples/Parse Parse -R $(ROOT)/examples/Data Data -R $(ROOT)/examples/IO IO


include ../Makefile.ynot

extract: coq ml/ExtractRules ../../mllib/ExtractTemplate.v $(MODULES:%.v=.extract/%.ml)
	@ cp ../../mllib/ExtractTemplate.v Extract.v
	@ echo >> Extract.v
	@ if [ -f ml/ExtractRules ]; then \
            cat ml/ExtractRules >> Extract.v; \
          fi
	@ echo >> Extract.v
	@ if [ -f ml/ExtractExtra ]; then \
            cat ml/ExtractExtra >> Extract.v; \
          fi
	$(COQC) $(COQ_OPTIONS) -I . Extract
	- for x in patch/*.patch; do patch -N -p0 < $$x; done
	@ rm -f Extract.v Extract.vo .extract/*.orig .extract/*.rej

.SUFFIXES: .v .ml .vo

.v.vo: coq

#$(MODULES:%.v=.extract/%.ml): $(@:.extract/%.ml=%.vo) ml/ExtractRules
#	@ mkdir -p .extract
#	@ echo Extracting $(@:.extract/%.ml=%)
#	@ cp ../../mllib/ExtractTemplate.v .Ex$(@:.extract/%.ml=%.v)
#	@ echo >> .Ex$(@:.extract/%.ml=%.v)
#	@ cat ml/ExtractRules >> .Ex$(@:.extract/%.ml=%.v)
#	@ echo "Require Import $(@:.extract/%.ml=%)." >> .Ex$(@:.extract/%.ml=%.v)
#	@ echo "Cd \".extract\"." >> .Ex$(@:.extract/%.ml=%.v)
#	@ echo "Extraction Library $(@:.extract/%.ml=%)." >> .Ex$(@:.extract/%.ml=%.v)
#	@ echo "Cd \"..\"." >> .Ex$(@:.extract/%.ml=%.v)
#	coqtop -q $(COQ_OPTIONS) -I . -compile .Ex$(@:.extract/%.ml=%)
#	@ mv `echo $(@:.extract/%=%) | awk -- '{ print ".extract/" tolower(substr($$1,0,1)) substr($$1,2) }'` $@
#	@ mv `echo $(@:.extract/%=%i) | awk -- '{ print ".extract/" tolower(substr($$1,0,1)) substr($$1,2) }'` $(@:%.ml=%.mli)
#	@ rm -f .Ex$(@:.extract/%.ml=%.vo) .Ex$(@:.extract/%.ml=%.v)

ml/ExtractRules:

#build: extract
#	$(OCAMLBUILD) $(LIBRARIES) $(CFLAGS) $(LFLAGS) -I .extract -I ml main.native
#	@ rm -f _log

