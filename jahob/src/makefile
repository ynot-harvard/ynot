# for profiling:
#OCAMLC=ocamlcp 
OCAMLC=ocamlc.opt
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc
DIRS=ast bapa decision form isabelle coq tptp \
     jast joust main mona parspec presburger \
     simplify util vcgen smtlib bohne
INCLUDES=-I ast -I bapa -I decision -I form -I isabelle -I coq -I tptp \
	-I jast -I joust -I main -I mona -I parspec -I presburger \
	-I simplify -I util -I vcgen -I smtlib -I bohne
#OCAMLFLAGS=-dtypes $(INCLUDES)    # add other options for ocamlc here
#OCAMLOPTFLAGS=-dtypes $(INCLUDES) # add other options for ocamlopt here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here
OCAMLYACC=ocamlyacc
OCAMLYACCFLAGS=
OCAMLLEX=ocamllex
BIN=../bin
DOC=../doc
LIB=../lib
DOC_SRC=*/*.ml */*.mli
DEP_DOT_FILE=$(DOC)/depend/dependencies.dot
DEP_PS_FILE=$(DOC)/depend/dependencies.ps
DEP_PDF_FILE=$(DOC)/depend/dependencies.pdf

all: $(BIN)/testForm $(BIN)/bapa $(BIN)/jpprint \
	$(BIN)/jahob \
	$(BIN)/pres \
	$(BIN)/timed_command $(BIN)/genbapa $(BIN)/testinf \
	$(BIN)/testmona

COMMON_FILES=util/util.cmo util/debug.cmo \
	main/common.cmo main/cmdLine.cmo

# ------------------------------------------------------------
# form/
# ------------------------------------------------------------

form/yaccForm.output form/yaccForm.mli form/yaccForm.ml: form/yaccForm.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) form/yaccForm.mly

form/lexForm.ml: form/lexForm.mll
	$(OCAMLLEX) form/lexForm.mll

FORM_FILES=form/form.cmo form/typeVars.cmo form/mlPrintForm.cmo form/printForm.cmo form/formUtil.cmo \
	form/parsingFormAux.cmo form/yaccForm.cmo form/lexForm.cmo \
	form/parseForm.cmo form/typeReconstruct.cmo form/termRewrite.cmo coq/printFormCoq.cmo form/folTranslation.cmo

TESTFORM_FILES=$(COMMON_FILES) $(FORM_FILES) smtlib/smtPrint.cmo tptp/tptpPrettyPrinter.cmo form/testForm.cmo

testForm: $(BIN)/testForm

$(BIN)/testForm: $(TESTFORM_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma $(TESTFORM_FILES)

# ------------------------------------------------------------
# isabelle/
# ------------------------------------------------------------

ISABELLE_FILES=isabelle/vclemmas.cmo isabelle/isabelle.cmo 

# ------------------------------------------------------------
# Coq/
# ------------------------------------------------------------

COQ_FILES=coq/printFormCoq.cmo coq/coq.cmo 

# ------------------------------------------------------------
# TPTP/
# ------------------------------------------------------------

TPTP_FILES=tptp/tptpPrettyPrinter.cmo tptp/spassPrettyPrinter.cmo

# ------------------------------------------------------------
# ast/
# ------------------------------------------------------------

TESTAST_FILES=$(COMMON_FILES) $(FORM_FILES) \
	ast/ast.cmo ast/astUtil.cmo $(ISABELLE_FILES) ast/resolveAst.cmo ast/printAst.cmo

$(BIN)/testAst: $(TESTAST_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma $(TESTAST_FILES)

# ------------------------------------------------------------
#                        DECISION PROCEDURES
# ------------------------------------------------------------

# ------------------------------------------------------------
# mona/
# ------------------------------------------------------------

MONA_FILES=mona/monaForm.cmo mona/monaPrint.cmo mona/monaUtil.cmo \
	mona/monaConvert.cmo mona/mona.cmo

TEST_MONA_FILES=$(FORM_FILES) $(MONA_FILES) mona/testMona.cmo

$(BIN)/testmona: $(COMMON_FILES) $(TEST_MONA_FILES)
	$(OCAMLC) -g -o $(BIN)/testmona $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(TEST_MONA_FILES)

# ------------------------------------------------------------
# presburger/
# ------------------------------------------------------------

# ------------------------------------------------------------

PRES_FILES=presburger/presburger.cmo

$(BIN)/pres: $(COMMON_FILES) $(PRES_FILES)
	$(OCAMLC) -g -o $(BIN)/pres $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(PRES_FILES)

# ------------------------------------------------------------
# simplify/
# ------------------------------------------------------------

SIMPLIFY_FILES=simplify/simplify.cmo

# ------------------------------------------------------------
# bapa/
# ------------------------------------------------------------

BAPA_FILES=$(FORM_FILES) $(PRES_FILES) \
	bapa/alpha.cmo bapa/bapapres.cmo form/typeinf.cmo bapa/formbapa.cmo \
	form/parsingFormAux.cmo form/yaccForm.cmo form/lexForm.cmo \
	form/parseForm.cmo form/printForm.cmo bapa/bapa.cmo

TEST_BAPA_FILES=$(BAPA_FILES) $(SIMPLIFY_FILES) bapa/testBapa.cmo

$(BIN)/bapa: $(TEST_BAPA_FILES)
	$(OCAMLC) -g -o $(BIN)/bapa $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(TEST_BAPA_FILES)

# ------------------------------------------------------------
# generate bapa formula/
# ------------------------------------------------------------

GEN_BAPA_FILES=$(BAPA_FILES) bapa/genbapa.ml
$(BIN)/genbapa: $(GEN_BAPA_FILES)
	$(OCAMLC) -g -o $(BIN)/genbapa $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(GEN_BAPA_FILES)

# ------------------------------------------------------------
# smtlib/
# ------------------------------------------------------------

SMTLIB_FILES=smtlib/smtPrint.cmo

# ------------------------------------------------------------
# type inference/
# ------------------------------------------------------------

TYPE_INF_FILES=form/typeinf.cmo form/testInf.cmo

$(BIN)/testinf: $(COMMON_FILES) $(FORM_FILES) $(TYPE_INF_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(FORM_FILES) $(BAPA_FILES) $(TYPE_INF_FILES)

# ------------------------------------------------------------
# decision/
# ------------------------------------------------------------

DECISION_FILES=$(FORM_FILES) $(ISABELLE_FILES) $(COQ_FILES) $(MONA_FILES) \
	$(BAPA_FILES) $(SIMPLIFY_FILES) $(SMTLIB_FILES) $(TPTP_FILES)\
	decision/slice.cmo decision/decider.cmo decision/idecider.cmo \
	decision/cachedDecider.cmo

$(BIN)/idecider: $(DECISION_FILES)
	$(OCAMLC) -g -o $(BIN)/idecider $(OCAMLFLAGS) unix.cma str.cma \
	$(COMMON_FILES) $(DECISION_FILES)

# ------------------------------------------------------------
#                        SYNTAX TREES
# ------------------------------------------------------------

# ------------------------------------------------------------
# joust/
# ------------------------------------------------------------

joust/parser.output joust/parser.mli joust/parser.ml: joust/parser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) joust/parser.mly

joust/lexer.ml: joust/lexer.mll
	$(OCAMLLEX) joust/lexer.mll

JOUST_FILES=joust/source.cmo \
	joust/syntax.cmo \
	joust/reserved.cmo \
	joust/pretty.cmo \
	joust/lexer.cmo \
	joust/parser.cmo

JPPRINT_FILES=$(JOUST_FILES) joust/comtest.cmo

$(BIN)/jpprint: $(JPPRINT_FILES)
	$(OCAMLC) -g -o $(BIN)/jpprint $(OCAMLFLAGS) unix.cma str.cma \
	$(JPPRINT_FILES)

# ------------------------------------------------------------
# parspec/
# ------------------------------------------------------------

parspec/yaccSpec.output parspec/yaccSpec.mli parspec/yaccSpec.ml: parspec/yaccSpec.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) parspec/yaccSpec.mly

parspec/lexSpec.ml: parspec/lexSpec.mll
	$(OCAMLLEX) parspec/lexSpec.mll

PARSPEC_FILES=$(FORM_FILES) parspec/specs.cmo \
	parspec/parsingSpecAux.cmo parspec/yaccSpec.cmo parspec/lexSpec.cmo \
	parspec/parseSpec.cmo \
	jast/jtype.cmo jast/jast.cmo parspec/printSpec.cmo

# ------------------------------------------------------------
# bohne/
# ------------------------------------------------------------

$(LIB)/cudd/lib/libcudd.a: 
	make -C $(LIB)/cudd

bohne/caddie.o: bohne/caddie.c
	$(OCAMLC) -c -cc "gcc" -ccopt "-fPIC -I`ocamlc -where`/caml \
	  -I$(LIB)/cudd/include -DPIC -DNATIVE_CODE \
	  -o bohne/caddie.o"  $<

CCOPTS += -ccopt -L$(LIB)/cudd/lib -cclib -lcudd -cclib -lst -cclib -lmtr -cclib -lutil

BOHNE_FILES=$(LIB)/cudd/lib/libcudd.a bohne/caddie.o bohne/caddieBdd.cmo \
	bohne/bf.cmo bohne/bf_set.cmo bohne/bohneUtil.cmo bohne/pred.cmo \
	bohne/bohneProgram.cmo bohne/abstraction.cmo bohne/region.cmo \
	bohne/bohneRefine.cmo bohne/bohne.cmo bohne/bohneDecaf.cmo \
	bohne/bohneInterface.cmo


# ------------------------------------------------------------
# main/
# ------------------------------------------------------------

JAHOB_FILES=$(COMMON_FILES) $(JOUST_FILES) $(PARSPEC_FILES) \
	ast/ast.cmo ast/astUtil.cmo jast/jastUtil.cmo \
	$(DECISION_FILES) \
	ast/astUtil.cmo ast/resolveAst.cmo ast/printAst.cmo \
	joust/pretty.cmo jast/jastconsistency.cmo  \
	jast/jastjava.cmo jast/jast2ast.cmo jast/javajast.cmo \
	vcgen/background.cmo vcgen/sast.cmo vcgen/vcgen.cmo \
	vcgen/loopInvariantInference.cmo \
	$(BOHNE_FILES) \
	main/analyze.cmo main/jahob.cmo \


$(BIN)/jahob: $(JAHOB_FILES)
	$(OCAMLC) -custom -g -o $(BIN)/jahob $(OCAMLFLAGS) unix.cma str.cma \
	$(JAHOB_FILES) $(CCOPTS)

# ------------------------------------------------------------
# $(BIN)/timed_command
# ------------------------------------------------------------

$(BIN)/timed_command: unix-utils/timed_command.c
	gcc -o $(BIN)/timed_command unix-utils/timed_command.c

# ------------------------------------------------------------
# html documentation
# ------------------------------------------------------------

doc: $(DOC_SOURCES)
	$(OCAMLDOC) -t "Jahob Documentation" -html -d $(DOC)/html $(INCLUDES) \
		 */*.ml */*.mli

docdep:
	$(OCAMLDOC) -dot -t "Jahob Dependencies" -o $(DEP_DOT_FILE) $(INCLUDES) \
		-dot-reduce */*.ml */*.mli; \
	dot -Tps -o $(DEP_PS_FILE) $(DEP_DOT_FILE); \
	ps2pdf $(DEP_PS_FILE) $(DEP_PDF_FILE)

docmanual:
	cd ../doc/manual; \
	./l

# ------------------------------------------------------------
# Common rules
# ------------------------------------------------------------
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mly .mll

.ml.annot:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Clean up
cleanast:
	cd ast; \
	rm -f *.cm[iox] *.annot

cleanbapa:
	cd bapa; \
	rm -f *.cm[iox] *.annot

cleandecision:
	cd decision; \
	rm -f *.cm[iox] *.annot

cleanform:
	rm -f $(BIN)/testForm; \
	cd form; \
	rm -f *.cm[iox] *.annot \
	rm -f yaccForm.ml yaccForm.mli lexForm.ml

cleanmona:
	rm -f $(BIN)/testmona; \
	cd mona; \
	rm -f *.cm[iox] *.annot \

cleanparspec:
	cd parspec; \
	rm -f *.cm[iox] *.annot \
	rm -f yaccSpec.ml yaccSpec.mli lexSpec.ml

cleanjast:
	cd jast; \
	rm -f *.cm[iox] *.annot

cleanjoust:
	cd joust; \
	rm -f *.cm[iox] *.annot \
	rm -f parser.ml parser.mli lexer.ml

	rm -f *.cm[iox] *.annot

cleanpres:
	cd presburger; \
	rm -f *.cm[iox] *.annot

cleanutil:
	cd util; \
	rm -f *.cm[iox] *.annot

cleanvcgen:
	cd vcgen; \
	rm -f *.cm[iox] *.annot

cleansimplify:
	cd simplify; \
	rm -f *.cm[iox] *.annot

cleansmtlib:
	cd smtlib; \
	rm -f *.cm[iox] *.annot

cleanisabelle:
	cd isabelle; \
	rm -f *.cm[iox] *.annot

cleanbohne:
	cd bohne; \
	rm -f *.cm[iox] *.o *.annot

cleanmain:
	cd main; \
	rm -f *.cm[iox] *.o *.annot

cleantptp:
	cd tptp; \
	rm -f *.cm[iox] *.o *.annot

clean: cleanast cleanbapa cleandecision cleanform cleanparspec \
	cleanjast cleanjoust cleanmona cleanpres cleanutil cleanvcgen \
	cleanmain cleanisabelle cleansimplify cleansmtlib cleanbohne \
	cleantptp

# Dependencies
beforedepend: form/yaccForm.mli form/yaccForm.ml form/lexForm.ml \
	parspec/yaccSpec.mli parspec/yaccSpec.ml parspec/lexSpec.ml \
	joust/parser.mli joust/parser.ml joust/lexer.ml \

depend: beforedepend
	(for d in $(DIRS); \
	do $(OCAMLDEP) $(INCLUDES) $$d/*.mli $$d/*.ml; \
	done) > .depend

-include .depend
