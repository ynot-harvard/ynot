# $Id: Makefile,v 1.1 2005-11-22 16:22:37 wies Exp $
#
# dddmp: Decision Diagram storage and retrieval
#---------------------------------------------------------------------------
.SUFFIXES: .o .c .u

CC	= gcc
RANLIB	= ranlib
# Define EXE as .exe for MS-DOS and derivatives.
PURE	=
EXE	=
#EXE	= .exe

MFLAG	=
ICFLAGS = -g
XCFLAGS =
CFLAGS	= $(ICFLAGS) $(MFLAG) $(XCFLAGS)
DDDEBUG =

LINTFLAGS = -u -n

# this is to create the lint library
LINTSWITCH = -o

WHERE	= ..

INCLUDE = $(WHERE)/include

LIBS	= ./libdddmp.a $(WHERE)/cudd/libcudd.a $(WHERE)/mtr/libmtr.a \
	$(WHERE)/st/libst.a $(WHERE)/util/libutil.a

MNEMLIB =

BLIBS	= -kL. -kldddmp -kL$(WHERE)/cudd -klcudd -kL$(WHERE)/mtr -klmtr \
	-kL$(WHERE)/st -klst -kL$(WHERE)/util -klutil

LINTLIBS = ./llib-ldddmp.ln $(WHERE)/cudd/llib-lcudd.ln \
	$(WHERE)/mtr/llib-lmtr.ln $(WHERE)/st/llib-lst.ln \
	$(WHERE)/util/llib-lutil.ln

LDFLAGS =

# files for the package
P	= dddmp
PSRC    = dddmpDump.c dddmpBinary.c dddmpConvert.c dddmpDbg.c \
          dddmpDdNode.c
PHDR    = dddmp.h dddmpInt.h $(INCLUDE)/cudd.h $(INCLUDE)/cuddInt.h
POBJ	= $(PSRC:.c=.o)
PUBJ	= $(PSRC:.c=.u)
TARGET	= test$(P)$(EXE)
TARGETu = test$(P)-u

# files for the test program
SRC	= test$(P).c
OBJ	= $(SRC:.c=.o)
UBJ	= $(SRC:.c=.u)

#------------------------------------------------------

lib$(P).a: $(POBJ)
	ar r $@ $?
	$(RANLIB) $@

.c.o: $(PHDR)
	$(CC) -c $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar r $@ $?
	$(RANLIB) $@

.c.u: $(PHDR)
	cc -j $< -I$(INCLUDE) $(CFLAGS)

# if the header files change, recompile
$(POBJ): $(PHDR)
$(PUBJ): $(PHDR)
$(OBJ): $(PHDR)
$(UBJ): $(PHDR)

$(TARGET): $(SRC) $(OBJ) $(PHDR) $(LIBS) $(MNEMLIB)
	$(PURE) $(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm

# optimize (DECstations and Alphas only: uses u-code)
$(TARGETu): $(SRC) $(UBJ) $(PHDR) $(LIBS:.a=.b)
	cc -O3 -Olimit 1000 $(XCFLAGS) $(LDFLAGS) -o $@ $(UBJ) $(BLIBS) -lm

lint: llib-l$(P).ln

llib-l$(P).ln: $(PSRC) $(PHDR)
	lint $(LINTFLAGS) $(LINTSWITCH)$(P) -I$(INCLUDE) $(PSRC)

lintpgm: lint
	lint $(LINTFLAGS) -I$(INCLUDE) $(SRC) $(LINTLIBS)

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b llib-l$(P).ln tags

programs: $(TARGET) $(TARGETu) lintpgm

clean:
	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
	.pure core *.warnings

distclean: clean
	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
	*.bak *~ tags .gdb_history *.qv *.qx
