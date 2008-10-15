# $Id: Makefile,v 1.1 2005-11-22 16:22:37 wies Exp $
#
# st -- hash table package
#---------------------------------------------------------------------------
.SUFFIXES: .c .o .u

CC	= gcc
RANLIB	= ranlib

MFLAG	=
ICFLAGS = -g -O6 -Wall
CFLAGS  = $(ICFLAGS) $(MFLAG) $(XCFLAGS)

LINTFLAGS = -u -n

# this is to create the lint library
LINTSWITCH = -o

P	= st
PSRC	= st.c
PHDR	= st.h
POBJ	= st.o
PUBJ	= st.u

WHERE	= ..
INCLUDE = $(WHERE)/include

lib$(P).a: $(POBJ)
	ar r lib$(P).a $(POBJ)
	$(RANLIB) lib$(P).a

.c.o: $(PHDR)
	$(CC) -c $< -I$(INCLUDE) $(CFLAGS) $(DEBUG)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar r lib$(P).b $(PUBJ)
	$(RANLIB) lib$(P).b

.c.u: $(PSRC) $(PHDR)
	cc -j $< -I$(INCLUDE) $(XCFLAGS)

lint: llib-l$(P).ln

llib-l$(P).ln: $(PSRC) $(PHDR)
	lint $(LINTFLAGS) $(LINTSWITCH)$(P) -I$(INCLUDE) $(PSRC)

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b llib-l$(P).ln tags

clean:
	rm -f *.o *.u *.warnings

distclean: clean
	rm -f lib$(P).a lib$(P).b llib-l$(P).ln tags *~ *.bak .pure
