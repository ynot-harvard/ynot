all:
	make -C src
	make -C examples

cleandep:
	rm */.depend

clean:
	make -C src clean
	make -C examples clean
	make -C doc clean

doc:
	make -C doc

coqtop:
	coqtop -R src Ynot -R examples Examples

dist: 
	hg archive -t tgz -X private ynot.tgz

.PHONY: all clean coqtop cleandep dist doc
