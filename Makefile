all:
	make -C src
	make -C examples

cleandep:
	rm */.depend

clean:
	make -C src clean
	make -C examples clean

coqtop:
	coqtop -impredicative-set -R src Ynot -R examples Examples

dist: 
	hg archive -t tgz -X paper -X private ynot.tgz

.PHONY: all clean coqtop cleandep dist
