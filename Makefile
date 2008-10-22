all:
	make -C src
	make -C examples

clean:
	make -C src clean
	make -C examples clean

coqtop:
	coqtop -impredicative-set -R src Ynot -R examples Examples

dist: 
	hg archive -t tgz -X SIGNUP ynot.tgz

.PHONY: all clean coqtop