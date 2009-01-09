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

install: doc
	cp doc/Tutorial.pdf private/web/
	rsync -az --exclude '*~' private/web/* login.seas.harvard.edu:/deas/services/web/koa/ynot.cs.harvard.edu/htdocs

.PHONY: all clean coqtop cleandep dist doc install
