all:
	$(MAKE) -C src
	$(MAKE) -C examples

cleandep:
	rm */.depend

clean:
	$(MAKE) -C src clean
	$(MAKE) -C examples clean
	$(MAKE) -C doc clean

doc:
	$(MAKE) -C doc

coqtop:
	coqtop -R src Ynot -R examples Examples

dist: 
	hg archive -t tgz -X private ynot.tgz

install: doc
	cp doc/Tutorial.pdf private/web/
	rsync -az --exclude '*~' private/web/* login.seas.harvard.edu:/deas/services/web/koa/ynot.cs.harvard.edu/htdocs

.PHONY: all clean coqtop cleandep dist doc install
