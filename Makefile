all: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: all install html clean distclean

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

distclean: clean
	rm -rf Makefile.coq .merlin Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin
