all: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: all
	$(MAKE) -f Makefile.coq install

uninstall: all
	$(MAKE) -f Makefile.coq uninstall

mrproper:
	rm -f Makefile.coq

html: Makefile.coq
	rm -f website/MetaCoq*.html
	$(MAKE) -f Makefile.coq html
	mv html/*.html ./website
	rm -rf html
