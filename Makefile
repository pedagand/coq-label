COQLIB=$(subst /,\/,$(shell coqc -where))

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.merlin:
	cp .tools/merlin .merlin
	sed -i s/COQLIB/"$(COQLIB)"/g .merlin

.PHONY: all clean
