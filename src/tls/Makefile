EXTRACT='Nothing'
FLAVOR?=Kremlin

all: refresh-depend kremlin-all

clean-depend:
	rm -f cache/Kremlin/.depend

refresh-depend: clean-depend
	+$(MAKE) -C ../parsers gen

SHELL=/bin/bash

.PHONY: clean-%
clean-c:
	rm -rf extract/Kremlin-{Library,Internal-Test}/{*.c,*/*.c}

kremlin-% verify-%: refresh-depend
	+$(MAKE) -f Makefile.Kremlin $*

quic-%: refresh-depend
	+$(MAKE) -C ../../apps/quicMinusNet $* -k

#TR (2019-03-06): disabling quic-test until merge into master
test: refresh-depend kremlin-test #quic-test

clean: ocaml-clean kremlin-clean quic-clean
	rm -rf extract/Kremlin extract/OCaml extract/copied
	+$(MAKE) -C ../parsers clean

%.fst-in %.fsti-in:
	+$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver: refresh-depend
	rm -f cache/Kremlin/$(notdir $(subst -ver,,$@)).checked
	+$(MAKE) -f Makefile.Kremlin cache/Kremlin/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
