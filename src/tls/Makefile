EXTRACT='Nothing'
FLAVOR?=Model

# ADL (31 Aug. 2018) Disabling ocaml-all during transition to EverCrypt
all: refresh-depend model-all karamel-all #ocaml-all

clean-depend:
	rm -f cache/OCaml/.depend cache/Karamel/.depend cache/Model/.depend

refresh-depend: clean-depend
	+$(MAKE) -C ../parsers gen

SHELL=/bin/bash

.PHONY: clean-%
clean-c:
	rm -rf extract/Karamel-{Library,Internal-Test}/{*.c,*/*.c}

ocaml-%: refresh-depend
	+$(MAKE) -f Makefile.OCaml $*

karamel-%: refresh-depend
	+$(MAKE) -f Makefile.Karamel $*

model-% verify-%: refresh-depend
	+$(MAKE) -f Makefile.Model $*

quic-%: refresh-depend
	+$(MAKE) -C ../../apps/quicMinusNet $* -k

#ADL (31 Aug. 2018) Disabling ocaml-test during transition to EverCrypt
test: refresh-depend karamel-test #quic-test #model-test ocaml-test

clean: ocaml-clean karamel-clean quic-clean model-clean
	rm -rf extract/Karamel extract/OCaml extract/copied
	+$(MAKE) -C ../parsers clean

VFLAGS=
%.fst-in %.fsti-in:
	+$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver: refresh-depend
	rm -f cache/Model/$(notdir $(subst -ver,,$@)).checked
	+$(MAKE) -f Makefile.Model cache/Model/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
