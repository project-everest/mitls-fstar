EXTRACT='Nothing'
FLAVOR?=Model

# ADL (31 Aug. 2018) Disabling ocaml-all during transition to EverCrypt
all: refresh-depend model-all kremlin-all #ocaml-all

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin/.depend cache/Model/.depend

refresh-depend: clean-depend
	+$(MAKE) -C ../parsers gen

SHELL=/bin/bash

.PHONY: clean-%
clean-c:
	rm -rf extract/Kremlin-{Library,Internal-Test}/{*.c,*/*.c}

ocaml-%: refresh-depend
	+$(MAKE) -f Makefile.OCaml $*

kremlin-%: refresh-depend
	+$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: refresh-depend
	+$(MAKE) -f Makefile.Model $*

quic-%: refresh-depend
	+$(MAKE) -C ../../apps/quicMinusNet $* -k

#ADL (31 Aug. 2018) Disabling ocaml-test during transition to EverCrypt
test: refresh-depend model-test kremlin-test quic-test #ocaml-test

clean: ocaml-clean kremlin-clean quic-clean model-clean
	rm -rf extract/Kremlin extract/OCaml extract/copied
	+$(MAKE) -C ../parsers clean

%.fst-in %.fsti-in:
	+$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver: refresh-depend
	rm -f cache/Model/$(notdir $(subst -ver,,$@)).checked
	+$(MAKE) -f Makefile.Model cache/Model/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
