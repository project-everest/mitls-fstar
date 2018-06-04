EXTRACT='Nothing'
FLAVOR?=Model

# NOTE: the `lowparse` target is independent of the rest of miTLS, it
# is there only for CI

all: clean-depend model-all ocaml-all kremlin-all lowparse

lowparse:
	+$(MAKE) -C ../lowparse

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin/.depend cache/Model/.depend

ocaml-%: clean-depend
	$(MAKE) -f Makefile.OCaml $*

kremlin-%: clean-depend
	$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: clean-depend
	$(MAKE) -f Makefile.Model $*

quic-%: clean-depend
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: clean-depend model-test kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean model-clean
	rm -rf extract/Kremlin extract/OCaml extract/copied

%.fst-in %.fsti-in:
	$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver:
	$(MAKE) -f Makefile.Model cache/Model/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
