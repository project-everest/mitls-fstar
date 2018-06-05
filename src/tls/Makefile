EXTRACT='Nothing'
FLAVOR?=Model

# NOTE: by default, this file DOES NOT verify LowParse. It only
# verifies and tests LowParse examples and unit tests. If you want to
# verify LowParse, then you can explicit set the VERIFY_LOWPARSE
# variable. In that case, F* ulib and KreMLib MUST have been already
# verified beforehand.

all: clean-depend model-all ocaml-all kremlin-all lowparse-examples

lowparse:
ifdef VERIFY_LOWPARSE
	+$(MAKE) -C ../lowparse -f Makefile.LowParse
endif

lowparse-test lowparse-all: lowparse

lowparse-clean:
	+$(MAKE) -C ../lowparse clean
	+$(MAKE) -C ../lowparse -f Makefile.LowParse clean

lowparse-examples: lowparse
	+$(MAKE) ADMIT_LOWPARSE=1 -C ../lowparse

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin/.depend cache/Model/.depend

ocaml-%: clean-depend
	+$(MAKE) -f Makefile.OCaml $*

kremlin-%: clean-depend
	+$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: lowparse-% clean-depend
	+$(MAKE) -f Makefile.Model $*

quic-%: clean-depend
	+$(MAKE) -C ../../apps/quicMinusNet $* -k

test: clean-depend model-test kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean model-clean lowparse-clean
	rm -rf extract/Kremlin extract/OCaml extract/copied

%.fst-in %.fsti-in:
	+$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver:
	+$(MAKE) -f Makefile.Model cache/Model/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
