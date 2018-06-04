EXTRACT='Nothing'
FLAVOR?=Model

# NOTE: this file explicitly verifies LowParse separately before
# verifying miTLS. Verifying LowParse separately assumes that F* ulib
# and KreMLib are already verified.  If you want to disable this
# behavior, you can set the ADMIT_LOWPARSE variable.

all: clean-depend model-all ocaml-all kremlin-all lowparse-examples

lowparse:
ifndef ADMIT_LOWPARSE
	+$(MAKE) -C ../lowparse -f Makefile.LowParse
endif

lowparse-test lowparse-all: lowparse

lowparse-clean:
	+$(MAKE) -C ../lowparse clean
	+$(MAKE) -C ../lowparse -f Makefile.LowParse clean

lowparse-examples: lowparse
	+$(MAKE) -C ../lowparse

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin/.depend cache/Model/.depend

ocaml-%: clean-depend
	+$(MAKE) -f Makefile.OCaml $*

kremlin-%: clean-depend
	+$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: lowparse-% clean-depend
	+$(MAKE) -f Makefile.Model $*

quic-%: lowparse-% clean-depend
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
