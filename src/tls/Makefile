EXTRACT='Nothing'
FLAVOR=generic

all:
	rm -f .depend.OCaml .depend.Kremlin
	$(MAKE) ocaml-all kremlin-all

clean-depend:
	rm -rf .depend.OCaml .depend.Kremlin

ocaml-all kremlin-all: clean-depend

include Makefile.common

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

quic-%:
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: kremlin-test quic-test #ocaml-test -- broken until PKI is fixed

clean: kremlin-clean ocaml-clean quic-clean
	rm -rf extract/OCaml extract/Kremlin

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_checked_modules --lax
