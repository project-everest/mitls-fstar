EXTRACT='Nothing'
FLAVOR=generic

all: ocaml-all kremlin-all

include Makefile.common

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

test: ocaml-test kremlin-test

clean: kremlin-clean ocaml-clean
	rm -rf extract/OCaml extract/Kremlin

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_checked_modules --lax
