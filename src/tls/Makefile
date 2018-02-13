EXTRACT='Nothing'
FLAVOR=generic

all:
	rm -f .depend.$(FLAVOR)
	$(MAKE) verify-all

include Makefile.common

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

test: ocaml-test

clean: ocaml-clean
	rm -rf $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	.depend.$(FLAVOR) *.checked.lax *.checked

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS))  --cache_dir $(CACHE_DIR) --cache_checked_modules $(OTHERFLAGS) --use_hints --use_hint_hashes
