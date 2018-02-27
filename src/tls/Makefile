EXTRACT='Nothing'
FLAVOR=generic

all:
	rm -f .depend.$(FLAVOR) .depend.verify .depend.OCaml .depend.Kremlin
	$(MAKE) verify-all ocaml-all kremlin-all

clean-depend:
	rm -rf .depend.$(FLAVOR) .depend.verify .depend.OCaml .depend.Kremlin

ocaml-all kremlin-all: clean-depend

include Makefile.common

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

quic-%:
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: ocaml-test kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean
	rm -rf $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	rm -rf $(EXTRACT_DIR)/Kremlin $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	$(EXTRACT_DIR)/Kremlin-{Internal-Test,Library}/{,*/}*.{c,h,o} \
	.depend.$(FLAVOR) .depend.verify *.checked.lax *.checked

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_dir $(CACHE_DIR) --cache_checked_modules $(OTHERFLAGS) --use_hints --use_hint_hashes

# cwinter: should this use lax?
# %.fst-in %.fsti-in:
#	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_checked_modules --lax
