EXTRACT='Nothing'
FLAVOR=generic

all:
	$(MAKE) verify-all 
	$(MAKE) ocaml-all 
	$(MAKE) kremlin-all

ocaml-clean-depend:
	rm -f .depend.OCaml

kremlin-clean-depend:
	rm -f .depend.Kremlin

ocaml-all: ocaml-clean-depend
kremlin-all: kremlin-clean-depend

include Makefile.common

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

quic-%:
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: ocaml-test kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean ocaml-clean-depend kremlin-clean-depend
	rm -rf $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	rm -rf $(EXTRACT_DIR)/Kremlin $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	$(EXTRACT_DIR)/Kremlin-{Internal-Test,Library}/{,*/}*.{c,h,o} \
	.depend.$(FLAVOR) *.checked

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_dir $(CACHE_DIR) --cache_checked_modules $(OTHERFLAGS) --use_hints --use_hint_hashes
