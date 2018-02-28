EXTRACT='Nothing'
FLAVOR?=Model

all: model-all ocaml-all kremlin-all

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

model-% verify-%:
	$(MAKE) -f Makefile.Model $*

quic-%:
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: ocaml-test kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean
	rm -rf $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	rm -rf $(EXTRACT_DIR)/Kremlin $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	$(EXTRACT_DIR)/Kremlin-{Internal-Test,Library}/{,*/}*.{c,h,o} \
	*.checked *.checked.lax

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_dir $(CACHE_DIR) --cache_checked_modules $(OTHERFLAGS) --use_hints --use_hint_hashes
