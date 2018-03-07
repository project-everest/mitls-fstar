EXTRACT='Nothing'
FLAVOR?=Model

all: model-all
# to be selected depending on the branch, e.g. just model-all for verify.
#all: model-all ocaml-all kremlin-all

ocaml-%:
	$(MAKE) -f Makefile.OCaml $*

kremlin-%:
	$(MAKE) -f Makefile.Kremlin $*

model-% verify-%:
	$(MAKE) -f Makefile.Model $*

quic-%:
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean model-clean
	rm -rf $(EXTRACT_DIR)/Kremlin $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	*.checked *.checked.lax

%.fst-in %.fsti-in:
	$(MAKE) -f Makefile.$(FLAVOR) $@
