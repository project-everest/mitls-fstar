EXTRACT='Nothing'
FLAVOR?=Model

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin.depend cache/Model/.depend

all: clean-depend ocaml-all kremlin-all

ocaml-%: clean-depend
	$(MAKE) -f Makefile.OCaml $*

kremlin-%: clean-depend
	$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: clean-depend
	$(MAKE) -f Makefile.Model $*

quic-%: clean-depend
	$(MAKE) -C ../../apps/quicMinusNet $* -k

test: clean-depend kremlin-test ocaml-test quic-test

clean: ocaml-clean kremlin-clean quic-clean model-clean
	rm -rf $(EXTRACT_DIR)/Kremlin $(EXTRACT_DIR)/OCaml $(EXTRACT_DIR)/copied \
	*.checked *.checked.lax

%.fst-in %.fsti-in:
	$(MAKE) -f Makefile.$(FLAVOR) $@
