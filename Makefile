FSTAR_HOME    ?= ../FStar
KRML_HOME  ?= ../karamel
HACL_HOME     ?= ../hacl-star
MLCRYPTO_HOME ?= ../MLCrypto
MITLS_HOME    ?= .

all: model-all ocaml-all karamel-all test

model-% verify-% ocaml-% karamel-% quic-%:
	$(MAKE) -C $(MITLS_HOME)/src/tls $*

test clean:
	$(MAKE) -C $(MITLS_HOME)/src/tls $*


# cwinter: todo; put the CI commands here instead of everest-ci/ci?
ci: 
	$(MAKE) -C $(HACL_HOME)/secure_api/LowCProvider
	$(MAKE) -C $(MITLS_HOME)/libs/ffi
	$(MAKE) -C $(MITLS_HOME)/src/pki
	$(MAKE) -C $(MITLS_HOME)/src/tls all -k
	$(MAKE) -C $(MITLS_HOME)/src/tls test -k

%.fst-in %.fsti-in:
	$(MAKE) -C $(MITLS_HOME)/src/tls -f Makefile $@
