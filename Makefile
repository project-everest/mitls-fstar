FSTAR_HOME    ?= ../FStar
KREMLIN_HOME  ?= ../kremlin
HACL_HOME     ?= ../hacl-star
MLCRYPTO_HOME ?= ../MLCrypto
MITLS_HOME    ?= .

all: model-all ocaml-all kremlin-all test

model-% verify-% ocaml-% kremlin-% quic-%:
	$(MAKE) -C src/tls $*

test clean:
	$(MAKE) -C src/tls $*

ci: ocaml-all kremlin-all test

%.fst-in %.fsti-in:
	$(MAKE) -C src/tls -f Makefile $@
