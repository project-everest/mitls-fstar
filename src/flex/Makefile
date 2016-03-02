#
# Makefile for FlexTLS*
#

.PHONY: all lax codegen build clean


all: build

lax:
	@echo $(CYAN)"[Make] Lax-typechecking FlexTLS."$(NORMAL)

codegen:
	@echo $(CYAN)"[Make] Extracting FlexTLS."$(NORMAL)

build:
	 # miTLS
	@echo $(CYAN)"[Make] Verifying miTLS."$(NORMAL)
	@make tls-ver -C ../tls
	@echo $(CYAN)"[Make] Lax-typechecking miTLS."$(NORMAL)
	@make tls-lax -C ../tls
	@echo $(CYAN)"[Make] Extracting miTLS."$(NORMAL)
	@make tls-gen -C ../tls
	 # FlexTLS
	@make lax
	@make codegen

tt:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(MODULES_CMX) -I test test/main.ml -o flextest.out

clean:
	$(MAKE) -C ../tls clean
	rm -rf *.ml *.p.* *.cm* *.o *~ *.out
	(cd test; rm -rf *.p.* *.cm* *.o *~ *.out)


FSTAR_HOME?=../../.fstar
MITLS_HOME?=../../src

OCAML= ocamlfind ocamlopt
OCAMLOPTS= -package batteries,stdint,fileutils,sqlite3 -linkpkg -g -thread

OCAML_INCLUDE_PATHS= $(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml/hyperheap $(FSTAR_HOME)/lib/ml $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml/db)

MODULES_CMX= \
	$(FSTAR_HOME)/contrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(FSTAR_HOME)/lib/ml/fstarlib-hyperheap.cmxa \
	$(MITLS_HOME)/tls/mitls.cmxa


NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
