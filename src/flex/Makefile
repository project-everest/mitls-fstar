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

clean:
	$(MAKE) -C ../tls clean
	rm -rf *.ml *.p.* *.cm* *.o *~ *.out


FSTAR_HOME?=../../.fstar

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
