EXTRACT='Nothing'
FLAVOR=generic

# Resets the default goal to override any goals in Makefile.common
.DEFAULT_GOAL :=

all: ocaml kremlin

include Makefile.common


ocaml:
	$(MAKE) -f Makefile.OCaml

kremlin:
	$(MAKE) -f Makefile.Kremlin

test: ocaml kremlin
	./mitls.exe
	./mitls-c-test.exe

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_checked_modules --lax
