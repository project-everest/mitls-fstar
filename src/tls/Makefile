EXTRACT='Nothing'
FLAVOR=generic
include Makefile.common

all: ocaml kremlin

ocaml:
	$(MAKE) -f Makefile.OCaml

kremlin:
	$(MAKE) -f Makefile.Kremlin

test: ocaml kremlin
	./mitls.exe
	./mitls-c-test.exe

%.fst-in %.fsti-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --cache_checked_modules --lax
