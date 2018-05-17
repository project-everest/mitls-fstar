FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: FFICallbacks.cmxa # FFICallbacks.cma

clean:
	rm -rf dllFFICallbacks.dll FFICallbacks.a FFICallbacks.cmi FFICallbacks.cmx FFICallbacks.cmxa FFICallbacks.o libFFICallbacks.a FFIRegister.cmi FFIRegister.cmx FFIRegister.o *~

FFICallbacks.cmi: FFICallbacks.mli
	$(OCAMLC) -package batteries,zarith -c FFICallbacks.mli

ffi.o FFICallbacks.cmo FFICallbacks.cmx: FFICallbacks.ml ffi.c FFICallbacks.cmi ffi.c mitlsffi.h
	$(OCAMLC) -package batteries,zarith -c FFICallbacks.ml -ccopt -Wall -ccopt -fPIC ffi.c
	$(OCAMLOPT) -package batteries,zarith -c FFICallbacks.ml -ccopt -Wall -ccopt -fPIC ffi.c

FFICallbacks.cmxa: FFICallbacks.cmx ffi.o
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlfind mklib -o FFICallbacks FFICallbacks.cmx ffi.o

FFICallbacks.cma: FFICallbacks.cmo ffi.o
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlfind mklib -o FFICallbacks FFICallbacks.cmo ffi.o
