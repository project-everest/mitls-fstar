FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: MiTLS_FFICallbacks.cmxa # MiTLS_FFICallbacks.cma

clean:
	rm -rf dllMiTLS_FFICallbacks.dll MiTLS_FFICallbacks.a MiTLS_FFICallbacks.cmi MiTLS_FFICallbacks.cmx MiTLS_FFICallbacks.cmxa MiTLS_FFICallbacks.o libMiTLS_FFICallbacks.a MiTLS_FFIRegister.cmi MiTLS_FFIRegister.cmx MiTLS_FFIRegister.o *~

MiTLS_FFICallbacks.cmi: MiTLS_FFICallbacks.mli
	$(OCAMLC) -package batteries,zarith -c MiTLS_FFICallbacks.mli

ffi.o MiTLS_FFICallbacks.cmo MiTLS_FFICallbacks.cmx: MiTLS_FFICallbacks.ml ffi.c MiTLS_FFICallbacks.cmi ffi.c mitlsffi.h
	$(OCAMLC) -package batteries,zarith -c MiTLS_FFICallbacks.ml -ccopt -Wall -ccopt -fPIC ffi.c
	$(OCAMLOPT) -package batteries,zarith -c MiTLS_FFICallbacks.ml -ccopt -Wall -ccopt -fPIC ffi.c

MiTLS_FFICallbacks.cmxa: MiTLS_FFICallbacks.cmx ffi.o
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlfind mklib -o MiTLS_FFICallbacks MiTLS_FFICallbacks.cmx ffi.o

MiTLS_FFICallbacks.cma: MiTLS_FFICallbacks.cmo ffi.o
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlfind mklib -o MiTLS_FFICallbacks MiTLS_FFICallbacks.cmo ffi.o
