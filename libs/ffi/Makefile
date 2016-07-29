all: FFICallbacks.cmxa

clean:
	rm -rf dllFFICallbacks.dll FFICallbacks.a FFICallbacks.cmi FFICallbacks.cmx FFICallbacks.cmxa FFICallbacks.o libFFICallbacks.a FFIRegister.cmi FFIRegister.cmx FFIRegister.o

FFICallbacks.cmo FFICallbacks.cmi: FFICallbacks.mli
	ocamlfind c -package batteries -c FFICallbacks.mli

ffi.o FFICallbacks.cmx: FFICallbacks.ml ffi.c FFICallbacks.cmi
	ocamlfind opt -package batteries -c FFICallbacks.ml -ccopt -Wall ffi.c
    
FFICallbacks.cmxa: FFICallbacks.cmx ffi.o
	ocamlfind mklib -package batteries -o FFICallbacks FFICallbacks.cmx ffi.o
