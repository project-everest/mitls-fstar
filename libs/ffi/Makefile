all: FFICallbacks.cmxa

clean:
	rm -rf dllFFICallbacks.dll FFICallbacks.a FFICallbacks.cmi FFICallbacks.cmx FFICallbacks.cmxa FFICallbacks.o libFFICallbacks.a FFIRegister.cmi FFIRegister.cmx FFIRegister.o *~

FFICallbacks.cmo FFICallbacks.cmi: FFICallbacks.mli
	ocamlfind c -package batteries,zarith -c FFICallbacks.mli

ffi.o FFICallbacks.cmx: FFICallbacks.ml ffi.c FFICallbacks.cmi
	ocamlfind opt -package batteries,zarith -c FFICallbacks.ml -ccopt -Wall -ccopt -fPIC ffi.c
    
FFICallbacks.cmxa: FFICallbacks.cmx ffi.o
	ocamlfind mklib -package batteries,zarith -o FFICallbacks FFICallbacks.cmx ffi.o
