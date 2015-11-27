all: mitls-obj

clean:
	rm -rf *.ml *.cm* *.o *~

FSTAR_HOME=../../../FStar
CDIR_ML=$(FSTAR_HOME)/contrib/CoreCrypto/ml/
PDIR_ML=$(FSTAR_HOME)/contrib/Platform/ml/


ifeq ($(OS),Windows_NT)
    # internally flexlink uses i686-w64-mingw32-gcc.exe
    CC = flexlink -chain mingw -v -v -exe -lgdi32
    # flexlink is needed to link in	/cygdrive/c/OCaml/bin/flexdll_initer_mingw.o /cygdrive/c/OCaml/bin/flexdll_mingw.o
    LIB = $(FSTAR_HOME)/3rdparty/win32 #place to look for libcrypto.a
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = gcc-5
        LIB = $(FSTAR_HOME)/3rdparty/osx #place to look for libcrypto.a
    else
        CC = gcc
        LIB = $(FSTAR_HOME)/3rdparty/x86_64 #place to look for libcrypto.a
    endif
endif

OCAMLC=ocamlfind ocamlc -cc "$(CC)" -cclib -L$(LIB) -cclib -lcrypto -package batteries -package sqlite3 -package fileutils -linkpkg -g -thread
OCAMLOPT=ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -cclib -lcrypto -package batteries -package sqlite3 -package fileutils -linkpkg -g -thread
OCAMLDEP=ocamldep
INCLUDES=-I $(PDIR_ML) -I $(CDIR_ML) $(addprefix -I ../../libs/ml/, DHDB)

OCAML_INCLUDE_PATHS=$(addprefix -I , $(PDIR_ML) $(CDIR_ML)db/ $(CDIR_ML) $(FSTAR_HOME)/lib/ml/hyperheap $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/lib/ml/, native_int/prims.ml hyperheap/FStar_ST.ml hyperheap/FStar_HyperHeap.ml FStar_All.ml FStar_List.ml FStar_String.ml FStar_IO.ml FStar_Set.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, Platform/ml/platform.cmx CoreCrypto/ml/CoreCrypto.cmxa CoreCrypto/ml/db/DB.ml CoreCrypto/ml/DHDB.ml)


OCAMLFLAGS= $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml FStar_SeqProperties.ml  # add other options for ocaml here



# should be computed from the source files
TLSML= TLSError.cmx Nonce.cmx TLSConstants.cmx RSAKey.cmx DHGroup.cmx ECGroup.cmx CommonDH.cmx PMS.cmx HASH.cmx HMAC.cmx Sig.cmx UntrustedCert.cmxi Cert.cmxi TLSInfo.cmx TLSExtensions.cmxi TLSPRF.cmxi Range.cmxi Range.cmx DataStream.cmxi AppFragment.cmxi AppFragment.cmx HSFragment.cmx TLSFragment.cmxi TLSFragment.cmx StatefulPlain.cmxi StatefulPlain.cmx LHAEPlain.cmxi LHAEPlain.cmx MAC_SHA256.cmx MAC_SHA1.cmx MAC.cmxi MAC.cmx Encode.cmxi Encode.cmx ENC.cmx AEAD_GCM.cmx LHAE.cmx StatefulLHAE.cmx Record.cmx Alert.cmx PRF.cmx KEF.cmx DH.cmx RSA.cmx SessionDB.cmxi HandshakeMessages.cmx Handshake.cmxi AppData.cmx Dispatch.cmx TLS.cmx

# FIXME TODO
FStar_Seq.ml:
	$(FSTAR_HOME)/bin/fstar $(FSTAR_HOME)/lib/seq.fst --codegen OCaml --use_native_int

mllibs:
	make -C $(PDIR_ML) clean all
	make -C $(CDIR_ML) clean all
#	make -C ../../libs/ml/DHDB

mitls-obj: $(TLSML)

# Dependencies
depend:
	$(OCAMLDEP) ../../libs/ml/*.ml* *.ml > .depend

-include .depend

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

# ------------------------------------------------------------------------
