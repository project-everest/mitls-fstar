FSTAR_HOME = ../../../FStar
MLCRYPTO_HOME ?= ../../../MLCrypto
CONTRIB=ucontrib
PLATFORM = $(FSTAR_HOME)/$(CONTRIB)/Platform/ml
OPENSSL_HOME = $(MLCRYPTO_HOME)/openssl
INCLUDE=-package batteries,zarith -I $(PLATFORM)
MARCH?=x86_64

OCAMLC = ocamlfind c $(INCLUDE) -g -annot
OCAMLOPT = ocamlfind opt $(INCLUDE) -g -annot
OCAMLMKLIB = ocamlfind mklib $(INCLUDE)
OCAMLDEP = ocamlfind dep -slash

CCOPTS = -std=c11 -D__USE_MINGW_ANSI_STDIO -g
ifndef NO_OPENSSL
CCOPTS += -Lopenssl -I$(OPENSSL_HOME)/include
else
CCOPTS += -DNO_OPENSSL
endif

ifeq ($(OS),Windows_NT)
    # On cygwin + cygwinports, DLLs are searched in the PATH, which is not
    # altered to include by default the mingw64 native DLLs. We also need to
    # find dllcorecrypto.dll; it is in the current directory, which Windows
    # always uses to search for DLLs.
    EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    VS_BIN = $(shell ../../scripts/vsbin.sh)
    ARCH = win32
    EXTRA_OPTS =
    EXTRA_LIBS = -L.
    CC = $(MARCH)-w64-mingw32-gcc
    ifeq ($(MARCH),x86_64)
      LIB_MACHINE=x64
      OPENSSL_CONF = CC=x86_64-w64-mingw32-gcc ./Configure mingw64 enable-tls1_3
    else
      LIB_MACHINE=x86
      OPENSSL_CONF = CC=i686-w64-mingw32-gcc ./Configure mingw enable-tls1_3
    endif
    LIBMIPKI := libmipki.dll
else
    # On Unix-like systems, the library search path is LD_LIBRARY_PATH, which is
    # correctly setup to find libssleay.so and the like, but never includes the
    # current directory, which is where dllcorecrypto.so is located.
    EXTRA_PATH = LD_LIBRARY_PATH=.
    VS_BIN =
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        EXTRA_OPTS =
        EXTRA_LIBS = -L.
        ARCH = osx
        OPENSSL_CONF = ./config enable-tls1_3
    else
        EXTRA_OPTS = -fPIC
        EXTRA_LIBS = -L.
        ARCH = x86_64
        OPENSSL_CONF = ./config enable-tls1_3 -fPIC
    endif
    LIBMIPKI := libmipki.so
endif

ifeq ($(VS_BIN),)
LIBFILE=
else
LIBFILE=libmipki.lib
libmipki.lib: libmipki.dll
	"$(VS_BIN)/dumpbin.exe" /nologo /exports libmipki.dll | awk -F " " 'BEGIN {print "LIBRARY libmipki"; print "EXPORTS";} $$4 ~/mipki_/{print $$4}' > libmipki.def
	"$(VS_BIN)/lib.exe" /nologo /def:libmipki.def /out:$@ /machine:$(LIB_MACHINE)
	-rm *.def *.exp
endif

.PHONY: test clean

all: $(LIBMIPKI) $(LIBFILE)

mipki.o: mipki.c mipki.h
	$(CC) $(CCOPTS) $(EXTRA_OPTS) -c mipki.c

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

$(PLATFORM)/platform.cmx: $(PLATFORM)/platform.ml
	$(MAKE) -C $(PLATFORM)


ifndef NO_OPENSSL

$(OPENSSL_HOME)/Configure:
	echo "openssl folder is empty, please update submodules in $(MLCRYPTO_HOME)"
	false

$(OPENSSL_HOME)/libcrypto.a: $(OPENSSL_HOME)/Configure
	cd $(OPENSSL_HOME) && $(OPENSSL_CONF)
	$(MAKE) -C $(OPENSSL_HOME) build_libs

libcrypto.a: $(OPENSSL_HOME)/libcrypto.a
	cp $(OPENSSL_HOME)/libcrypto.a .

libmipki.dll: libcrypto.a mipki.o
	$(CC) $(COPTS) -shared mipki.o libcrypto.a -lws2_32 -o $@

libmipki.so: libcrypto.a mipki.o
	$(CC) $(COPTS) -shared mipki.o libcrypto.a -o $@

else # NO_OPENSSL

libmipki.dll: mipki.o
	$(CC) $(COPTS) -DNO_OPENSSL -shared mipki.o -lws2_32 -o $@

libmipki.so: mipki.o
	$(CC) $(COPTS) -DNO_OPENSSL -shared mipki.o -o $@

endif


test.exe: $(LIBMIPKI) test.c
	$(CC) $(COPTS) -L. -lmipki test.c -o $@

test: test.exe
	@./test.exe

#DLL_OBJ = $(PLATFORM)/platform.cmx CoreCrypto.cmx openssl_stub.o # $(DB)/DB.cmx DHDB.cmx
#CoreCrypto.cmxa: $(DLL_OBJ)
#	$(OCAMLMKLIB) $(EXTRA_LIBS) $(CCLIBS) -o CoreCrypto $(DLL_OBJ)
#
#DLL_BYTE = $(PLATFORM)/platform.cmo CoreCrypto.cmo openssl_stub.o # DHDB.cmo $(DB)/DB.cmo
#CoreCrypto.cma: $(DLL_BYTE)
#	$(OCAMLMKLIB) $(EXTRA_LIBS) -o CoreCrypto $^

clean:
	$(MAKE) -C $(PLATFORM) clean
	rm -f *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.lib *.annot *~
