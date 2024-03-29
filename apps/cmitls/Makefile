MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
MLCRYPTO_HOME ?= ../../../MLCrypto
EVERCRYPT_HOME ?= ../../../hacl-star/providers

UNAME=$(shell uname)
MARCH?=x86_64

ifeq ($(OS),Windows_NT)
  LIBMITLS=libmitls.dll
  LIBPKI=libmipki.dll
  OPENSSL=libcrypto-*.dll
  CC?=$(MARCH)-w64-mingw32-gcc
  PIC=
  WINSOCK=-lbcrypt -lws2_32
	ifeq ($(shell uname -o),Cygwin)
	  MITLS_HOME := $(shell cygpath -u ${MITLS_HOME})
	  MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
	  EVERCRYPT_HOME := $(shell cygpath -u ${EVERCRYPT_HOME})
	endif
  LIBPATHS=$(EVERCRYPT_HOME)/../dist/gcc-compatible:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Karamel-Library:$(MLCRYPTO_HOME)/openssl
  PATH := $(LIBPATHS):$(PATH)
  export PATH
else ifeq ($(UNAME),Darwin)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC
  WINSOCK=
  LIBPATHS=$(EVERCRYPT_HOME)/../dist/gcc-compatible:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Karamel-Library
  DYLD_LIBRARY_PATH := $(LIBPATHS):$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC -lpthread
  WINSOCK=
  LIBPATHS=$(EVERCRYPT_HOME)/../dist/gcc-compatible:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Karamel-Library:$(MLCRYPTO_HOME)/openssl
  LD_LIBRARY_PATH := $(LIBPATHS):$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: cmitls.exe

clean:
	rm -rf *.o *.exe *.dll *~

copy: $(MITLS_HOME)/src/pki/$(LIBPKI) $(MITLS_HOME)/src/tls/extract/Karamel-Library/$(LIBMITLS)
	cp $(MITLS_HOME)/src/pki/$(LIBPKI) .
	cp $(MLCRYPTO_HOME)/openssl/$(OPENSSL) .
	cp $(MITLS_HOME)/src/tls/extract/Karamel-Library/$(LIBMITLS) .

$(MITLS_HOME)/src/pki/$(LIBPKI):
	$(MAKE) -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Karamel-Library/$(LIBMITLS):
	$(MAKE) -j8 -C ../../src/tls -f Makefile.Karamel build-library

cmitls.exe: cmitls.c ../../libs/ffi/mitlsffi.h ../../src/pki/mipki.h \
	$(MITLS_HOME)/src/pki/$(LIBPKI) \
	$(MITLS_HOME)/src/tls/extract/Karamel-Library/$(LIBMITLS)
	$(CC) $(CFLAGS) -I../../src/pki -I../../libs/ffi \
	  -I$(MITLS_HOME)/src/tls/extract/Karamel-Library/stub \
	  -I$(MITLS_HOME)/src/tls/extract/Karamel-Library/include \
	  -L$(subst :, -L,$(LIBPATHS)) \
	  -Wall cmitls.c -lmitls -lmipki $(PIC) -o cmitls.exe $(WINSOCK)

test: cmitls.exe
	./cmitls.exe google.com 443
	./cmitls.exe www.cloudflare.com 443
