MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
MLCRYPTO_HOME ?= ../../../MLCrypto
EVERCRYPT_HOME ?= ../../../evercrypt

UNAME=$(shell uname)
MARCH?=x86_64

ifeq ($(OS),Windows_NT)
  LIBMITLS=libmitls.dll
  LIBPKI=libmipki.dll
  OPENSSL=libcrypto-*.dll
  CC?=$(MARCH)-w64-mingw32-gcc
  PIC=
  WINSOCK=-lws2_32
	ifeq ($(shell uname -o),Cygwin)
	  MITLS_HOME := $(shell cygpath -u ${MITLS_HOME})
	  MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
	  EVERCRYPT_HOME := $(shell cygpath -u ${EVERCRYPT_HOME})
	endif
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(MLCRYPTO_HOME)/openssl
  PATH := $(LIBPATHS):$(PATH)
  export PATH
else ifeq ($(UNAME),Darwin)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC
  WINSOCK=
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library
  DYLD_LIBRARY_PATH := $(LIBPATHS):$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC -lpthread
  WINSOCK=
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(MLCRYPTO_HOME)/openssl
  LD_LIBRARY_PATH := $(LIBPATHS):$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: cmitls.exe

clean:
	rm -rf *.o *.exe *.dll *~

$(MITLS_HOME)/src/pki/$(LIBPKI):
	$(MAKE) -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS):
	$(MAKE) -j8 -C ../../src/tls -f Makefile.Kremlin build-library

cmitls.exe: cmitls.c ../../libs/ffi/mitlsffi.h ../../src/pki/mipki.h \
	$(MITLS_HOME)/src/pki/$(LIBPKI) \
	$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	$(CC) $(CFLAGS) -I../../src/pki -I../../libs/ffi \
	  -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/stub \
	  -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/include \
	  -L$(subst :, -L,$(LIBPATHS)) \
	  -Wall cmitls.c -lmitls -lmipki $(PIC) -o cmitls.exe $(WINSOCK)

test: cmitls.exe
	./cmitls.exe google.com 443
	./cmitls.exe tls13.cloudflare.com 443
