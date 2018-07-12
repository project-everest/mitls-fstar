MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
HACL_HOME ?= ../../../hacl-star
MLCRYPTO_HOME ?= ../../../MLCrypto
EVERCRYPT_HOME ?= $(HACL_HOME)/providers

include $(FSTAR_HOME)/ulib/ml/Makefile.include

UNAME=$(shell uname)
MARCH?=x86_64

ifeq ($(OS),Windows_NT)
  LIBMITLS=libmitls.dll
  LIBQC=libquiccrypto.dll
  LIBPKI=libmipki.dll
  OPENSSL=libcrypto-*.dll
  CC?=$(MARCH)-w64-mingw32-gcc
  ifeq ($(shell uname -o),Cygwin)
    MITLS_HOME := $(shell cygpath -u ${MITLS_HOME})
    HACL_HOME := $(shell cygpath -u ${HACL_HOME})
    MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
    EVERCRYPT_HOME := $(shell cygpath -u ${EVERCRYPT_HOME})
  endif
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/providers/quic_provider:$(MLCRYPTO_HOME)/openssl
  PATH := $(LIBPATHS):$(PATH)
  CFLAGS+=-lbcrypt
  export PATH
else ifeq ($(UNAME),Darwin)
  LIBMITLS=libmitls.so
  LIBQC=libquiccrypto.so
  LIBPKI=libmipki.so
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/providers/quic_provider:$(MLCRYPTO_HOME)/openssl
  DYLD_LIBRARY_PATH := $(LIBPATHS):$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  LIBMITLS=libmitls.so
  LIBQC=libquiccrypto.so
  LIBPKI=libmipki.so
  CFLAGS+=-lpthread -pthread
  LIBPATHS=$(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/providers/quic_provider:$(MLCRYPTO_HOME)/openssl
  LD_LIBRARY_PATH := $(LIBPATHS):$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

$(MITLS_HOME)/src/pki/$(LIBPKI):
	$(MAKE) -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS):
	$(MAKE) -j8 -C ../../src/tls -f Makefile.Kremlin build-library

$(HACL_HOME)/providers/quic_provider/$(LIBQC):
	$(MAKE) -j8 -C $(HACL_HOME)/providers/quic_provider

EXTERNAL_HEADERS=\
        $(MITLS_HOME)/src/pki/mipki.h \
        $(HACL_HOME)/secure_api/QuicProvider/quic_provider.h \
        ../../libs/ffi/mitlsffi.h

EXTERNAL_LIBS =\
        $(MITLS_HOME)/src/pki/$(LIBPKI) \
        $(HACL_HOME)/providers/quic_provider/$(LIBQC) \
        $(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)

quic.exe: quic.c $(EXTERNAL_HEADERS) $(EXTERNAL_LIBS)
	$(CC) -fPIC -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/include \
	  -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/stub -I../../src/pki \
	  -I../../libs/ffi -I$(HACL_HOME)/providers/quic_provider \
          -L$(subst :, -L,$(LIBPATHS)) \
	  $< -lmitls -lquiccrypto -lmipki $(CFLAGS) -o $@

test: quic.exe
	./quic.exe
	./quic.exe 0rtt
	./quic.exe hrr

quic12.exe: quic12.c $(EXTERNAL_HEADERS) $(EXTERNAL_LIBS)
	$(CC) -fPIC -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/include \
	  -I$(MITLS_HOME)/src/tls/extract/Kremlin-Library/stub -I../../src/pki \
	  -I../../libs/ffi -I$(HACL_HOME)/providers/quic_provider \
	  -L$(subst :, -L,$(LIBPATHS)) \
	  $< -lmitls -lquiccrypto -lmipki $(CFLAGS) -o $@

test12: quic12.exe
	./quic12.exe

debug12: quic12.exe
	gdb ./quic12.exe

