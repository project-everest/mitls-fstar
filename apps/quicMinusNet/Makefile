MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
HACL_HOME ?= ../../../hacl-star
MLCRYPTO_HOME ?= ../../../MLCrypto

include $(FSTAR_HOME)/ulib/ml/Makefile.include

UNAME=$(shell uname)
MARCH?=x86_64

ifeq ($(OS),Windows_NT)
  LIBMITLS=libmitls.dll
  LIBQC=libquicprovider.dll
  LIBPKI=libmipki.dll
  OPENSSL=libcrypto-*.dll
  CC?=$(MARCH)-w64-mingw32-gcc
  ifeq ($(shell uname -o),Cygwin)
    MITLS_HOME := $(shell cygpath -u ${MITLS_HOME})
    HACL_HOME := $(shell cygpath -u ${HACL_HOME})
    MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
  endif
  PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/secure_api/out/runtime_switch:$(MLCRYPTO_HOME)/openssl:$(PATH)
  export PATH
else ifeq ($(UNAME),Darwin)
  LIBMITLS=libmitls.so
  LIBQC=libquicprovider.so
  LIBPKI=libmipki.so
  DYLD_LIBRARY_PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/secure_api/out/runtime_switch:$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  LIBMITLS=libmitls.so
  LIBQC=libquicprovider.so
  LIBPKI=libmipki.so
  CFLAGS+=-lpthread
  LD_LIBRARY_PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/secure_api/out/runtime_switch:$(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

$(MITLS_HOME)/src/pki/$(LIBPKI):
	$(MAKE) -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS):
	$(MAKE) -j8 -C ../../src/tls -f Makefile.Kremlin build-library

$(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC):
	$(MAKE) -j8 -C $(HACL_HOME)/secure_api

copy: $(LIBMITLS) $(LIBPKI) $(LIBQC)

$(LIBMITLS): $(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	cp $(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS) .

$(LIBPKI): $(MITLS_HOME)/src/pki/$(LIBPKI)
	cp $(MITLS_HOME)/src/pki/$(LIBPKI) .
	cp $(MLCRYPTO_HOME)/openssl/$(OPENSSL) .

$(LIBQC): $(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC)
	cp $(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC) .

quic.exe: quic.c \
	$(MITLS_HOME)/src/pki/$(LIBPKI) \
	$(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC) \
	$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	$(CC) -fPIC -I../../src/tls/extract/Kremlin-Library/stub -I../../src/pki -I../../libs/ffi -I$(HACL_HOME)/secure_api/QuicProvider \
	  -L$(MITLS_HOME)/src/pki \
	  -L$(MITLS_HOME)/src/tls/extract/Kremlin-Library \
	  -L$(HACL_HOME)/secure_api/out/runtime_switch \
	  -L$(MLCRYPTO_HOME)/openssl \
	  -lmitls -lquicprovider -lmipki quic.c $(CFLAGS) -o quic.exe

test: quic.exe
	./quic.exe
	./quic.exe t
