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
  LD_LIBRARY_PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(HACL_HOME)/secure_api/out/runtime_switch:$(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: test

clean:
	rm -rf *.o *.exe *~

$(MITLS_HOME)/src/pki/$(LIBPKI):
	make -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS):
	make -j8 -C ../../src/tls -f Makefile.Kremlin build-library

$(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC):
	make -C $(HACL_HOME)/secure_api/QuicProvider

quic.exe: quic.c \
	$(MITLS_HOME)/src/pki/$(LIBPKI) \
	$(HACL_HOME)/secure_api/out/runtime_switch/$(LIBQC) \
	$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	$(CC) -fPIC -I../../src/pki -I../../libs/ffi -I$(HACL_HOME)/secure_api/QuicProvider \
	  -L$(MITLS_HOME)/src/pki \
	  -L$(MITLS_HOME)/src/tls/extract/Kremlin-Library \
	  -L$(HACL_HOME)/secure_api/out/runtime_switch \
	  -L$(MLCRYPTO_HOME)/openssl \
	  -lmitls -lquicprovider -lmipki quic.c -o quic.exe

test: quic.exe
	./quic.exe
	./quic.exe t
