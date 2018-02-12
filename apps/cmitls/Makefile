MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
MLCRYPTO_HOME ?= ../../../MLCrypto

include $(FSTAR_HOME)/ulib/ml/Makefile.include

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
	endif
  PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(MLCRYPTO_HOME)/openssl:$(PATH)
  export PATH
else ifeq ($(UNAME),Darwin)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC
  WINSOCK=
  DYLD_LIBRARY_PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  LIBMITLS=libmitls.so
  LIBPKI=libmipki.so
  PIC=-fPIC -lpthread
  WINSOCK=
  LD_LIBRARY_PATH := $(MITLS_HOME)/src/pki:$(MITLS_HOME)/src/tls/extract/Kremlin-Library:$(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

all: test

clean:
	rm -rf *.o *.exe *.dll *~

$(MITLS_HOME)/src/pki/$(LIBPKI):
	make -C ../../src/pki

$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS):
	make -j8 -C ../../src/tls -f Makefile.Kremlin build-library

copy: $(LIBMITLS) $(LIBPKI)

$(LIBMITLS): $(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	cp $(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS) .

$(LIBPKI): $(MITLS_HOME)/src/pki/$(LIBPKI)
	cp $(MITLS_HOME)/src/pki/$(LIBPKI) .
	cp $(MLCRYPTO_HOME)/openssl/$(OPENSSL) .

cmitls.exe: cmitls.c \
	$(MITLS_HOME)/src/pki/$(LIBPKI) \
	$(MITLS_HOME)/src/tls/extract/Kremlin-Library/$(LIBMITLS)
	$(CC) -I../../src/pki -I../../libs/ffi \
	  -L$(MITLS_HOME)/src/pki \
	  -L$(MITLS_HOME)/src/tls/extract/Kremlin-Library \
	  -L$(MLCRYPTO_HOME)/openssl \
	  -lmitls -lmipki $(PIC) cmitls.c -o cmitls.exe $(WINSOCK)

test: cmitls.exe
	./cmitls.exe google.com 443
	./cmitls.exe tls13.cloudflare.com 443
