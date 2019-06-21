MITLS_HOME 	?= ../../../..
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
OPENSSL_HOME	?= $(MLCRYPTO_HOME)/openssl

LD_DIRS 	= \
  $(OPENSSL_HOME) \
  $(HACL_HOME)/dist/compact \
  $(MITLS_HOME)/src/tls/dist/compact \
  $(MITLS_HOME)/src/pki \

LD_LIBS = crypto evercrypt mitls mipki

NOOP=
SPACE=$(NOOP) $(NOOP)
LD_PATH=$(subst $(SPACE),:,$(LD_DIRS))

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  export DYLD_LIBRARY_PATH := $(LD_PATH):$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  export LD_LIBRARY_PATH := $(LD_PATH):$(LD_LIBRARY_PATH)
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  export PATH := $(LD_PATH):$(PATH)
endif

LDFLAGS 	+= $(addprefix -L,$(LD_DIRS)) $(addprefix -l,$(LD_LIBS)) \
  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

include Makefile.basic

test.exe:
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

test: test.exe
	$(LD_EXTRA) ./$<
