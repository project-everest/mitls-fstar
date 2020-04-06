MITLS_HOME 	?= ../../../..
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
OPENSSL_HOME	?= $(MLCRYPTO_HOME)/openssl

LD_DIRS 	= \
  $(OPENSSL_HOME) \
  $(HACL_HOME)/dist/mitls \
  $(MITLS_HOME)/src/tls/dist/compact \
  $(MITLS_HOME)/src/pki \

ifeq ($(OS),Windows_NT)
  LD_DIRS := $(shell cygpath -u $(LD_DIRS))
endif

LD_LIBS = mitls mipki evercrypt crypto

NOOP=
SPACE=$(NOOP) $(NOOP)
LD_PATH=$(subst $(SPACE),:,$(LD_DIRS))

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  LD_EXTRA = DYLD_LIBRARY_PATH=$(LD_PATH):$$DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  LD_EXTRA = LD_LIBRARY_PATH=$(LD_PATH):$$LD_LIBRARY_PATH
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  LD_EXTRA = PATH=$(LD_PATH):$$PATH
endif

LDFLAGS 	+= $(addprefix -L,$(LD_DIRS)) $(addprefix -l,$(LD_LIBS)) \
  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

CFLAGS += -Wno-deprecated-declarations

include Makefile.basic

test.exe:
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

.PHONY: test
test: test.exe
	$(LD_EXTRA) ./$<
