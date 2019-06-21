MITLS_HOME 	?= ../../../..
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
OPENSSL_HOME	?= $(MLCRYPTO_HOME)/openssl

LD_DIRS 	= \
  $(OPENSSL_HOME) \
  $(HACL_HOME)/dist/compact \
  $(MITLS_HOME)/src/pki \

LD_LIBS = crypto evercrypt mipki

NOOP=
SPACE=$(NOOP) $(NOOP)
LD_PATH=$(subst $(SPACE),:,$(LD_DIRS))

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
  export DYLD_LIBRARY_PATH := $(LD_PATH):$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
  export LD_LIBRARY_PATH := $(LD_PATH):$(LD_LIBRARY_PATH)
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
  export PATH := $(LD_PATH):$(PATH)
endif

include Makefile.basic

CFLAGS		+= -g -std=gnu11 -O3
LDFLAGS 	+= $(addprefix -L,$(LD_DIRS)) $(addprefix -l,$(LD_LIBS)) \

KREMLIB_A 	= $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
EVERCRYPT_SO 	= $(HACL_HOME)/dist/compact/libevercrypt.$(SO)
MIPKI_SO	= $(MITLS_HOME)/src/pki/libmipki.$(SO)

$(KREMLIB_A) $(EVERCRYPT_SO) $(MIPKI_SO):
	@echo "Please run make in the $(dir $@) directory before invoking this Makefile" && false


all: libmitls.$(SO)

libmitls.$(SO): $(OBJS) $(KREMLIB_A) | $(EVERCRYPT_SO) $(MIPKI_SO)
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDFLAGS)

