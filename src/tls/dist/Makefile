MITLS_HOME 	?= ../../../..
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
OPENSSL_HOME	?= $(MLCRYPTO_HOME)/openssl

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
endif

include Makefile.basic

CFLAGS		+= -g -std=gnu11 -O3
LDFLAGS		+= -L$(HACL_HOME)/dist/compact -levercrypt
LDFLAGS		+= -L$(MITLS_HOME)/src/pki -lmipki
LDFLAGS		+= -L$(OPENSSL_HOME) -lcrypto

KREMLIB_A 	= $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
EVERCRYPT_SO 	= $(HACL_HOME)/dist/compact/libevercrypt.$(SO)
MIPKI_SO	= $(MITLS_HOME)/src/pki/libmipki.$(SO)

$(KREMLIB_A) $(EVERCRYPT_SO) $(MIPKI_SO):
	@echo "Please run make in the $(dir $@) directory before invoking this Makefile" && false


all: libmitls.$(SO)

libmitls.$(SO): $(OBJS) $(KREMLIB_A) | $(EVERCRYPT_SO) $(MIPKI_SO)
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDFLAGS)

