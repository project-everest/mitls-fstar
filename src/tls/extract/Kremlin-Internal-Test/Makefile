UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME ?= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto

ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(MITLS_HOME)/src/pki:$(PATH)
  CC ?= x86_64-w64-mingw32-gcc
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

INCLUDE_DIRS 	= $(MITLS_HOME)/src/pki $(MITLS_HOME)/libs/ffi secure kremlib include stub vale curve .

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
# then: remove Crypto_Symmetric_Bytes
FILES 		= Cert C_Loops_Spec_Loops CommonDH CoreCrypto \
  Crypto_AEAD_Crypto_Symmetric_Buffer_Utils_Crypto_Plain Crypto_Indexing \
  CryptoTypes curve/Curve25519 DHGroup ECGroup Extensions Flag Flags FStar \
  HaclProvider Hashing_Spec kremlib/kremdate kremlib/kremstr kremlinit \
  LowCProvider Nonce Parse PMS Prims PSK RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD stub/mipki stub/core_crypto stub/hacl_aead \
  stub/hacl_provider Test_Main TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags vale/sha256_main_i vale/vale_aes_glue vale/Vale_Hash_SHA2_256

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -I$(MLCRYPTO_HOME)/openssl/include -Wno-missing-braces

all: test.exe

-include .depend

.depend:
	$(CC) $(CFLAGS) -MM $(addsuffix .c,$(FILES)) > $@

test.exe: $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -o $@ -lcrypto -lssl -lmipki -L$(MLCRYPTO_HOME)/openssl -L$(MITLS_HOME)/src/pki

test: all
	./test.exe
