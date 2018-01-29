UNAME		= $(shell uname)
MARCH		?= x86_64

ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(PATH)
  CC ?= x86_64-w64-mingw32-gcc
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(DYLD_LIBRARY_PATH)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
  export LD_LIBRARY_PATH
endif

INCLUDE_DIRS 	= secure kremlib include stub vale curve .

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
# then: remove Crypto_Symmetric_Bytes
FILES 		= Cert C_Loops_Spec_Loops CommonDH CoreCrypto \
  Crypto_AEAD_Crypto_Symmetric_Buffer_Utils_Crypto_Plain Crypto_Indexing \
  CryptoTypes curve/Curve25519 DHGroup ECGroup Extensions Flag Flags FStar \
  HaclProvider Hashing_Spec kremlib/kremdate kremlib/kremstr kremlinit \
  LowCProvider Nonce Parse PMS Prims PSK RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD stub/core_crypto stub/hacl_aead \
  stub/hacl_provider Test_Main TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags vale/sha256_main_i vale/vale_aes_glue vale/Vale_Hash_SHA2_256

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror -Wno-unused-variable -Wno-parentheses

all: test.exe

-include .depend

.depend:
	$(CC) $(CFLAGS) -MM $(addsuffix .c,$(FILES)) > $@

test.exe: $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -o $@ -lcrypto -lssl -L$(MLCRYPTO_HOME)/openssl

test: all
	./test.exe
