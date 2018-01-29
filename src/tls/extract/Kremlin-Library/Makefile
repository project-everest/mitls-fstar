UNAME		= $(shell uname)
MARCH		?= x86_64

ifeq (,$(MLCRYPTO_HOME))
  $(error Please define MLCRYPTO_HOME)
endif

ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(DYLD_LIBRARY_PATH)
  SO = so
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  CFLAGS := -fPIC $(CFLAGS)
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
  SO = so
  export LD_LIBRARY_PATH
endif

INCLUDE_DIRS 	= secure kremlib include stub vale curve .

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
# then: remove Crypto_Symmetric_Bytes
FILES 		= AEAD_GCM AEADOpenssl AEADProvider Alert BufferBytes Cert \
  C_Loops_Spec_Loops CommonDH Connection Content CoreCrypto \
  Crypto_AEAD_Crypto_Symmetric_Buffer_Utils_Crypto_Plain Crypto_Indexing \
  CryptoTypes curve/Curve25519 DataStream DHGroup ECGroup Epochs Extensions FFI \
  FFICallbacks Flag Flags FStar HaclProvider Handshake HandshakeLog \
  HandshakeMessages Hashing Hashing_CRF Hashing_OpenSSL Hashing_Spec HKDF HMAC \
  HMAC_UFCMA KeySchedule kremlib/kremdate kremlib/kremstr kremlinit LHAEPlain \
  LowCProvider Negotiation Nonce Parse PMS Prims PSK QUIC Range Record RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD StAE StatefulLHAE \
  StatefulPlain StreamAE StreamDeltas StreamPlain stub/core_crypto stub/hacl_aead \
  stub/hacl_provider Test_CommonDH Test_Handshake Test_Main Test_StAE \
  Test_TLSConstants Ticket TLS TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags TLSPRF Transport vale/sha256_main_i vale/vale_aes_glue \
  vale/Vale_Hash_SHA2_256

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -g -fwrapv -fstack-check -D_BSD_SOURCE \
  -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO -I$(MLCRYPTO_HOME)/openssl/include

all: libmitls.$(SO)

-include .depend

.depend:
	$(CC) $(CFLAGS) -MM $(addsuffix .c,$(FILES)) > $@

libmitls.so: $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -shared -o $@ -lcrypto -lssl -L$(MLCRYPTO_HOME)/openssl

libmitls.dll: $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	echo "Not generating a DLL yet because too many unresolved symbols"

test:
