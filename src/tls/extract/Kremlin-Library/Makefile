# Note: please backport any changes here to ../Kremlin-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	?= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto

ifeq ($(OS),Windows_NT)
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH :=$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  SO = so
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  CFLAGS := -fPIC $(CFLAGS)
  LD_LIBRARY_PATH :=  $(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  LDOPTS := -lpthread $(LDOPTS)
  SO = so
  export LD_LIBRARY_PATH
endif

ifdef HAVE_OPENSSL
ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(PATH)
else
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
endif
endif

ifeq (,$(wildcard $(MITLS_HOME)/src/pki/libmipki.$(SO)))
  $(error MITLS_HOME is $(MITLS_HOME) and I cannot find $(MITLS_HOME)/src/pki/libmipki.$(SO) -- please run make in $(MITLS_HOME)/src/pki)
endif

INCLUDE_DIRS 	= secure kremlib include stub vale curve ffi pki .

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
# then: remove Crypto_Symmetric_Bytes
# then: remove AEADOpenssl because no other modules refer to it
# thanks to inlining and partial evaluation.
# (except AEADProvider, which refers to AEADOpenssl_state in AEADOpenssl.h)
FILES 		= AEAD_GCM AEADProvider Alert BufferBytes Cert \
  C_Loops_Spec_Loops CommonDH Connection Content CoreCrypto \
  Crypto_AEAD_Crypto_Symmetric_Buffer_Utils_Crypto_Plain Crypto_Indexing \
  CryptoTypes curve/Curve25519 DataStream DHGroup ECGroup Epochs Extensions FFI \
  FFICallbacks Flag Flags FStar HaclProvider Handshake HandshakeLog \
  HandshakeMessages Hashing Hashing_CRF Hashing_OpenSSL Hashing_Spec HKDF HMAC \
  HMAC_UFCMA KeySchedule kremlib/kremdate kremlib/kremstr kremlinit LHAEPlain \
  LowCProvider Negotiation Nonce Parse PMS Prims PSK QUIC Range Record RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD StAE StatefulLHAE \
  StatefulPlain StreamAE StreamDeltas StreamPlain stub/mipki_wrapper stub/core_crypto stub/hacl_aead \
  stub/hacl_provider \
  Ticket TLS TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags TLSPRF Transport vale/sha256_main_i vale/vale_aes_glue \
  vale/Vale_Hash_SHA2_256 # stub/mitlsffi

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces

ifdef HAVE_OPENSSL
CFLAGS += -I$(MLCRYPTO_HOME)/openssl/include -DHAVE_OPENSSL
LDOPTS += -L$(MLCRYPTO_HOME)/openssl -lcrypto -lssl
endif

all: libmitls.$(SO)

-include .depend

.depend:
	$(CC) $(CFLAGS) -MM $(addsuffix .c,$(FILES)) > $@

libmitls.$(SO): $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -shared -o $@ -lmipki $(LDOPTS) -L$(MITLS_HOME)/src/pki

test:
