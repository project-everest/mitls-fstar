# Note: please backport any changes here to ../Kremlin-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto

ifeq ($(OS),Windows_NT)
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  CFLAGS := -pthread $(CFLAGS) -include log_to_choice.h
  LDOPTS := -lntdll $(LDOPTS)
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
  LDOPTS := -lpthread -Xlinker -z -Xlinker noexecstack -Xlinker --version-script -Xlinker $(MITLS_HOME)/src/tls/libmitls_version_script $(LDOPTS)
  SO = so
  export LD_LIBRARY_PATH
endif

ifndef NO_OPENSSL
ifeq ($(OS),Windows_NT)
  PATH := $(MLCRYPTO_HOME)/openssl:$(PATH)
else ifeq ($(UNAME),Darwin)
  DYLD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(DYLD_LIBRARY_PATH)
else
  LD_LIBRARY_PATH := $(MLCRYPTO_HOME)/openssl:$(LD_LIBRARY_PATH)
endif
endif

INCLUDE_DIRS 	= secure kremlib include stub vale curve ffi uint128 .

# Note: see comment in Makefile.Kremlin to see why we're re-extracting
# Crypto.Symmetric.Bytes rather than using the one from secure/

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
# then: remove AEADOpenssl because no other modules refer to it
# thanks to inlining and partial evaluation.
# (except AEADProvider, which refers to AEADOpenssl_state in AEADOpenssl.h)
# ADL: Do not include Test_* modules in this library please
FILES 		= AEAD_GCM AEADProvider Alert BufferBytes Cert \
  C_Loops_Spec_Loops CommonDH Connection Content CoreCrypto \
  Crypto_Indexing Crypto_Symmetric_Bytes Crypto_Plain \
  CryptoTypes curve/Curve25519 DataStream DHGroup ECGroup Epochs Extensions FFI \
  FFICallbacks Flag Flags FStar HaclProvider Handshake HandshakeLog \
  HandshakeMessages Hashing Hashing_CRF Hashing_OpenSSL Hashing_Spec HKDF HMAC \
  HMAC_UFCMA KeySchedule kremlib/kremdate kremlib/kremstr kremlinit LHAEPlain \
  LowCProvider Negotiation Nonce Parse PMS Prims PSK QUIC Range Record RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD StAE StatefulLHAE \
  StatefulPlain StreamAE StreamDeltas StreamPlain stub/core_crypto stub/hacl_aead \
  stub/hacl_provider Ticket TLS TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags TLSPRF Transport vale/sha256_main_i vale/vale_aes_glue \
  vale/Vale_Hash_SHA2_256 stub/mitlsffi stub/buffer_bytes uint128/uint128_wrapper \
  stub/RegionAllocator

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces

ifndef NO_OPENSSL
CFLAGS += -I$(MLCRYPTO_HOME)/openssl/include
LDOPTS += -L$(MLCRYPTO_HOME)/openssl -lcrypto
else
CFLAGS += -DNO_OPENSSL
endif

all: libmitls.$(SO)

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

libmitls.$(SO): $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -shared -o $@ $(LDOPTS)

clean:
	rm -fr *.c *.o *.dll *.so *.a *.h *~

test:
