# Note: please backport any changes here to ../Kremlin-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto
EVERCRYPT_HOME	?= ../../../../../hacl-star/providers
KREMLIN_HOME    ?= ../../../../../kremlin

LDOPTS += -L$(EVERCRYPT_HOME)/out -levercrypt

ifeq ($(OS),Windows_NT)
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  CFLAGS := -pthread $(CFLAGS) -include log_to_choice.h
  LDOPTS += -lntdll -lbcrypt
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
  LDOPTS := -lpthread -Xlinker -z -Xlinker noexecstack -Xlinker --version-script -Xlinker $(MITLS_HOME)/src/tls/libmitls_version_script -Wl,-z,defs $(LDOPTS)
  SO = so
  export LD_LIBRARY_PATH
endif

# Force-include RegionAllocator.h and enable heap regions in all builds
CFLAGS := $(CFLAGS) -include RegionAllocator.h -DUSE_HEAP_REGIONS

ifneq (,$(EVEREST_WINDOWS))
CFLAGS+= # -DKRML_NOSTRUCT_PASSING
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

INCLUDE_DIRS 	= secure kreminc include stub ffi uint128 .

# Note: see comment in Makefile.Kremlin to see why we're re-extracting
# Crypto.Symmetric.Bytes rather than using the one from secure/

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove AEADOpenssl because no other modules refer to it
# thanks to inlining and partial evaluation.
# (except AEADProvider, which refers to AEADOpenssl_state in AEADOpenssl.h)
# ADL: Do not include Test_* modules in this library please
FILES = AEAD_GCM AEADProvider Alert BufferBytes Cert \
  C_Loops_Spec_Loops CommonDH Connection Content CoreCrypto \
  secure/Crypto_AEAD_Main \
  Crypto_Indexing Crypto_Symmetric_Bytes Crypto_Plain \
  CryptoTypes DataStream DHGroup ECGroup Old_Epochs Extensions FFI \
  FFICallbacks Flags Format FStar Old_Handshake HandshakeLog \
  HandshakeMessages Hashing Hashing_CRF Hashing_Spec HKDF HMAC \
  Old_HMAC_UFCMA Old_KeySchedule kremlinit LHAEPlain \
  LowParse Negotiation Nonce Parse PMS Prims \
  PSK QUIC Random Range Record RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  StAE StatefulLHAE \
  StatefulPlain StreamAE StreamDeltas StreamPlain stub/core_crypto \
  Ticket TLS TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags TLSPRF Transport stub/mitlsffi stub/buffer_bytes \
  stub/RegionAllocator

ifdef MITLS_USE_OPENSSL
FILES += AEADOpenssl
endif

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces -Wno-error-tautological-compare -Wno-error-int-to-void-pointer-cast \
  -Wno-error-enum-conversion

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

libmitls.$(SO): $(addsuffix .o,$(FILES))
	$(CC) $^ -shared -o $@ $(LDOPTS) $(KREMLIN_HOME)/kremlib/out/libkremlib.a

clean:
	rm -fr $(addsuffix .o,$(FILES)) $(addsuffix .c,$(FILES)) libmitls.$(SO)
	rm -fr *.a *.h *.d *~

test:
