# Note: please backport any changes here to ../Kremlin-Library/Makefile
all: test.exe

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto
EVERCRYPT_HOME	?= ../../../../../hacl-star/providers

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
  endif
  LDOPTS := -lntdll -lbcrypt $(LDOPTS)
  PATH := $(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH := $(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  SO = so
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  LD_LIBRARY_PATH := $(EVERCRYPT_HOME)/out:$(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  LDOPTS := -lpthread $(LDOPTS)
  SO = so
  export LD_LIBRARY_PATH
endif

ifeq (,$(wildcard $(MITLS_HOME)/src/pki/libmipki.$(SO)))
  $(error MITLS_HOME is $(MITLS_HOME) and I cannot find $(MITLS_HOME)/src/pki/libmipki.$(SO) -- please run make in $(MITLS_HOME)/src/pki)
endif

ifneq (,$(EVEREST_WINDOWS))
CFLAGS+=-DKRML_NOUINT128 -DKRML_SEPARATE_UINT128 # -DKRML_NOSTRUCT_PASSING
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

INCLUDE_DIRS 	= secure kreminc include stub vale curve pki ffi uint128 .

# Note: see comment in Makefile.Kremlin to see why we're re-extracting
# Crypto.Symmetric.Bytes rather than using the one from secure/

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
# then: remove Crypto_AEAD_Main because of the hacl_provider hack
FILES 		= Cert C_Loops_Spec_Loops CommonDH CoreCrypto \
  Crypto_Indexing Crypto_Symmetric_Bytes Crypto_Plain \
  CryptoTypes curve/Hacl_Curve25519 DHGroup ECGroup Extensions Flag Flags FStar \
  HaclProvider Hashing_Spec kremlib/kremdate kremlib/kremstr kremlinit \
  LowCProvider Nonce Parse PMS Prims PSK RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  Specializations_Providers_AEAD stub/mipki_wrapper stub/core_crypto stub/hacl_aead \
  stub/hacl_provider stub/buffer_bytes Test_Main TLSConstants TLS_Curve25519 TLSError TLSInfo \
  TLSInfoFlags vale/sha256_main_i vale/vale_aes_glue vale/Vale_Hash_SHA2_256 \
  stub/RegionAllocator

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces

LDOPTS += -L$(EVERCRYPT_HOME)/out -levercrypt

ifneq (,$(EVEREST_WINDOWS))
FILES+=uint128/FStar_UInt128
endif

ifndef NO_OPENSSL
CFLAGS += -I$(MLCRYPTO_HOME)/openssl/include
LDOPTS += -L$(MLCRYPTO_HOME)/openssl -lcrypto -lssl
else
CFLAGS += -DNO_OPENSSL
endif

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

test.exe: $(addsuffix .o,$(FILES)) vale/sha256-$(MARCH)$(VARIANT).o vale/aesgcm-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o
	$(CC) $^ -o $@ -lmipki $(LDOPTS) -L$(MITLS_HOME)/src/pki

CERT_FILES=CAFile.pem server-ecdsa.crt server-ecdsa.key

$(CERT_FILES):
	cp $(MITLS_HOME)/data/$@ .

clean:
	rm -fr $(addsuffix .o,$(FILES)) $(addsuffix .c,$(FILES)) test.exe
	rm -fr vale/sha256-$(MARCH)$(VARIANT).o vale/aesgcm-$(MARCH)$(VARIANT).o vale/aes-$(MARCH)$(VARIANT).o

test: test.exe $(CERT_FILES)
	./$<
