# Note: please backport any changes here to ../Kremlin-Library/Makefile
all: test.exe

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
KREMLIN_HOME    ?= ../../../../../kremlin
MLCRYPTO_HOME	?= ../../../../../MLCrypto
EVERCRYPT_HOME	?= ../../../../../hacl-star/providers

LDOPTS += -L$(EVERCRYPT_HOME)/out -levercrypt

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
  endif
  LDOPTS += -lntdll -lbcrypt
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
  LDOPTS += -lpthread
  SO = so
  export LD_LIBRARY_PATH
endif

ifeq (,$(wildcard $(MITLS_HOME)/src/pki/libmipki.$(SO)))
  $(error MITLS_HOME is $(MITLS_HOME) and I cannot find $(MITLS_HOME)/src/pki/libmipki.$(SO) -- please run make in $(MITLS_HOME)/src/pki)
endif

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

INCLUDE_DIRS 	= secure kreminc include stub pki ffi uint128 .

# Note: see comment in Makefile.Kremlin to see why we're re-extracting
# Crypto.Symmetric.Bytes rather than using the one from secure/

# ls *.c */*.c | sed 's/\.c//g' >> Makefile
FILES 		= Cert C_Loops_Spec_Loops CommonDH CoreCrypto \
  secure/Crypto_AEAD_Main \
  Crypto_Indexing Crypto_Symmetric_Bytes Crypto_Plain \
  CryptoTypes DHGroup ECGroup Extensions Flags Format FStar \
  Hashing_Spec Hashing HMAC HKDF kremlinit \
  LowParse Nonce Parse PMS Prims PSK Random RSAKey \
  secure/Crypto_HKDF_Crypto_HMAC \
  stub/mipki_wrapper stub/core_crypto \
  stub/buffer_bytes Test_Main TLSConstants \
  TLS_Curve25519 TLSError TLSInfo TLSInfoFlags \
  stub/RegionAllocator

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv -fstack-check \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces -Wno-error-tautological-compare -Wno-error-int-to-void-pointer-cast

LDOPTS += -L$(EVERCRYPT_HOME)/out -levercrypt

ifndef NO_OPENSSL
CFLAGS += -I$(MLCRYPTO_HOME)/openssl/include
LDOPTS += -L$(MLCRYPTO_HOME)/openssl -lcrypto
else
CFLAGS += -DNO_OPENSSL
endif

LDOPTS += -L$(MITLS_HOME)/src/pki -lmipki $(KREMLIN_HOME)/kremlib/out/libkremlib.a 

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

test.exe: $(addsuffix .o,$(FILES))
	$(CC) $^ -o $@ $(LDOPTS)

CERT_FILES=CAFile.pem server-ecdsa.crt server-ecdsa.key

$(CERT_FILES):
	cp $(MITLS_HOME)/data/$@ .

clean:
	rm -fr $(addsuffix .o,$(FILES)) $(addsuffix .c,$(FILES)) test.exe

test: test.exe $(CERT_FILES)
	./$<

.PHONY: test
