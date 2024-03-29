# Note: please backport any changes here to ../Karamel-Library/Makefile
all: test.exe

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
KRML_HOME    ?= ../../../../../karamel
MLCRYPTO_HOME	?= ../../../../../MLCrypto
EVERCRYPT_HOME	?= ../../../../../hacl-star/providers

LDOPTS += -levercrypt
LDOPTS += -L$(EVERCRYPT_HOME)/../dist/gcc-compatible
LDOPTS += -L$(KRML_HOME)/krmllib/dist/generic -lkrmllib

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    MLCRYPTO_HOME := $(shell cygpath -u ${MLCRYPTO_HOME})
  endif
  LDOPTS += -lntdll -lbcrypt
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  ASMS=$(wildcard stub/*-mingw.S)
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH := $(EVERCRYPT_HOME)/../dist/gcc-compatible:$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  SO = so
  ASMS=$(wildcard stub/*-darwin.S)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  LD_LIBRARY_PATH := $(EVERCRYPT_HOME)/../dist/gcc-compatible:$(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  LDOPTS += -lpthread
  SO = so
  ASMS=$(wildcard stub/*-linux.S)
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

INCLUDE_DIRS 	= $(KRML_HOME)/krmllib/dist/minimal $(KRML_HOME)/include $(HACL_HOME)/dist/gcc-compatible/clients include stub pki ffi .

# Note: see comment in Makefile.Karamel to see why we're re-extracting
# Crypto.Symmetric.Bytes rather than using the one from secure/

FILES = $(patsubst %.c,%,$(wildcard *.c)) \
  stub/mipki_wrapper stub/buffer_bytes stub/RegionAllocator stub/evercrypt_openssl stub/evercrypt_vale_stubs \
  stub/Hacl_AES $(patsubst %.S,%,$(ASMS))

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror -Wno-deprecated-declarations \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv  \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE -D__USE_MINGW_ANSI_STDIO \
  -Wno-missing-braces -Wno-error-tautological-compare -Wno-error-int-to-void-pointer-cast

LDOPTS += -L$(EVERCRYPT_HOME)/out -levercrypt

ifndef NO_OPENSSL
CFLAGS += -I$(MLCRYPTO_HOME)/openssl/include
LDOPTS += -L$(MLCRYPTO_HOME)/openssl -lcrypto
else
CFLAGS += -DNO_OPENSSL
endif

LDOPTS += -L$(MITLS_HOME)/src/pki -lmipki $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(FILES))

test.exe: $(addsuffix .o,$(FILES))
	rm -rf $(EVERCRYPT_HOME)/../dist/gcc-compatible/*.dll.a # newer dynamic link is not properly setup on mitls/master ... persist with static linking
	$(CC) $^ -o $@ $(LDOPTS)

CERT_FILES=CAFile.pem server-ecdsa.crt server-ecdsa.key

$(CERT_FILES):
	cp $(MITLS_HOME)/data/$@ .

clean:
	rm -fr $(addsuffix .o,$(FILES)) $(addsuffix .c,$(FILES)) test.exe

test: test.exe $(CERT_FILES)
	./$<

.PHONY: test
