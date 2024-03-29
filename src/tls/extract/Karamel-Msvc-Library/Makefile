# Note: please backport any changes here to ../Karamel-Internal-Test/Makefile

UNAME		= $(shell uname)
MARCH		?= x86_64

MITLS_HOME 	= ../../../..
MLCRYPTO_HOME	?= ../../../../../MLCrypto
EVERCRYPT_HOME	?= ../../../../../hacl-star/providers
KRML_HOME    ?= ../../../../../karamel

LDOPTS += -levercrypt
LDOPTS += -L$(EVERCRYPT_HOME)/../dist/gcc-compatible
LDOPTS += -L$(KRML_HOME)/krmllib/dist/generic -lkrmllib

ifeq ($(OS),Windows_NT)
  PATH := $(MITLS_HOME)/src/pki:$(PATH)
  SO = dll
  CC ?= x86_64-w64-mingw32-gcc
  CFLAGS := -pthread $(CFLAGS) -include log_to_choice.h
  LDOPTS += -lntdll -lbcrypt
  ASMS=$(wildcard stub/*-mingw.S)
  export PATH
else ifeq ($(UNAME),Darwin)
  VARIANT = -Darwin
  DYLD_LIBRARY_PATH :=$(MITLS_HOME)/src/pki:$(DYLD_LIBRARY_PATH)
  SO = so
  ASMS=$(wildcard stub/*-darwin.S)
  export DYLD_LIBRARY_PATH
else ifeq ($(UNAME),Linux)
  VARIANT = -Linux
  CFLAGS := -fPIC $(CFLAGS)
  LD_LIBRARY_PATH :=  $(MITLS_HOME)/src/pki:$(LD_LIBRARY_PATH)
  LDOPTS := -lpthread -Xlinker -z -Xlinker noexecstack -Xlinker --version-script -Xlinker $(MITLS_HOME)/src/tls/libmitls_version_script -Wl,-z,defs $(LDOPTS)
  SO = so
  ASMS=$(wildcard stub/*-linux.S)
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

INCLUDE_DIRS 	= $(KRML_HOME)/krmllib/dist/minimal $(KRML_HOME)/include $(HACL_HOME)/dist/gcc-compatible/clients include stub ffi .

# we are now packaging most miTLS modules into meaningful C compilation units
# See src/tls/Makefile.Karamel for the list of bundles that are used
# All extracted C files should be part of the DLL
FILES = $(patsubst %.c,%,$(wildcard *.c)) \
  stub/mitlsffi stub/buffer_bytes stub/RegionAllocator stub/evercrypt_openssl stub/evercrypt_vale_stubs \
  stub/Hacl_AES $(patsubst %.S,%,$(ASMS))

CFLAGS := $(addprefix -I,$(INCLUDE_DIRS)) $(CFLAGS) -Wall -Werror -Wno-deprecated-declarations \
  -Wno-unused-variable -Wno-parentheses -Wno-unknown-warning-option \
  -Wno-unused-but-set-variable -Wno-infinite-recursion -g -fwrapv  \
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
	rm -rf $(EVERCRYPT_HOME)/../dist/gcc-compatible/*.dll.a # newer dynamic link is not properly setup on mitls/master ... persist with static linking
	$(CC) $^ -shared -o $@ $(LDOPTS) $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

clean:
	rm -fr $(addsuffix .o,$(FILES)) $(addsuffix .c,$(FILES)) libmitls.$(SO)
	rm -fr *.a *.h *.d *~

test:
