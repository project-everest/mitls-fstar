MITLS_HOME 	?= ../../../..
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
OPENSSL_HOME	?= $(MLCRYPTO_HOME)/openssl

# This Makefile is configured to build libmitls with heap regions. This entails:
# - passing RegionAllocator.c at link-time
# - defining USE_HEAP_REGIONS
# - linking against pthreads
# - ignoring clobbered variable by longjmp error messages.
# Once we are fully low-level and no longer rely on manual memory management,
# all of these should go.
#
# This Makefile is configured to build libmitls with custom logging. This
# entails:
# - adding -add-early-include '"log_to_choice.h"' to the kremlin invocation
# - ignoring function cast type errors
# - defining LOG_TO_CHOICE

LD_DIRS 	= \
  $(OPENSSL_HOME) \
  $(HACL_HOME)/dist/compact \
  $(MITLS_HOME)/src/pki \

LD_LIBS = evercrypt crypto mipki pthread

# This Makefile uses heap regions

NOOP=
SPACE=$(NOOP) $(NOOP)
LD_PATH=$(subst $(SPACE),:,$(LD_DIRS))

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
  HEAD		= ghead
  export DYLD_LIBRARY_PATH := $(LD_PATH):$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC -fstack-check
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all \
    -Xlinker --version-script -Xlinker libmitls_internal_script \
    -Wl,-z,defs
  HEAD		= head
  export LD_LIBRARY_PATH := $(LD_PATH):$(LD_LIBRARY_PATH)
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
  LDFLAGS	+= -Xlinker --version-script -Xlinker libmitls_internal_script -Wl,--out-implib,libmitls.dll.a
  HEAD		= head
  export PATH := $(LD_PATH):$(PATH)
endif

include Makefile.basic

CFLAGS		+= -g -std=gnu11 -O3 \
  -DUSE_HEAP_REGIONS -Wno-clobbered -Wno-cast-function-type \
  -DLOG_TO_CHOICE
LDFLAGS 	+= $(addprefix -L,$(LD_DIRS)) $(addprefix -l,$(LD_LIBS)) \

KREMLIB_A 	= $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
EVERCRYPT_SO 	= $(HACL_HOME)/dist/compact/libevercrypt.$(SO)
MIPKI_SO	= $(MITLS_HOME)/src/pki/libmipki.$(SO)

$(KREMLIB_A) $(EVERCRYPT_SO) $(MIPKI_SO):
	@echo "Please run make in the $(dir $@) directory before invoking this Makefile" && false


all: libmitls.$(SO)

libmitls_custom_script: libmitls_internal_script | libmitls.def
	$(HEAD) -n -1 $< > $@
	egrep '(__eq__|__neq__)' libmitls.def | sed 's/$$/;/g' >> $@
	echo '};' >> $@

libmitls.$(SO): libmitls_custom_script $(OBJS) $(KREMLIB_A) | $(EVERCRYPT_SO) $(MIPKI_SO)
	$(CC) $(CFLAGS) -shared -o $@ $(OBJS) $(LDFLAGS) $(KREMLIB_A)

