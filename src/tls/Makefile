MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME ?= ../../../hacl-star
FFI_HOME ?= $(MITLS_HOME)/libs/ffi
MARCH ?= x86_64
ODIR ?= output
KRML_DIR ?= krml_output

FSTARFLAGS = --fstar_home $(FSTAR_HOME) $(OTHERFLAGS)
FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTARFLAGS)
KRML = $(KREMLIN_HOME)/krml

HINTS_ENABLED ?= --use_hints
VERFLAGS = --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection $(HINTS_ENABLED)

# These are all the known working targets in this file,
# Check for regressions & comment about them!

# NOTE: the sequence of subtargets in all, build and verify
# must be processed sequentially,
# but each subtarget alone can be built with parallelism enabled.
all:
	$(MAKE) build
	$(MAKE) verify

build:
	$(MAKE) mitls.exe
	$(MAKE) tls-ffi
	$(MAKE) cmitls.exe

verify:
	$(MAKE) all-ver
	$(MAKE) tls-sanity
	$(MAKE) tls-lax

clean:
	-rm -rf .depend* *.ml *.cm* *.o *.a *.exe *.lib *~ *.out $(ODIR) .fstarlib

record_fstar_version:
	$(FSTAR) --version | grep ^commit | sed 's/commit=\([^ ]*\).*/\1/' > $(MITLS_HOME)/.fstar_version

.PHONY: all build verify init depend clean record_fstar_version test

STDLIB_REALIZED=Pervasives Pervasives.Native Mul Float Char UInt Int8 UInt8 Int16 UInt16 Int32 UInt32 Int64 UInt64 UInt128 Int.Cast Int.Cast.Full BaseTypes IO Heap List.Tot.Base List Option String Set Buffer CommonST TSet Map HyperHeap HyperStack HyperStack.ST HyperStack.All ST All Monotonic.RRef Monotonic.Seq Monotonic.HyperHeap Monotonic.HyperStack Seq.Base Seq.Properties BitVector Math.Lib
CODEGEN_LIBS=Platform
# CoreCrypto LowCProvider Platform Classical Seq HyperHeap HyperStack FFICallbacks
PLATFORM_REALIZED=$(addprefix Platform., Date Error Tcp)
PDIR=$(FSTAR_HOME)/ucontrib/Platform/fst/
CDIR=$(FSTAR_HOME)/ucontrib/CoreCrypto/fst/
LLDIR=$(HACL_HOME)/secure_api
LCDIR=$(LLDIR)/LowCProvider

# Modules that are implemented in ML or C
NOEXTRACT=$(addprefix --no_extract ,Prims $(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_REALIZED) CoreCrypto DHDB LowCProvider FFICallbacks)

# Should unify this with kremlin stuff
RAW_HACL_INCLUDES=$(KREMLIN_HOME)/kremlib $(HACL_HOME)/specs $(HACL_HOME)/code/lib/kremlin $(HACL_HOME)/code/bignum $(HACL_HOME)/code/experimental/aesgcm $(HACL_HOME)/code/poly1305 $(HACL_HOME)/code/salsa-family $(LLDIR)/test $(LLDIR)/utils $(LLDIR)/vale $(LLDIR)/uf1cma $(LLDIR)/prf $(LLDIR)/aead
RAW_FSTAR_INCLUDE_PATHS=$(CDIR) $(PDIR) $(LCDIR)/fst $(RAW_HACL_INCLUDES) $(FFI_HOME)

HACL_INCLUDES=$(addprefix --include , $(RAW_HACL_INCLUDES))
FSTAR_INCLUDE_PATHS=$(addprefix --include , $(RAW_FSTAR_INCLUDE_PATHS))
KRML_INCLUDE_PATHS=$(addprefix -I ,$(RAW_FSTAR_INCLUDE_PATHS))

OCAMLPKG=-package batteries,stdint,fileutils,zarith,fstarlib
OCAMLPATH=$(FSTAR_HOME)/bin
OCAMLOPTS=$(OCAMLPKG) -thread -w -a
OCAML_PATHS=test $(ODIR) $(FSTAR_HOME)/ucontrib/Platform/ml $(FSTAR_HOME)/ucontrib/CoreCrypto/ml $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/db $(LCDIR) $(FFI_HOME)
OCAML_INCLUDE_PATHS=$(addprefix -I ,$(OCAML_PATHS))

# Since quite a few people forget to set that in their path... eventually,
# everyone should have it in their ~/.bashrc
ifeq ($(OS),Windows_NT)
  EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
endif

# --------------------------------------------------------------------
# Modules verified in tls-ver -- any time one more file verifies, it
# should be added here.

VERIFY= \
Flags \
MonotoneMap \
TLSError \
TLSConstants \
Transport \
Nonce \
RSAKey \
DHGroup \
ECGroup \
CommonDH \
PMS \
Hashing.Spec \
Hashing.OpenSSL \
Hashing \
Hashing.CRF \
HMAC \
Cert \
Signature \
TLSInfo \
IdNonce \
Extensions \
Range \
DataStream \
Alert \
Content \
StreamPlain \
StreamAE \
MasterSecret \
StatefulPlain \
LHAEPlain \
AEAD_GCM \
MAC \
StatefulLHAE \
Record \
StAE \
KeySchedule \
HandshakeLog \
Handshake \
StreamDeltas \
HKDF \
Epochs \
Connection \
ConnInvariant \
TLS \
FFI \
QUIC

# Lax-checking one file at a time
%.fst-lax:
	$(FSTAR) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/concrete-flags \
	$(basename $@).fst

# Verifying one file at a time
# @echo -e  "\e[1;34m"Verifying $(basename $(notdir $@)) "\e[0m";
%.fst-ver:
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver:
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fsti

# Targets to get F* arguments in interactive mode
%.fst-in:
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	--cache_checked_modules

%.fsti-in:
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@))

# These rules are silent to avoid disturbing .fst-in etc
.depend-TLS: # $(wildcard *.fst *.fsti)
	@-$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make FFI.fst QUIC.fst > .depend-TLS
.depend-HS: # $(wildcard *.fst *.fsti)
	@-$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make Handshake.fst > .depend-HS
.depend-AEAD: # $(wildcard $(HACL_HOME)/secure_api/*/*.fst)
	@-$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make $(LLDIR)/aead/Crypto.AEAD.Main.fst > .depend-AEAD
.depend-CDH:
	@-$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make CommonDH.fst > .depend-CDH

-include .depend-CDH
-include .depend-AEAD
-include .depend-HS
-include .depend-TLS

all-ver: record_fstar_version $(addsuffix .fst-ver, $(VERIFY))

# Sanity check
tls-sanity: record_fstar_version
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
        --verify_module False \
	$(FSTS) test/False.fst 2>&1 | tail -n 1 | grep -c '1 error was reported (see above)'

tls-lax: record_fstar_version
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax \
	--include $(MITLS_HOME)/src/tls/concrete-flags \
	TLS.fst

Curve25519.ml: record_fstar_version
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax \
	--include $(MITLS_HOME)/src/tls/concrete-flags \
	Curve25519.fst --codegen OCaml

wc:
	wc -l *.fst *.fsti

.fstarlib: $(FSTAR_HOME)/ulib/*.fst $(FSTAR_HOME)/ulib/ml/*.ml $(wildcard $(FSTAR_HOME)/ulib/ml/extracted/*.ml)
	touch .fstarlib
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml

mitls.cmxa: .fstarlib *.fst $(wildcard output/*.ml) $(wildcard output/*.cmx)
	$(MAKE) -f Extracted.mk mitls.cmxa

mitls.exe: mitls.cmxa
	$(MAKE) -f Extracted.mk mitls.exe

cmitls.o: cmitls.c
	$(MAKE) -f Extracted.mk cmitls.o
cmitls.exe: cmitls.o
	echo $(MAKECMDGOALS)
	$(MAKE) -f Extracted.mk $(MAKECMDGOALS)

kremlin:
	$(MAKE) -f Extracted.mk kremlin
test:
	$(MAKE) -f Extracted.mk test

# Some rules are only defined after extraction, and passed to the post-extraction Makefile (with ocamldep)
.DEFAULT:
	$(MAKE) -f Extracted.mk $(MAKECMDGOALS)
