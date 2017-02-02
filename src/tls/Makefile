# These are all the known working targets in this file,
# Check for regressions & comment about them!
all: all-ver tls-sanity tls-lax tls-ffi

CONTRIB=ucontrib
LIB=ulib
FFI_HOME=../../libs/ffi
MARCH?=x86_64

clean:
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml clean MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/Platform/ml clean
	$(MAKE) -C $(FFI_HOME) clean
	rm -rf *.ml *.p.* *.cm* *.o *.a *.exe *~ *.out output
	rm -rf test/*.cm* test/*.o

# ------------------ Dependencies on F* & its libraries --------------
# Default F* location. 
FSTAR_HOME?=../../../FStar
# This location can easily be overridden by doing:
#   FSTAR_HOME=../../../fstar make mitls.exe
# BUT NOT AS FOLLOWS
#   make FSTAR_HOME=../../../fstar mitls.exe
# the latter form won't work because FSTAR_HOME will incorrectly override
# values in recursive invocations of $(MAKE)...

.PHONY: record_fstar_version
record_fstar_version:
	$(FSTAR_HOME)/bin/fstar.exe --version | grep ^commit | sed 's/commit=\([^ ]*\).*/\1/' > ../../.fstar_version

# .fst files in [ulib/ml] that are realized in fstarlib.cmxa
STDLIB_REALIZED=All List.Tot.Base List Heap Set Map ST HyperHeap HyperStack IO

OPTIONS=--fstar_home $(FSTAR_HOME)

CODEGEN_LIBS=CoreCrypto LowCProvider Platform Classical Seq HyperHeap HyperStack FFICallbacks

FSTARFLAGS=$(OPTIONS) $(OTHERFLAGS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

PLATFORM_REALIZED=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/
PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/
LLDIR=$(FSTAR_HOME)/examples/low-level
LDIR=$(LLDIR)/crypto
LCDIR=$(LLDIR)/LowCProvider

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

HINTS_ENABLED?=--use_hints
VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
  --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection \
  $(HINTS_ENABLED) --include $(LDIR)/hacl

# The .fst interfaces for the platform and crypto libraries.
LIBFILES=$(PLATFORM) $(CRYPTO) $(FFI_HOME)/FFICallbacks.fst

FSTAR_INCLUDE_PATHS=--include $(CDIR) --include $(PDIR) --include $(LDIR)/real --include $(LCDIR)/fst --include $(LDIR) --include $(FFI_HOME) --include $(FSTAR_HOME)/ulib/hyperstack

OCAMLOPTS=-package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread -w a+A-27
OCAML=ocamlfind ocamlopt
OCAMLMKLIB=ocamlfind mklib
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/$(LIB)/ml/extracted $(FSTAR_HOME)/$(LIB)/ml/hyperstack $(FSTAR_HOME)/$(LIB)/ml $(FSTAR_HOME)/$(CONTRIB)/Platform/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/db $(LCDIR) ../../libs/ml $(FFI_HOME))

# Since quite a few people forget to set that in their path... eventually,
# everyone should have it in their ~/.bashrc
ifeq ($(OS),Windows_NT)
  EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
endif

# ---------------------------------------------------------------------
# These files are all extracted via lax type-checking in mitls.cmxa
# Files are listed in dependency order

FSTS=Flags.fst \
MonotoneMap.fst \
TLSError.fst \
TLSConstants.fst \
Transport.fst \
Nonce.fst \
RSAKey.fst \
DHGroup.fst \
ECGroup.fst \
CommonDH.fst \
PMS.fst \
Hashing.fst \
HashMAC.fst \
Cert.fst \
Signature.fst \
PSK.fst \
TLSInfo.fst \
IdNonce.fst \
TLSExtensions.fst \
Buffer.Utils.fst \
Crypto.Symmetric.Bytes.fst \
Crypto.Config.fst \
Crypto.Indexing.fst \
Flag.fst \
Spartan.fst \
Crypto.Symmetric.AES.fst \
Crypto.Symmetric.AES128.fst \
Crypto.Symmetric.Chacha20.fst \
Crypto.Symmetric.Cipher.fst \
Crypto.Symmetric.Poly1305.Bigint.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5.fst \
Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6.fst \
Crypto.Symmetric.Poly1305.Bignum.fst \
Crypto.Symmetric.Poly1305.Spec.fst \
Crypto.Symmetric.Poly1305.fst \
Crypto.Symmetric.GF128.Spec.fst \
Crypto.Symmetric.GF128.fst \
Crypto.Symmetric.MAC.fst \
Crypto.Symmetric.UF1CMA.fst \
Crypto.Plain.fst \
Crypto.Symmetric.PRF.fst \
Crypto.AEAD.Encoding.fst \
Crypto.AEAD.Invariant.fst \
Crypto.AEAD.Wrappers.PRF.fst \
Crypto.AEAD.EnxorDexor.fst \
Crypto.AEAD.Wrappers.Encoding.fst \
Crypto.AEAD.Wrappers.CMA.fst \
Crypto.AEAD.fst \
Crypto.AEAD.Encrypt.fst \
Crypto.AEAD.Decrypt.fst \
AEADOpenssl.fst \
AEADProvider.fst \
Range.fst \
DataStream.fst \
Alert.fst \
Content.fst \
StreamPlain.fst \
StatefulPlain.fst \
LHAEPlain.fst \
StreamAE.fst \
AEAD_GCM.fst \
MAC.fst \
Encode.fst \
StatefulLHAE.fst \
ENC.fst \
HandshakeMessages.fst \
StAE.fst \
StreamDeltas.fst \
Record.fst \
HKDF.fst \
TLSPRF.fst \
MasterSecret.fst \
HandshakeLog.fst \
Negotiation.fst \
Epochs.fst \
KeySchedule.fst \
Handshake.fst \
Connection.fst \
ConnInvariant.fst \
TLS.fst \
FFI.fst \
test/TestRecord.fst \
test/TestDH.fst \
test/TestGCM.fst \
test/TestHandshake.fst \
test/TestFFI.fst \
test/TestAPI.fst #the preceding space is significant!

# --------------------------------------------------------------------
# Modules verified in tls-ver -- any time one more file verifies, it
# should be added here.
#
# Missing modules from FSTS:
# TLSExtensions, Encode, ENC, HandshakeMessages,
# TLSPRF, PRF, HandshakeLog, KeySchedule, Handshake

#17-02-02 removed Flags from the list as it was causing an fstar error. TODO
# Flags

# temporary removals

VERIFY= \
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
HashMAC \
Cert \
Signature \
TLSInfo \
IdNonce \
TLSExtensions \
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
MAC_SHA256 \
MAC_SHA1 \
StAE \
KeySchedule \
StreamDeltas \
HKDF \
Epochs \
Connection \
ConnInvariant \
FFI \
TLS

depend:
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make TLS.fst > .depend

#include .depend

all-ver: record_fstar_version $(addsuffix .fst-ver, $(VERIFY))

# Lax-checking one file at a time
%.fst-lax: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Verifying one file at a time
%.fst-ver: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fsti

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@))

%.fsti-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(addsuffix .fst,$(VERIFY))

# Sanity check
tls-sanity: record_fstar_version $(LIBFILES) $(FSTS) test/False.fst
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
        --verify_module False \
	$(FSTS) test/False.fst | tail -n 1 | grep -c "Error: 1 errors were reported (see above)"

# Lax typecheck all files (with ideal flag off)
tls-lax: record_fstar_version $(LIBFILES)
	$(FSTAR) --lax \
	--include $(LDIR)/spartan \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	$(FSTS)

wc:
	wc -l $(LIBFILES) $(FSTS)

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib has the entire F* standard library.
# Warning: remember that ORDER MATTERS for the GNU linker which discards unused
# symbols... this is why libllcrypto comes AFTER lowc_stub
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib.cmxa \
  $(LCDIR)/lowc_stub.o \
  $(LCDIR)/libllcrypto.a \
  $(LCDIR)/LowCProvider.cmx \
  $(FFI_HOME)/FFICallbacks.cmxa

# .fst files realized elsewhere.
TLSGEN_REALIZED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_REALIZED) SessionDB DB DHDB CoreCrypto LowCProvider FFICallbacks)

OUTPUT_DIR?=output

# All our extracted modules.
TLSML := $(subst .,_,$(FSTS))
TLSML := $(subst _fst,.ml,$(TLSML))
TLSML := $(subst Handshake.fsti, , $(TLSML))
TLSML := $(subst StAE.fsti, , $(TLSML))
# F* does not provide an implementation for these in fstarlib.cmxa, so add them
# to our own list.
TLSML := \
  FStar_Ghost.ml FStar_Seq_Base.ml \
  FStar_List_Tot_Properties.ml FStar_List_Tot.ml FStar_BitVector.ml FStar_UInt.ml \
  FStar_Seq_Properties.ml FStar_Seq.ml FStar_Monotonic_RRef.ml \
  FStar_Monotonic_Seq.ml \
  $(TLSML)
# Last step: prefix with the output directory.
TLSML := $(addprefix $(OUTPUT_DIR)/,$(notdir $(TLSML)))
TLSML := $(TLSML) $(FFI_HOME)/FFIRegister.ml

# Note to self: there is little point in breaking down this rule into more
# atomic ones. One may hope that we can only rebuild the .ml files that have
# changed; however, extraction is a global operation that touches every .ml
# file; as make is only aware of mtimes (and not hashsums), we would rebuild
# every single .ml file anyway...

mitls.cmxa: record_fstar_version $(LIBFILES)
	mkdir -p $(OUTPUT_DIR)
	# Build $(FFI_HOME)/FFICallbacks.cmxa
	$(MAKE) -C $(FFI_HOME)
	$(FSTAR) --include $(LDIR)/spartan \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions \
	  --__temp_no_proj FStar.Heap --odir $(OUTPUT_DIR) $(TLSGEN_REALIZED) \
	  $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	  $(FSTAR_INCLUDE_PATHS) \
	  --include concrete-flags \
	  $(FSTS)
	# Note (JP): the Makefile seems incorrect and we need to run make clean
	# first
	# Make OCaml version of F* libs. 
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml clean
	# Builds everything against prims, setting MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml MEM=HST
	# Recursively builds everything in platform, etc.
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml
	# Low-level C record stack
	$(MAKE) -C $(LCDIR)
	# # All our .cmx files
	$(OCAML) $(OCAMLOPTS) -w -a $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) -c $(TLSML)
	# A .cmxa with all the .cmx above
	$(OCAML) -a $(OCAML_INCLUDE_PATHS) $(TLSML:.ml=.cmx) -I $(OUTPUT_DIR) -o mitls.cmxa

#16-10-19 beware: failing tests in mitls.cmxa will leave mitls.exe unchanged.
mitls.exe:  mitls.cmxa 
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -g mitls.cmxa \
		-I test/ -I output/ test/mitls.ml -o mitls.exe

test.out: mitls.cmxa 
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) $(LIB_ML) mitls.cmxa -I test/ test/parsing_test.ml test/test_hkdf.ml test/test_main.ml -o test.out

.PHONY: test
test: test.out mitls.exe
	# Unit tests from test/test_main.ml
	$(EXTRA_PATH) ./test.out
	# Run mitls.exe 1.2
	./mitls.exe www.google.com 443 -v 1.2
	# Run mitls.exe 1.3. Broken right now. 
	# mitls-fstar/src/tls/mitls.exe tls13.crypto.mozilla.org 443

# Depends on mitls.cmxa
rpc.ml:
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions \
	  --__temp_no_proj FStar.Heap --odir $(OUTPUT_DIR) $(TLSGEN_REALIZED) \
	  $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	  $(FSTAR_INCLUDE_PATHS) \
	  test/Formatting.fst test/RPC.fst

rpc.exe:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
		-I output/ output/Formatting.ml output/RPC.ml test/rpc_test.ml -o rpc.exe

# FFI support - calling from C into miTLS. TODO: remove duplication somehow
ifeq ($(OS),Windows_NT)
tls-ffi: mitls.cmxa
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -output-obj -g mitls.cmxa -o libmitls.dll
else
UNAME_S = $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
tls-ffi: mitls.cmxa
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -ccopt -dynamiclib -ccopt -lasmrun -g mitls.cmxa -o libmitls.dylib
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -output-obj -ccopt -bundle -g mitls.cmxa -o libmitls.so
else
tls-ffi: mitls.cmxa
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -output-obj -g mitls.cmxa -o libmitls.so
endif
endif
