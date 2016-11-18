# These are all the known working targets in this file,
# Check for regressions & comment about them!
all: all-ver tls-sanity tls-lax tls-ffi

CONTRIB=ucontrib
LIB=ulib
FFI_HOME=../../libs/ffi

clean:
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml clean MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/Platform/ml clean
	$(MAKE) -C $(FFI_HOME) clean
	rm -rf *.ml *.p.* *.cm* *.o *.a *.exe *~ *.out output
	rm -rf test/*.cm* test/*.o

# ------------------ Dependencies on F* & its libraries --------------
# When using NuBuild, FStar must be located within the source tree.
# Now that soft links are available on all platforms, I don't see a
# reason not to assume a fixed location.
FSTAR_HOME?=../../.fstar
# This location can easily be overridden by doing:
#   FSTAR_HOME=../../../fstar make tls-gen
# BUT NOT AS FOLLOWS
#   make FSTAR_HOME=../../../fstar tls-gen
# the latter form won't work because FSTAR_HOME will incorrectly override
# values in recursive invocations of $(MAKE)...

# .fst files in [ulib/ml] that are realized in fstarlib.cmxa
STDLIB_REALIZED=All List Heap Set Map ST HyperHeap HyperStack IO

OPTIONS=--fstar_home $(FSTAR_HOME)

CODEGEN_LIBS=CoreCrypto LowCProvider Platform Classical SeqProperties HyperHeap HyperStack FFICallbacks

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
VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20 --__temp_no_proj Handshake --__temp_no_proj Connection $(HINTS_ENABLED)

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
  EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
endif

# ----------------------- NuBuild integration -------------------------
NUBUILD_HOME=../../.nubuild
NUBUILD=$(NUBUILD_HOME)/bin/NuBuild.exe
ifdef USE_NUBUILD
FSTAR_OR_NUBUILD=$(NUBUILD) $(NUBUILDFLAGS) FStarVerify $(FSTARFLAGS)
else
FSTAR_OR_NUBUILD=$(FSTAR)
endif

# ---------------------------------------------------------------------
# These files are all extracted via lax type-checking in tls-gen
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
Crypto.AEAD.Lemmas.fst \
Crypto.AEAD.Lemmas.Part2.fst \
Crypto.AEAD.Lemmas.Part3.fst \
Crypto.AEAD.Wrappers.fst \
Crypto.AEAD.fst \
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
Hashing \
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

all-ver: $(addsuffix .fst-ver, $(VERIFY))

# Lax-checking one file at a time
%.fst-lax: $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Verifying one file at a time
%.fst-ver: $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver: $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
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
tls-sanity: $(LIBFILES) $(FSTS) test/False.fst
	$(MAKE) refresh
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
        --verify_module False \
	$(FSTS) test/False.fst | tail -n 1 | grep -c "Error: 1 errors were reported (see above)"

# Lax typecheck all files (with ideal flag off)
tls-lax: $(LIBFILES)
	$(MAKE) refresh
	$(FSTAR) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	$(FSTS)

wc:
	wc -l $(LIBFILES) $(FSTS)

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib has the entire F* standard library.
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib.cmxa \
  $(LCDIR)/LowCProvider.cmxa \
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
  FStar_List_Tot.ml FStar_Ghost.ml FStar_Seq.ml FStar_UInt.ml \
  FStar_BitVector.ml FStar_SeqProperties.ml FStar_Monotonic_RRef.ml \
  FStar_Monotonic_Seq.ml \
  $(TLSML)
# Last step: prefix with the output directory.
TLSML := $(addprefix $(OUTPUT_DIR)/,$(notdir $(TLSML)))
TLSML := $(TLSML) $(FFI_HOME)/FFIRegister.ml

refresh:
	$(FSTAR_HOME)/src/tools/rebuild_fstar_if $(FSTAR_HOME)

# Note to self: there is little point in breaking down this rule into more
# atomic ones. One may hope that we can only rebuild the .ml files that have
# changed; however, extraction is a global operation that touches every .ml
# file; as make is only aware of mtimes (and not hashsums), we would rebuild
# every single .ml file anyway...

tls-gen: $(LIBFILES)
	$(MAKE) refresh
	mkdir -p $(OUTPUT_DIR)
	# Build $(FFI_HOME)/FFICallbacks.cmxa
	$(MAKE) -C $(FFI_HOME)
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions \
	  --__temp_no_proj FStar.Heap --odir $(OUTPUT_DIR) $(TLSGEN_REALIZED) \
	  $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	  $(FSTAR_INCLUDE_PATHS) \
	  --include concrete-flags \
	  $(FSTS)
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
	# Then our test executable
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) $(LIB_ML) mitls.cmxa \
	         -I test/ test/parsing_test.ml test/test_hkdf.ml test/test_main.ml -o test.out
	# Run the tests
	$(EXTRA_PATH) ./test.out

#16-10-19 beware: failing tests in tls-gen will leave mitls.exe unchanged.
mitls.exe: tls-gen
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
		-I test/ -I output/ test/mitls.ml -o mitls.exe

# Depends on tls-gen
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
tls-ffi: tls-gen
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -output-obj -g mitls.cmxa -o libmitls.dll
else
UNAME_S = $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
tls-ffi: tls-gen
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -ccopt -dynamiclib -ccopt -lasmrun -g mitls.cmxa -o libmitls.dylib
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -output-obj -ccopt -bundle -g mitls.cmxa -o libmitls.so
else
tls-ffi: tls-gen
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) -linkall -runtime-variant _pic -output-obj -g mitls.cmxa -o libmitls.so
endif
endif
