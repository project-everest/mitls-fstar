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
	rm -rf IdealFlags.fst *.ml *.p.* *.cm* *.o *.a *.exe *~ *.out output
	rm -rf ideal-flags concrete-flags
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

CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap HyperStack FFICallbacks

FSTARFLAGS=$(OPTIONS) $(OTHERFLAGS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

PLATFORM_REALIZED=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/
PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

HINTS_ENABLED?=--use_hints
VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20 --__temp_no_proj Handshake --__temp_no_proj Connection $(HINTS_ENABLED)

# The .fst interfaces for the platform and crypto libraries.
LIBFILES=$(PLATFORM) $(CRYPTO) $(FFI_HOME)/FFICallbacks.fst

FSTAR_INCLUDE_PATHS=--include $(CDIR) --include $(PDIR) --include $(FFI_HOME) --include $(FSTAR_HOME)/ulib/hyperstack

OCAMLOPTS=-package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread -w a+A-27
OCAML=ocamlfind ocamlopt
OCAMLMKLIB=ocamlfind mklib
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/$(LIB)/ml/extracted $(FSTAR_HOME)/$(LIB)/ml/hyperstack $(FSTAR_HOME)/$(LIB)/ml $(FSTAR_HOME)/$(CONTRIB)/Platform/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/db ../../libs/ml $(FFI_HOME))

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

FSTS=IdealFlags.fst \
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
Range.fst \
DataStream.fst \
Alert.fst \
Content.fst \
StreamPlain.fst \
StreamAE.fst \
MasterSecret.fst \
StatefulPlain.fst \
LHAEPlain.fst \
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

CONCRETE_FSTS=$(subst IdealFlags.fst, concrete-flags/IdealFlags.fst, $(FSTS))
IDEAL_FSTS=$(subst IdealFlags.fst, ideal-flags/IdealFlags.fst, $(FSTS))

# --------------------------------------------------------------------
# Modules verified in tls-ver -- any time one more file verifies, it
# should be added here.
#
# Missing modules from FSTS:
# TLSExtensions, Encode, ENC, HandshakeMessages,
# TLSPRF, PRF, HandshakeLog, KeySchedule, Handshake

VERIFY= \
IdealFlags \
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

ConcreteFlags: Concrete.fst
	mkdir -p concrete-flags
	cp Concrete.fst concrete-flags/IdealFlags.fst

IdealFlags: Ideal.fst
	mkdir -p ideal-flags
	cp Ideal.fst ideal-flags/IdealFlags.fst

all-ver: IdealFlags $(addsuffix .fst-ver, $(subst IdealFlags, ideal-flags/IdealFlags, $(VERIFY)))

all-lax: ConcreteFlags $(addsuffix .fst-lax, $(basename $(CONCRETE_FSTS)))

# Lax-checking one file at a time
%.fst-lax: ConcreteFlags $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Verifying one file at a time
%.fst-ver: IdealFlags $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver: IdealFlags $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fsti

# Targets to get F* arguments in interactive mode
%.fst-in: IdealFlags
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@))

%.fsti-in: IdealFlags
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(addsuffix .fst,$(VERIFY))

# Sanity check
tls-sanity: IdealFlags $(LIBFILES) $(IDEAL_FSTS) test/False.fst
	$(MAKE) refresh
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ideal-flags \
        --verify_module False \
	$(IDEAL_FSTS) test/False.fst | tail -n 1 | grep -c "Error: 1 errors were reported (see above)"

# Lax typecheck all files (with ideal flag off)
tls-lax: $(LIBFILES) ConcreteFlags $(CONCRETE_FSTS)
	$(MAKE) refresh
	$(FSTAR) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include concrete-flags \
	$(CONCRETE_FSTS)

wc:
	wc -l $(LIBFILES) $(FSTS)

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib has the entire F* standard library.
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib.cmxa \
  $(FFI_HOME)/FFICallbacks.cmxa

# .fst files realized elsewhere.
TLSGEN_REALIZED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_REALIZED) SessionDB DB DHDB CoreCrypto FFICallbacks)

OUTPUT_DIR?=output

# All our extracted modules.
TLSML := $(FSTS:.fst=.ml)
TLSML := $(subst Handshake.fsti, , $(TLSML))
TLSML := $(subst StAE.fsti, , $(TLSML))
# F* does not provide an implementation for these in fstarlib.cmxa, so add them
# to our own list.
TLSML := \
  FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml FStar_Monotonic_RRef.ml \
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
tls-gen-deps: $(CONCRETE_FSTS)


tls-gen: $(LIBFILES) ConcreteFlags
	$(MAKE) tls-gen-deps
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
	  $(CONCRETE_FSTS)
	# Builds everything against prims, setting MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml MEM=HST
	# Recursively builds everything in platform, etc.
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml
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
