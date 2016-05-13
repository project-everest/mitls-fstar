# These are all the known working targets in this file,
# check for regressions & comment about them!
all: tls-ver tls-sanity tls-lax tls-gen

# TODO extend scope of verification
# TODO compilation to ML & testing
# MK removed mitls-ml as strider was failing on it for ages

CONTRIB=ucontrib
LIB=ulib

clean:
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/Platform/ml clean
	rm -rf *.ml *.p.* *.cm* *.o *~ *.out

# ------------------ dependencies on Fstar & its libraries --------------------
# When using NuBuild, FStar must be located within the source tree. Now that soft links are 
# available on all platforms, I don't see a reason not to assume a fixed location.
FSTAR_HOME?=../../.fstar
# JP: this location can easily be overridden by doing:
#   FSTAR_HOME=../../../fstar make tls-gen
# BUT NOT AS FOLLOWS
#   make FSTAR_HOME=../../../fstar tls-gen
# the latter form won't work because FSTAR_HOME will incorrectly override values
# in recursive invocations of $(MAKE)...

# The .fst files found in [lib/ml] that are realized in
# stdlib-hyperheap.cmxa
STDLIB_REALIZED=All List Heap Set ST HyperHeap IO

OTHERFLAGS=--universes --explicit_deps --use_native_int
# --trace_error --print_universes 
STDLIB=FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst \
hyperheap/FStar.ST.fst hyperheap/FStar.All.fst FStar.Monotonic.RRef.fst FStar.Char.fsti FStar.String.fsti FStar.List.fst FStar.ListProperties.fst \
FStar.Seq.fst FStar.SeqProperties.fst FStar.Float.fsti FStar.IO.fsti FStar.UInt8.fst
CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap

FSTARFLAGS=$(OTHERFLAGS) \
	   $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	   $(OPTIONS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

PLATFORM_REALIZED=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/
PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20

# The .fst interfaces for the platform and crypto libraries.
LIBFILES = $(addprefix $(FSTAR_HOME)/$(LIB)/, $(STDLIB)) $(PLATFORM) $(CRYPTO)

OCAMLOPTS=-package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread
OCAML=ocamlfind ocamlopt
DEBUG=ocamlfind ocamlc
OCAMLMKLIB=ocamlfind ocamlmklib
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/$(LIB)/ml/native_int $(FSTAR_HOME)/$(LIB)/ml/hyperheap $(FSTAR_HOME)/$(LIB)/ml $(FSTAR_HOME)/$(CONTRIB)/Platform/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/db)

# ----------------------- NuBuild integration ------------------------
NUBUILD_HOME=../../.nubuild
NUBUILD=$(NUBUILD_HOME)/bin/NuBuild.exe
ifdef USE_NUBUILD
FSTAR_OR_NUBUILD=$(NUBUILD) FStarVerify $(FSTARFLAGS)
else
FSTAR_OR_NUBUILD=$(FSTAR)
endif

# ------------------------- miTLS* -------------------------------------------
# We try to limit the use of preprocessing, as it is messy.
# Not sure which interfaces we should put in there.

# This is the dependency order for interactive verification;
# these files are now all extracted via lax type-checking in tls-gen

FSTS=IdealFlags.fst \
MonotoneSeq.fst \
MonotoneMap.fst \
TLSError.fst \
TLSConstants.fst \
Nonce.fst \
RSAKey.fst \
DHGroup.fst \
ECGroup.fst \
CommonDH.fst \
PMS.fst \
HASH.fst \
HMAC.fst \
Sig.p.fst \
Cert.fst \
TLSInfo.fst \
IdNonce.fst \
TLSExtensions.fst \
Range.fst \
DataStream.fst \
Alert.fst \
Content.fst \
StreamPlain.fst \
StreamAE.fsti \
StreamAE.fst \
MasterSecret.fst \
StatefulPlain.fst \
LHAEPlain.fst \
AEAD_GCM.fst \
MAC.fst \
Encode.fst \
StatefulLHAE.fst \
ENC.fst \
MAC_SHA256.fst \
MAC_SHA1.fst \
HandshakeMessages.fst \
StAE.fsti \
StAE.fst \
Record.fst \
HSCrypto.fst \
TLSPRF.fst \
PRF.p.fst \
HandshakeLog.fst \
KeySchedule.fst \
Handshake.fsti \
Handshake.fst \
Connection.fst \
ConnInvariant.fst \
test/TestRecord.fst \
test/TestDH.fst \
test/TestClient.fst \
test/TestServer.fst \
test/TestServer13.fst \
test/TestClient13.fst #the preceding space is significant!

# BREAKING LAX CHECKING WITH StAE
#TLS.fst \

# these files are verified here for regression testing -- any time one more file
# verifies, it should be added here
# missing modules from FSTS are: PMS Sig Cert Encode Enc Handshake
VERIFY= \
MonotoneSeq \
MonotoneMap \
TLSError \
TLSConstants \
Nonce \
RSAKey \
DHGroup \
ECGroup \
CommonDH \
HASH \
HMAC \
TLSInfo \
IdNonce \
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
MAC_SHA256 \
MAC_SHA1 \
StAE \
Connection \
ConnInvariant


# admitting things verified elsewhere; redundant with lax and --verify_module?
# No, --verify_module overrides --admit_fsi
ADMITTED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_REALIZED)) SessionDB DHDB CoreCrypto Cert Handshake)


# truncates $(FSTS) just before $(basename $@).fst
define prefix_cfg
	$(shell str="$(FSTS)"; echo "$${str%%$(1).$(2) *}")
endef

# truncates $(FSTS) just after $(basename $@).fst
define prefix_ver
	$(shell str="$(FSTS)"; echo "$${str%%$(1).$(2) *} $(1).$(2)")
endef
# the space in calls to prefix_ver and prefix_cfg matters!

# verifying one file within $(FSTS)
%.fst-ver: $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	--__temp_no_proj Handshake --__temp_no_proj Connection \
	--verify_module $(subst .p,,$(basename $@)) \
	$^ \
	$(call prefix_ver,$(basename $@),fst)

%.fsti-ver:
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver, $(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

%.fst-in:
	@echo $(OTHERFLAGS) $(VERFLAGS) \
	--__temp_no_proj Handshake --__temp_no_proj Connection \
	$(LIBFILES) $(ADMITTED) \
	$(call prefix_cfg,$(basename $@),fst) \
	--verify_module $(subst .p,,$(basename $@))

%.fsti-in:
	@echo $(OTHERFLAGS) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_cfg, $(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

# verifying everything stable
# Add TLS.fst again when at least it lax type checks
tls-ver: $(LIBFILES) Ideal.fst $(FSTS)
	cp Ideal.fst IdealFlags.fst
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	--__temp_no_proj Handshake --__temp_no_proj Connection \
	$(addprefix --verify_module ,$(VERIFY)) \
	$(filter-out Ideal.fst,$^)

tls-sanity: $(LIBFILES) Ideal.fst $(FSTS) test/False.fst
	cp Ideal.fst IdealFlags.fst
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	--__temp_no_proj Handshake --__temp_no_proj Connection \
        --verify_module False \
	$(filter-out Ideal.fst,$^) | tail -n 1 | grep -c "Error: 1 errors were reported (see above)"


wc:
	wc -l $(LIBFILES) $(FSTS)

tls-lax: $(LIBFILES) Concrete.fst $(FSTS)
	cp Concrete.fst IdealFlags.fst
	$(FSTAR) --lax  $(ADMITTED) $(filter-out Concrete.fst,$^)

IdealFlags.fst:

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib-hyperheap has the entire F* standard library.
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib-hyperheap.cmxa

# .fst files realized elsewhere.
TLSGEN_REALIZED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_ADMITS) SessionDB DB DHDB CoreCrypto)

OUTPUT_DIR=output

# All our extracted modules.
TLSML := $(FSTS:.p.fst=.ml)
TLSML := $(TLSML:.fst=.ml)
TLSML := $(subst Handshake.fsti, , $(TLSML))
TLSML := $(subst StreamAE.fsti, , $(TLSML))
TLSML := $(subst StAE.fsti, , $(TLSML))
# F* does not provide an implementation for these in fstarlib.cmxa, so add them
# to our own list.
TLSML := \
  FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml FStar_Monotonic_RRef.ml \
  $(TLSML)
# Last step: F* currently extracts everything in the current directory
TLSML := $(addprefix $(OUTPUT_DIR)/,$(notdir $(TLSML)))

# Note to self: there is little point in breaking down this rule into more
# atomic ones. One may hope that we can only rebuild the .ml files that have
# changed; however, extraction is a global operation that touches every .ml
# file; as make is only aware of mtimes (and not hashsums), we would rebuild
# every single .ml file anyway...
tls-gen: $(LIBFILES) Concrete.fst $(FSTS)
	mkdir -p $(OUTPUT_DIR)
	cp Concrete.fst IdealFlags.fst
	$(FSTAR_HOME)/src/tools/rebuild_fstar_if $(FSTAR_HOME)
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions --__temp_no_proj FStar.Heap \
	  --odir $(OUTPUT_DIR) $(TLSGEN_REALIZED) \
	  $(filter-out Concrete.fst,$^)

	# Builds everything against native_int/prims; including native_int/prims.cmx
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml hyperheap PRIMS_DIR=native_int
	# Recursively builds everything in platform, etc.
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml
	# # All our .cmx files
	$(OCAML) $(OCAMLOPTS) -w -a $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) -c $(TLSML)
	# A .cmxa with all the .cmx above
	$(OCAML) -a $(OCAML_INCLUDE_PATHS) $(TLSML:.ml=.cmx) -I $(OUTPUT_DIR) -o mitls.cmxa
	# Then our test executable
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) $(LIB_ML) mitls.cmxa \
	         -I test/ test/parsing_test.ml test/test_main.ml -o test.out
	# Run the test
	$(EXTRA_PATH) ./test.out

tls-client:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_client.ml -o client.out
	$(EXTRA_PATH) ./client.out 1.2 google.com 443

tls-server:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_server.ml -o server.out
	$(EXTRA_PATH) ./server.out 1.2 0.0.0.0 4443

# ------------------ preprocessing :( -----------------------

# preprocessing is still a necessary pain; pls remove files below when possible
# Nonce still has an #ideal flag
# many files have __SOURCE_FILE__ __LINE__ macros
TLS_PP_FILES= PMS Sig PRF

# Target to generate preprocessed files for atom-interactive
pp:: $(addsuffix .p.fst, $(TLS_PP_FILES))


HAS_CPP := $(shell which cpp 2> /dev/null; echo $$?)
ifeq ($(HAS_CPP),1)
   $(error "cpp not found in PATH. Unable to proceed")
endif

ifeq ($(OS),Windows_NT)
    EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    CPP=cpp #-ffreestanding
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
        CPP=cpp -ffreestanding
    else
        HAS_GNU_CPP := $(shell which cpp-5 2> /dev/null; echo $$?)
        ifeq ($(HAS_GNU_CPP),1)
            $(error "cpp-5 not found in PATH. Unable to proceed")
        endif
        CPP=cpp-5 # GCC cpp rather than LLVM
    endif
endif

%.p.fsi: %.fsi
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fsti: %.fsti
	$(CPP) -P -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fst: %.fst
	$(CPP) -P -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fs: %.fs
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@
