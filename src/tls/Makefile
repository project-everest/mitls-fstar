# These are all the known working targets in this file,
# check for regressions & comment about them!
all: tls-ver tls-lax tls-gen

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
STDLIB_ADMITS=All List Heap Set ST HyperHeap IO

OTHERFLAGS=--universes --explicit_deps
STDLIB=FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst \
hyperheap/FStar.ST.fst hyperheap/FStar.All.fst FStar.Monotonic.RRef.fst FStar.Char.fsti FStar.String.fsti FStar.List.fst FStar.ListProperties.fst \
FStar.Seq.fst FStar.SeqProperties.fst FStar.IO.fsti #FStar.Int64.fst 
CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap

FSTARFLAGS=$(OTHERFLAGS) \
	   $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	   $(OPTIONS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

PLATFORM_ADMITS=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/
PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20

# The .fst interfaces for the platform and crypto libraries.
LIBFILES = $(addprefix $(FSTAR_HOME)/$(LIB)/, $(STDLIB)) $(PLATFORM) $(CRYPTO)

OCAMLOPTS=-package batteries,stdint,fileutils,sqlite3 -linkpkg -g -thread
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

# these files are the stable inputs for verification -- this is the dependency
# order for interactive verification; these files are now all extracted via
# lax type-checking in tls-gen
FSTS=$(subst Handshake.fsti Connection.fst, $(LAX_CHECKED_FSTS), $(VERIFIABLE_FSTS))

VERIFIABLE_FSTS=TLSError.fst \
TLSConstants.fst \
Nonce.fst \
RSAKey.fst \
DHGroup.fst \
ECGroup.fst \
CommonDH.fst \
PMS.p.fst \
HASH.fst \
HMAC.fst \
Sig.p.fst \
UntrustedCert.fst \
Cert.fst \
TLSInfo.fst \
Range.fst \
DataStream.fst \
Alert.fst \
Content.fst \
StreamPlain.fst \
StreamAE.fst \
StatefulPlain.fst \
LHAEPlain.fst \
AEAD_GCM.fst \
MAC.fst \
Encode.fst \
StatefulLHAE.fst \
ENC.fst \
MAC_SHA256.fst \
MAC_SHA1.fst \
Handshake.fsti \
Connection.fst #the preceding space is significant!

LAX_CHECKED_FSTS=Record.fst \
test/TestRecord.fst \
test/TestDH.fst \
TLSExtensions.p.fst \
HSCrypto.fst \
HandshakeMessages.fst \
TLSPRF.fst \
PRF.p.fst \
Handshake.fst \
Connection.fst \
TLS.fst #the preceding space is significant!

# these files are verified here for regression testing -- any time one more file
# verifies, it should be added here
# missing modules from VERIFIABLE_FSTS are: PMS Sig Cert Encode Enc
VERIFY=\
TLSError \
TLSConstants \
Nonce \
RSAKey \
DHGroup \
ECGroup \
CommonDH \
HASH \
HMAC \
UntrustedCert \
TLSInfo \
Range \
DataStream \
Alert \
Content \
StreamPlain \
StreamAE \
StatefulPlain \
LHAEPlain \
AEAD_GCM \
MAC \
StatefulLHAE \
MAC_SHA256 \
MAC_SHA1 \
Connection 


# admitting things verified elsewhere; redundant with lax and --verify_module?
# No, --verify_module overrides --admit_fsi
ADMITTED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_ADMITS)) SessionDB DHDB CoreCrypto Cert Handshake)


# truncates $(FSTS) just before $(basename $@).fst
define prefix_cfg
	$(shell str="$(VERIFIABLE_FSTS)"; echo "$${str%%$(1).$(2) *}")
endef

# truncates $(FSTS) just after $(basename $@).fst
define prefix_ver
	$(shell str="$(VERIFIABLE_FSTS)"; echo "$${str%%$(1).$(2) *} $(1).$(2)")
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
tls-ver: $(LIBFILES) $(VERIFIABLE_FSTS)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	--__temp_no_proj Handshake --__temp_no_proj Connection \
	$(addprefix --verify_module ,$(VERIFY)) \
	$^

# same as tls-ver, but verifies one module at a time.
tls-ver1: $(FSTS) $(addsuffix .fst-ver,$(VERIFY))

wc:
	wc -l $(LIBFILES)) $(FSTS)

tls-lax: $(LIBFILES) $(FSTS)
	$(FSTAR) --lax  $(ADMITTED) $^

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib-hyperheap has the entire F* standard library.
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib-hyperheap.cmxa

# .fst files realized elsewhere.
TLSGEN_ADMIT=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_ADMITS)) $(PLATFORM_ADMITS) SessionDB DB DHDB CoreCrypto)

# All our extracted modules.
TLSML := $(FSTS:.p.fst=.ml)
TLSML := $(TLSML:.fst=.ml)
# F* does not provide an implementation for these in fstarlib.cmxa, so add them
# to our own list.
TLSML := \
  FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml \
  $(TLSML)
# Last step: F* currently extracts everything in the current directory
TLSML := $(notdir $(TLSML))

# Note to self: there is little point in breaking down this rule into more
# atomic ones. One may hope that we can only rebuild the .ml files that have
# changed; however, extraction is a global operation that touches every .ml
# file; as make is only aware of mtimes (and not hashsums), we would rebuild
# every single .ml file anyway...
tls-gen: $(LIBFILES) $(FSTS)
	$(FSTAR_HOME)/src/tools/rebuild_fstar_if $(FSTAR_HOME)
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions --__temp_no_proj FStar.Heap \
	  $(TLSGEN_ADMIT) \
	  $^
	# Builds everything against native_int/prims; including native_int/prims.cmx
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml hyperheap PRIMS_DIR=native_int
	# Recursively builds everything in platform, etc.
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml
	# # All our .cmx files
	$(OCAML) $(OCAMLOPTS) -w -a $(OCAML_INCLUDE_PATHS) -c $(TLSML)
	# A .cmxa with all the .cmx above
	$(OCAML) -a $(OCAML_INCLUDE_PATHS) $(TLSML:.ml=.cmx) -o mitls.cmxa
	# Then our test executable
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ test/parsing_test.ml test/test_main.ml -o test.out
	# Run the tests
	$(EXTRA_PATH) ./test.out

# ------------------ preprocessing :( -----------------------

# preprocessing is still a necessary pain; pls remove files below when possible
# Nonce still has an #ideal flag
# many files have __SOURCE_FILE__ __LINE__ macros
TLS_PP_FILES= TLSExtensions PMS Sig PRF TLSExtensions ENC

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
