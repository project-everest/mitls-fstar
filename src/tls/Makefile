# These are all the known working targets in this file,
# Check for regressions & comment about them!
all: tls-ver tls-sanity tls-lax tls-gen

CONTRIB=ucontrib
LIB=ulib

clean:
	$(MAKE) -C $(FSTAR_HOME)/$(LIB)/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/$(CONTRIB)/Platform/ml clean
	rm -rf IdealFlags.fst *.ml *.p.* *.cm* *.o *~ *.out output

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

# .fst files in [lib/ml] that are realized in stdlib-hyperheap.cmxa
STDLIB_REALIZED=All List Heap Set ST HyperHeap IO

OPTIONS=--universes --use_native_int

STDLIB=FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst \
hyperheap/FStar.ST.fst hyperheap/FStar.All.fst FStar.Monotonic.RRef.fst FStar.Char.fsti FStar.String.fsti FStar.List.fst FStar.ListProperties.fst \
FStar.Seq.fst FStar.SeqProperties.fst FStar.Float.fsti FStar.IO.fsti FStar.UInt8.fst

CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap

FSTARFLAGS=$(OPTIONS) $(OTHERFLAGS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

PLATFORM_REALIZED=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/
PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20 --__temp_no_proj Handshake --__temp_no_proj Connection

# The .fst interfaces for the platform and crypto libraries.
LIBFILES=$(addprefix $(FSTAR_HOME)/$(LIB)/, $(STDLIB)) $(PLATFORM) $(CRYPTO)

FSTAR_INCLUDE_PATHS=--include $(CDIR) --include $(PDIR) --include $(FSTAR_HOME)/$(LIB)/hyperheap 

OCAMLOPTS=-package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread
OCAML=ocamlfind ocamlopt
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/$(LIB)/ml/native_int $(FSTAR_HOME)/$(LIB)/ml/hyperheap $(FSTAR_HOME)/$(LIB)/ml $(FSTAR_HOME)/$(CONTRIB)/Platform/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/db)

# ----------------------- NuBuild integration -------------------------
NUBUILD_HOME=../../.nubuild
NUBUILD=$(NUBUILD_HOME)/bin/NuBuild.exe
ifdef USE_NUBUILD
FSTAR_OR_NUBUILD=$(NUBUILD) FStarVerify $(FSTARFLAGS)
else
FSTAR_OR_NUBUILD=$(FSTAR)
endif

# ---------------------------------------------------------------------
# These files are all extracted via lax type-checking in tls-gen
# Files are listed in dependency order

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
Signature.fst \
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
StAE.fst \
StreamDeltas.fst \
Record.fst \
HSCrypto.fst \
TLSPRF.fst \
PRF.fst \
HandshakeLog.fst \
KeySchedule.fst \
Handshake.fsti \
Handshake.fst \
Connection.fst \
test/TestRecord.fst \
test/TestDH.fst \
test/TestClient.fst \
test/TestServer.fst \
test/TestServer13.fst \
test/TestClient13.fst \
ConnInvariant.fst \
TLS.fst #the preceding space is significant!

# --------------------------------------------------------------------
# Modules verified in tls-ver -- any time one more file verifies, it
# should be added here.
#
# Missing modules from FSTS:
# Cert, TLSExtensions, Encode, ENC, HandshakeMessages, Record, HSCrypto,
# TLSPRF, PRF, HandshakeLog, KeySchedule, Handshake

VERIFY= \
IdealFlags \
MonotoneSeq \
MonotoneMap \
TLSError \
TLSConstants \
Nonce \
RSAKey \
DHGroup \
ECGroup \
CommonDH \
PMS \
HASH \
HMAC \
Signature \
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
StreamDeltas \
Connection \
ConnInvariant \
TLS 

all-ver: IdealFlags.fst $(addsuffix .fst-ver, $(VERIFY))

# Lax-checking one file at a time
%.fst-lax: IdealFlags.fst $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $@) \
	$(basename $@).fst

# Verifying one file at a time
%.fst-ver: IdealFlags.fst $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $@) \
	$(basename $@).fst

%.fsti-ver: IdealFlags.fst $(LIBFILES)
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $@) \
	$(basename $@).fsti

# Targets to get F* arguments in interactive mode
%.fst-in: IdealFlags.fst
	$(MAKE) refresh > /dev/null
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $@) \
	$(basename $@).fst

%.fsti-in: IdealFlags.fst
	$(MAKE) refresh > /dev/null
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $@) \
	$(basename $@).fsti

# Verifying everything stable
tls-ver: $(LIBFILES) $(FSTS)
	$(MAKE) refresh
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	$(addsuffix .fst,$(VERIFY))

# Sanity check
tls-sanity: $(LIBFILES) $(FSTS) test/False.fst
	$(MAKE) refresh
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
        --verify_module False \
	$(FSTS) test/False.fst | tail -n 1 | grep -c "Error: 1 errors were reported (see above)"

# Lax typecheck all files (with ideal flag off)
tls-lax: $(LIBFILES) Concrete.fst $(FSTS)
	cp Concrete.fst IdealFlags.fst
	$(MAKE) refresh
	$(FSTAR) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	$(FSTS)

wc:
	wc -l $(LIBFILES) $(FSTS)

IdealFlags.fst: Ideal.fst
	cp Ideal.fst IdealFlags.fst

# These are the .cmx files for all ML-implemented F* modules.
# CoreCrypto has DB, DHDB, Platform and CoreCrypto all together.
# fstarlib-hyperheap has the entire F* standard library.
LIB_ML= \
  $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa \
  $(FSTAR_HOME)/$(LIB)/ml/fstarlib-hyperheap.cmxa

# .fst files realized elsewhere.
TLSGEN_REALIZED=$(addprefix --no_extract ,$(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_REALIZED) SessionDB DB DHDB CoreCrypto)

OUTPUT_DIR=output

# All our extracted modules.
TLSML := $(FSTS:.fst=.ml)
TLSML := $(subst Handshake.fsti, , $(TLSML))
TLSML := $(subst StreamAE.fsti, , $(TLSML))
TLSML := $(subst StAE.fsti, , $(TLSML))
# F* does not provide an implementation for these in fstarlib.cmxa, so add them
# to our own list.
TLSML := \
  FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml FStar_Monotonic_RRef.ml \
  $(TLSML)
# Last step: prefix with the output directory.
TLSML := $(addprefix $(OUTPUT_DIR)/,$(notdir $(TLSML)))

refresh:
	$(FSTAR_HOME)/src/tools/rebuild_fstar_if $(FSTAR_HOME)

# Note to self: there is little point in breaking down this rule into more
# atomic ones. One may hope that we can only rebuild the .ml files that have
# changed; however, extraction is a global operation that touches every .ml
# file; as make is only aware of mtimes (and not hashsums), we would rebuild
# every single .ml file anyway...
tls-gen: $(LIBFILES) Concrete.fst $(FSTS)
	cp Concrete.fst IdealFlags.fst
	$(MAKE) refresh
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj TLSExtensions \
	  --__temp_no_proj FStar.Heap --odir $(OUTPUT_DIR) $(TLSGEN_REALIZED) \
	  $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	  $(FSTAR_INCLUDE_PATHS) \
	  $(FSTS)

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

mitls.exe: tls-gen
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
		-I test/ -I output/ test/mitls.ml -o mitls.exe

tls-client:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_client.ml -o client.out
	$(EXTRA_PATH) ./client.out 1.2 google.com 443

tls-server:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_server.ml -o server.out
	$(EXTRA_PATH) ./server.out 1.2 0.0.0.0 4443

# depends on tls-gen
test13:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_client.ml -o client13.exe
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(LIB_ML) mitls.cmxa \
	         -I test/ -I output/ test/test_server.ml -o server13.exe
	$(EXTRA_PATH) ./server13.exe 1.3 0.0.0.0 4443 &
	$(EXTRA_PATH) ./client13.exe 1.3 127.0.0.1 4443
	taskkill /F /IM server13.exe

ifeq ($(OS),Windows_NT)
    EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
endif
