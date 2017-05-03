MITLS_HOME ?= ../..
FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME ?= ../../../hacl-star
FFI_HOME ?= $(MITLS_HOME)/libs/ffi
MARCH ?= x86_64
ODIR ?= output

FSTARFLAGS = --fstar_home $(FSTAR_HOME) $(OTHERFLAGS)
FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTARFLAGS)

HINTS_ENABLED ?= --use_hints
VERFLAGS = --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection $(HINTS_ENABLED)

all:
	+$(MAKE) build
	+$(MAKE) verify

build:
	+$(MAKE) mitls.exe
	+$(MAKE) tls-ffi

verify:
	+$(MAKE) all-ver
	+$(MAKE) tls-sanity
	+$(MAKE) tls-lax

depend:
	-rm .depend* $(ODIR)/.depend

clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/Platform/ml clean
	$(MAKE) -C $(HACL_HOME)/secure_api/LowCProvider clean
	$(MAKE) -C $(FFI_HOME) clean
	-rm -rf .depend* *.ml *.cm* *.o *.a *.exe *~ *.out $(ODIR) 
	-rm -rf test/*.cm* test/*.o

record_fstar_version:
	$(FSTAR) --version | grep ^commit | sed 's/commit=\([^ ]*\).*/\1/' > $(MITLS_HOME)/.fstar_version

.PHONY: all build verify depend clean record_fstar_version

STDLIB_REALIZED=Mul Float Char Int8 UInt8 Int16 UInt16 Int32 UInt32 Int64 UInt64 UInt128 Int_Cast BaseTypes IO Heap List.Tot.Base List Option String Set Buffer CommonST TSet Map HyperHeap HyperStack ST All
CODEGEN_LIBS=Platform
# CoreCrypto LowCProvider Platform Classical Seq HyperHeap HyperStack FFICallbacks
PLATFORM_REALIZED=$(addprefix Platform.,Bytes Date Error Tcp)
PDIR=$(FSTAR_HOME)/ucontrib/Platform/fst/
CDIR=$(FSTAR_HOME)/ucontrib/CoreCrypto/fst/
LLDIR=$(HACL_HOME)/secure_api
LCDIR=$(LLDIR)/LowCProvider

# Modules that are implemented in ML or C
NOEXTRACT=$(addprefix --no_extract ,Prims $(addprefix FStar., $(STDLIB_REALIZED)) $(PLATFORM_REALIZED) CoreCrypto LowCProvider FFICallbacks)

HACL_INCLUDES=$(addprefix --include ,$(KREMLIN_HOME)/kremlib $(HACL_HOME)/specs $(HACL_HOME)/code/lib/kremlin $(HACL_HOME)/code/bignum $(HACL_HOME)/code/experimental/aesgcm $(HACL_HOME)/code/poly1305 $(HACL_HOME)/code/salsa-family $(LLDIR)/test $(LLDIR)/utils $(LLDIR)/vale $(LLDIR)/uf1cma $(LLDIR)/prf $(LLDIR)/aead)
FSTAR_INCLUDE_PATHS=--include $(CDIR) --include $(PDIR) --include $(LCDIR)/fst $(HACL_INCLUDES) --include $(FFI_HOME) --include $(FSTAR_HOME)/ulib/hyperstack

OCAMLPKG=-package batteries,stdint,fileutils,sqlite3,zarith
OCAMLOPTS=$(OCAMLPKG) -linkpkg -g -thread -w -a
OCAML_PATHS=test $(ODIR) $(FSTAR_HOME)/ulib/ml/extracted $(FSTAR_HOME)/ulib/ml/hyperstack $(FSTAR_HOME)/ulib/ml $(FSTAR_HOME)/ucontrib/Platform/ml $(FSTAR_HOME)/ucontrib/CoreCrypto/ml $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/db $(LCDIR) ../../libs/ml $(FFI_HOME)
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
MAC_SHA256 \
MAC_SHA1 \
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
FFI

.depend-TLS: $(wildcard *.fst *.fsti)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make FFI.fst > .depend-TLS
.depend-HS: $(wildcard *.fst *.fsti)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make Handshake.fst > .depend-HS
.depend-AEAD: $(wildcard $(HACL_HOME)/secure_api/*/*.fst)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --dep make Crypto.AEAD.Main.fst > .depend-AEAD

-include .depend-TLS
-include .depend-HS
-include .depend-AEAD

# Makefile voodoo to substitute _ for . in module names
# Note that this is not sound if the F* module name contains an underscore (e.g. AEAD_GCM.fst)
# The dependencies are handled by the .depend files above to allow semi-incremental extraction
# (it is only incremental on connected components of the dependency graph rather than on a per-module basis)
.SECONDEXPANSION:
$(ODIR)/%.ml: $$(subst _,.,%.fst)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

test/%.ml: test/%.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir test $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags --extract_module $(*F) $<

# Special case for Crypto.AEAD.*: must look in hacl-star/secure_api/aead
# Note that dependencies have absolute paths in the .depend so there is no need 
# to specialize for other internal Hacl paths
$(ODIR)/Crypto_AEAD_%.ml: $(LLDIR)/aead/Crypto.AEAD.%.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

# miTLS flags: extract with concrete
$(ODIR)/Flags.ml: concrete-flags/Flags.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

# Hacl flags: extract with concrete
$(ODIR)/Flag.ml: $(LLDIR)/test/Flag.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

# Try to only rebuild fstarlib when necessary
$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa: \
       		$(wildcard $(FSTAR_HOME)/ulib/*.fst) \
		$(wildcard $(FSTAR_HOME)/ulib/ml/*.ml) \
	       	$(wildcard $(FSTAR_HOME)/ulib/ml/extracted/*.ml) \
		$(wildcard $(FSTAR_HOME)/ulib/ml/hyperstack/*.ml)
	make -C $(FSTAR_HOME)/ulib/ml MEM=HST

# Try to only rebuild CoreCrypto when necessary
$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmi $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmx $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa: \
		$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.ml
	make -C $(FSTAR_HOME)/ucontrib/CoreCrypto/ml

# Try to only rebuild LowCProvider when necessary
# Missing: not dependency on hacl-star/code/*
$(LCDIR)/LowCProvider.cmxa: $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa $(wildcard $(LLDIR)/*/*.fst)
	make -C $(LCDIR)

$(FFI_HOME)/FFICallbacks.cmxa: $(wildcard $(FFI_HOME)/*.ml) $(wildcard $(FFI_HOME)/*.c)
	make -C $(FFI_HOME)

$(ODIR)/.depend: \
		$(ODIR)/Flag.ml $(ODIR)/Flags.ml \
	       	$(ODIR)/Crypto_AEAD_Main.ml \
		$(ODIR)/HKDF.ml \
	       	$(ODIR)/HandshakeLog.ml \
	       	$(ODIR)/Handshake.ml \
	       	$(ODIR)/FFI.ml \
		test/TestAPI.ml \
		test/TestFFI.ml
	ocamlfind ocamldep -native -slash -all $(OCAMLPKG) $(OCAML_INCLUDE_PATHS) $(addsuffix /*.ml,$(OCAML_PATHS)) test/TestAPI.ml test/TestFFI.ml > $(ODIR)/.depend

-include $(ODIR)/.depend

%.cmi %.cmx: %.ml
	ocamlfind ocamlopt $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -c $<

mitls.cmxa: \
	$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa \
       	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
       	$(LCDIR)/LowCProvider.cmxa \
	$(FFI_HOME)/FFICallbacks.cmxa \
       	$(ODIR)/FFI.cmx
	ocamlfind ocamlopt $(OCAML_INCLUDE_PATHS) -a output/*.cmx -o mitls.cmxa

mitls.exe: mitls.cmxa test/TestAPI.cmx test/TestFFI.cmx test/mitls.cmx
	ocamlfind ocamlopt $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I test/ -g \
	$(FSTAR_HOME)/ulib/ml/fstarlib.cmxa \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/lowc_stub.o $(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	$(FFI_HOME)/FFICallbacks.cmxa \
	mitls.cmxa \
	test/TestAPI.cmx test/TestFFI.cmx \
       	test/mitls.cmx -o mitls.exe

all-ver: record_fstar_version $(addsuffix .fst-ver, $(VERIFY))

# Lax-checking one file at a time
%.fst-lax: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/concrete-flags \
	$(basename $@).fst

# Verifying one file at a time
# @echo -e  "\e[1;34m"Verifying $(basename $(notdir $@)) "\e[0m"; 
%.fst-ver: $(LIBFILES)
	@$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver: $(LIBFILES)
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
	--verify_module $(basename $(notdir $@))

%.fsti-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@))

# Sanity check
tls-sanity: record_fstar_version $(LIBFILES)
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
        --verify_module False \
	$(FSTS) test/False.fst 2>&1 | tail -n 1 | grep -c '1 error was reported (see above)'

tls-lax: record_fstar_version $(LIBFILES)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax \
	--include $(MITLS_HOME)/src/tls/concrete-flags \
	TLS.fst

wc:
	wc -l $(LIBFILES) *.fst *.fsti

test.run:
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) $(LIB_ML) mitls.cmxa -I test/ test/parsing_test.ml test/test_hkdf.ml test/test_main.ml -o test.out
	./test.out

test.out: mitls.cmxa 
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I $(OUTPUT_DIR) $(LIB_ML) mitls.cmxa -I test/ test/parsing_test.ml test/test_hkdf.ml test/test_main.ml -o test.out

.PHONY: test
test: test.out mitls.exe
	# Unit tests from test/test_main.ml
	$(EXTRA_PATH) ./test.out
	# Run mitls.exe 
	./mitls.exe  -v 1.2 -ffi www.google.com
	./mitls.exe  -v 1.2 -noems www.microsoft.com
	#./mitls.exe -v 1.3. www.google.com failing due to different draft versions

# Depends on mitls.cmxa
rpc.ml:
	$(FSTAR) \
	  --no_location_info --lax --codegen OCaml --__temp_no_proj Extensions \
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

# our interactive tests; the baseline is make client{|12|13} vs make server 

server::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.3 -s -cert ../../data/server.crt -key ../../data/server.key 127.0.0.1 4443 
server12::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.2 -s -cert ../../data/server.crt -key ../../data/server.key 127.0.0.1 4443 
server13::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 -s -cert ../../data/server.crt -key ../../data/server.key 127.0.0.1 4443 

client13::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 127.0.0.1 4443 
client12::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.2 127.0.0.1 4443 
client::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.3 127.0.0.1 4443
