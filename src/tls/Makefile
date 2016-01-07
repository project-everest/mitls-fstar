# These are all the known working targets in this file,
# check for regressions & comment about them!
all: mitls-ver mitls-ml
# TODO extend scope of verification
# TODO compilation to ML & testing

clean:
	rm -rf *.ml *.p.* *.cm* *.o *~ *.out

# ------------------ dependencies on Fstar & its libraries --------------------
# When using NuBuild, FStar must be located within the source tree. Now that soft links are 
# available on all platforms, I don't see a reason not to assume a fixed location.
FSTAR_HOME=../../.fstar
add_stdlib_prefix=$(addprefix $(FSTAR_HOME)/lib/,$(1))

#STDLIB_ADMITS=Set Map HyperHeap Seq Char SeqProperties
STDLIB_ADMITS=Char HyperHeap Set Map

STDLIB=ext.fst classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi listTot.fst hyperHeap.fsi \
stHyperHeap.fst allHyperHeap.fst char.fsi string.fst list.fst listproperties.fst seq.fsi \
seq.fst seqproperties.fst #int64.fst 
CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap

FSTARFLAGS=$(call add_stdlib_prefix,$(STDLIB)) $(addprefix --codegen-lib , $(CODEGEN_LIBS)) $(OTHERFLAGS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTARFLAGS)

PDIR=$(FSTAR_HOME)/contrib/Platform/fst/

PLATFORM=$(addprefix $(PDIR),Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/contrib/CoreCrypto/fst/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

# MK: doesn't seem to be used, so I removed it after discussing with Santiago
DHDB= #$(DHDBDIR)DHDBManager.fst

VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 60

LIBFILES = $(PLATFORM) $(CRYPTO) $(DHDB)

OCAML=ocamlfind ocamlopt -package batteries -package stdint -linkpkg -g -thread
DEBUG=ocamlfind ocamlc -package batteries -package stdint -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml/hyperheap $(FSTAR_HOME)/lib/ml $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml/db ~/dev/mitls/mitls-fstar/src/tls)

# ----------------------- NuBuild integration ------------------------
NUBUILD_HOME=../../.nubuild
NUBUILD=$(NUBUILD_HOME)/bin/NuBuild.exe
ifdef USE_NUBUILD
FSTAR_OR_NUBUILD=$(NUBUILD) --quiet FStarVerify $(FSTARFLAGS)
else
FSTAR_OR_NUBUILD=$(FSTAR)
endif

# ------------------------- miTLS* -------------------------------------------
# We try to limit the use of preprocessing, as it is messy.
# Not sure which interfaces we should put in there.

# these files are the stable inputs for verification
TLSVER=TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst Range.p.fst DataStream.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fsti StatefulLHAE.fst Handshake.fsti Record.fst Connection.fst # TLS.fst #the preceding space is significant (see prefix_cfg)
#Removed temporarily: StatefulPlain.fsti
#Removed temporarily: TLS.fst

TLSREDUX=TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst \
	DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst \
	UntrustedCert.fsti Cert.fsti TLSInfo.fst TLSExtensions_Redux.p.fst Range.p.fst \
	DataStream.fst TLSPRF.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst \
	AEAD_GCM.fst StatefulLHAE.fst PRF-redux.p.fst  \
	HandshakeMessages_Redux.fst Handshake_Redux.fst

TLSPARSE=TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst \
	DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst \
	UntrustedCert.fst Cert.fst TLSInfo.fst TLSExtensions_Redux.p.fst \
	HandshakeMessages_Redux.fst

# these files are verified here
VERIFY=TLSError TLSConstants Nonce TLSInfo Range LHAEPlain AEAD_GCM StatefulLHAE DataStream Alert Content StatefulPlain

# admitting things verified elsewhere; redundant with lax and --verify_module?
# No, --verify_module overrides --admit_fsi
ADMITTED=$(addprefix --admit_fsi ,$(addprefix FStar., $(STDLIB_ADMITS)) SessionDB UntrustedCert DHDB CoreCrypto Cert Handshake)

# The whole TLS source tree, in dependency order --- where we are going, but not used yet.
TLS= $(TLSVER) \
TLSExtensions.p.fst TLSPRF.fst\
\
HSFragment.fst\
MAC_SHA256.p.fst\
MAC_SHA1.p.fst\
MAC.p.fst\
Encode.p.fst\
ENC.p.fst\
AEAD_GCM.fst\
LHAE.p.fst\
StatefulLHAE.fst\
Record.fst\
\
PRF.p.fst KEF.p.fst DH.p.fst RSA.p.fst SessionDB.p.fsti HandshakeMessages.p.fst Handshake.p.fst\
\
Handshake.fsti\
Connection.fst\
TLS.fst

# truncates $(TLSVER) just before $(basename $@).fst
define prefix_cfg
	$(shell str="$(TLSVER)"; echo "$${str%%$(1).$(2) *}")
endef

# truncates $(TLSVER) just after $(basename $@).fst
define prefix_ver
	$(shell str="$(TLSVER)"; echo "$${str%%$(1).$(2) *} $(1).$(2)")
endef

# verifying one file within $(TLSVER)
%.fst-ver:
	$(FSTAR_OR_NUBUILD) $(VERFLAGS) $(LIBFILES) $(ADMITTED) --verify_module $(subst .p,,$(basename $@)) $(call prefix_ver,$(basename $@),fst)

%.fsti-ver:
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver,$(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

%.fst-in:
	@echo $(VERFLAGS) $(STDLIB) $(LIBFILES) $(ADMITTED) $(call prefix_cfg,$(basename $@),fst) \
--verify_module $(subst .p,,$(basename $@))

%.fsti-in:
	@echo $(VERFLAGS) $(STDLIB) $(LIBFILES) $(ADMITTED) $(call prefix_cfg,$(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

# prints build-config block for interactive verification
%.fst-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg,$(basename $@),fst)
	@echo '--*)'

%.fsti-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg,$(basename $@),fsti)
	@echo '--*)'


# verifying everything stable
# Add TLS.fst again when at least it lax type checks
mitls-ver: $(LIBFILES) $(TLSVER) $(addsuffix .fst-ver,$(basename $(TLSVER)))

# going beyond TLSVER, not necessarily working

api-ver: $(LIBFILES) $(TLSVER) TLS.fsti
	$(FSTAR) $(ADMITTED) $(VERFLAGS) $^

test-gcm: $(LIBFILES)
	$(FSTAR) --lax $(ADMITTED) --codegen OCaml --admit_fsi FStar.IO \
	--include $(PDIR) --include $(CDIR) \
	$^ FStar.IO.fsti $(call prefix_ver,AEAD_GCM,fst) StatefulLHAE.fst TestGCM.fst	

top: $(LIBFILES) $(TLSVER)
	$(FSTAR) $(ADMITTED) $(VERFLAGS) $^ StatefulLHAE.fsti Record.fst Handshake.fsti --admit_fsi StatefulLHAE --admit_fsi Handshake --verify_module TLS


# --trace_error
mitls-ml: $(LIBFILES) $(TLSVER)
	$(FSTAR) --lax --debug Extreme $(ADMITTED) $^ --codegen OCaml --use_native_int --trace_error
	mv *.ml ../tls-ml

wc:
	wc -l $(STDLIB) $(PLATFORM) $(CRYPTO) $(DHDB) $(TLS)

redux: $(LIBFILES) $(TLSREDUX)
	$(FSTAR) --lax  $(ADMITTED) $^

TLSPARSE_ML=FStar_List_Tot.ml FStar_Seq.ml FStar_SeqProperties.ml TLSError.ml TLSConstants.ml $(FSTAR_HOME)/contrib/CoreCrypto/ml/DHDB.ml Nonce.ml RSAKey.ml ECGroup.ml DHGroup.ml CommonDH.ml PMS.ml HASH.ml Sig.ml UntrustedCert.ml Cert.ml TLSInfo.ml TLSExtensions.ml HandshakeMessages.ml
LIB_ML=$(FSTAR_HOME)/lib/ml/FStar_List.cmx $(FSTAR_HOME)/lib/ml/native_int/prims.cmx $(FSTAR_HOME)/contrib/CoreCrypto/ml/db/DB.cmx $(FSTAR_HOME)/contrib/CoreCrypto/ml/corecrypto.cmxa $(FSTAR_HOME)/lib/ml/hyperheap/FStar_ST.cmx $(FSTAR_HOME)/lib/ml/hyperheap/FStar_HyperHeap.cmx $(FSTAR_HOME)/lib/ml/FStar_All.cmx
TLSPARSE_ADMIT=$(addprefix --admit_fsi ,$(addprefix FStar., $(STDLIB_ADMITS)) SessionDB DHDB CoreCrypto Handshake)

redux-gen: $(LIBFILES) $(TLSPARSE)
	$(FSTAR) --lax --codegen OCaml  $(TLSPARSE_ADMIT) $^
	rm -f $(FSTAR_HOME)/lib/ml/FStar_ST.cmi
	make -C $(FSTAR_HOME)/lib/ml hyperheap
	make -C $(FSTAR_HOME)/contrib/Platform/ml
	make -C $(FSTAR_HOME)/contrib/CoreCrypto/ml/db
	rm -f $(FSTAR_HOME)/lib/ml/prims.cmi
	$(OCAML) $(FSTAR_HOME)/lib/ml/native_int/prims.ml
	make -C $(FSTAR_HOME)/contrib/CoreCrypto/ml
	make -C $(FSTAR_HOME)/contrib/CoreCrypto/ml/db DB.cmx
	$(OCAML) -w -a $(OCAML_INCLUDE_PATHS) -c $(TLSPARSE_ML)
	cp ./test/parsing_test.ml .
	$(OCAML) -package fileutils,sqlite3 $(OCAML_INCLUDE_PATHS) $(LIB_ML) $(TLSPARSE_ML:.ml=.cmx) parsing_test.ml -o test.out
	./test.out

# ------------------ preprocessing :( -----------------------

# preprocessing is still a necessary pain; pls remove files below when possible
# Nonce still has an #ideal flag
# many files have __SOURCE_FILE__ __LINE__ macros
TLS_PP_FILES= TLSExtensions PMS DHGroup Encode Range Sig PRF-redux TLSExtensions_Redux
# DHGroup.p.fst PMS.p.fst \
	TLSExtensions.p.fst TLSPRF.p.fst \
	HSFragment.p.fst TLSFragment.p.fst StatefulPlain.p.fst \
	LHAEPlain.p.fst MAC_SHA256.p.fst MAC_SHA1.p.fst MAC.p.fst Encode.p.fst \
	ENC.p.fst AEAD_GCM.p.fst LHAE.p.fst \
	PRF.p.fst KEF.p.fst DH.p.fst RSA.p.fst SessionDB.p.fsti \
	HandshakeMessages.p.fst Handshake.p.fst

# Target to generate preprocessed files for atom-interactive
pp:: $(addsuffix .p.fst, $(TLS_PP_FILES))

ifeq ($(OS),Windows_NT)
    CPP=cpp #-ffreestanding
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
	PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
        CPP=cpp -ffreestanding
    else
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
