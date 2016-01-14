# These are all the known working targets in this file,
# check for regressions & comment about them!
all: mitls-ver 
# TODO extend scope of verification
# TODO compilation to ML & testing
# MK removed mitls-ml as strider was failing on it for ages

clean:
	rm -rf *.ml *.p.* *.cm* *.o *~ *.out

# ------------------ dependencies on Fstar & its libraries --------------------
ifndef FSTAR_HOME
FSTAR_HOME=../../../FStar
endif
#STDLIB_ADMITS=Set Map HyperHeap Seq Char SeqProperties
STDLIB_ADMITS=Char HyperHeap Set Map

STDLIB=FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fsi \
stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.fst FStar.ListProperties.fst seq.fsi \
FStar.Seq.fst FStar.SeqProperties.fst #FStar.Int64.fst 
CODEGEN_LIBS=CoreCrypto Platform Classical SeqProperties HyperHeap
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(STDLIB) $(addprefix --codegen-lib , $(CODEGEN_LIBS)) $(OTHERFLAGS)

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

# ------------------------- miTLS* -------------------------------------------
# We try to limit the use of preprocessing, as it is messy.
# Not sure which interfaces we should put in there.

# these files are the stable inputs for verification
TLSVER=TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst Range.fst DataStream.fst Alert.fst Content.fst StreamPlain.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst MAC.fst Encode.fst ENC.fst StatefulLHAE.fsti StatefulLHAE.fst MAC_SHA256.fst MAC_SHA1.fst Handshake.fsti Connection.fst # TLS.fst #the preceding space is significant (see prefix_cfg)
#LHAE.fst --these do not even parse
#Record.fst --this does not lax type-check

#Removed temporarily: StatefulPlain.fsti
#Removed temporarily: TLS.fst

TLSREDUX=TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst \
	DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst \
	UntrustedCert.fsti Cert.fsti TLSInfo.fst TLSExtensions_Redux.p.fst Range.fst \
	DataStream.fst TLSPRF.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst \
	AEAD_GCM.fst StatefulLHAE.fst PRF-redux.p.fst  \
	HandshakeMessages_Redux.fst Handshake_Redux.fst

TLSPARSE=TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst \
	DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst \
	UntrustedCert.fst Cert.fst TLSInfo.fst TLSExtensions_Redux.p.fst \
	HandshakeMessages_Redux.fst

# these files are verified here
VERIFY=TLSError TLSConstants Nonce TLSInfo Range LHAEPlain AEAD_GCM LHAE StatefulLHAE MAC_SHA256 MAC_SHA1 MAC Encode DataStream Alert Content StreamPlain StatefulPlain

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
Encode.fst\
ENC.fst\
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
# the space in calls to prefix_ver and prefix_cfg matters!

# verifying one file within $(TLSVER)
%.fst-ver:
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver, $(basename $@),fst) \
--verify_module $(subst .p,,$(basename $@))

%.fsti-ver:
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver, $(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

%.fst-in:
	@echo $(VERFLAGS) $(STDLIB) $(LIBFILES) $(ADMITTED) $(call prefix_cfg, $(basename $@),fst) \
--verify_module $(subst .p,,$(basename $@))

%.fsti-in:
	@echo $(VERFLAGS) $(STDLIB) $(LIBFILES) $(ADMITTED) $(call prefix_cfg, $(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

# prints build-config block for interactive verification
%.fst-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg, $(basename $@),fst)
	@echo '--*)'

%.fsti-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg, $(basename $@),fsti)
	@echo '--*)'


# verifying everything stable
# Add TLS.fst again when at least it lax type checks
mitls-ver: $(LIBFILES) $(TLSVER)
	$(FSTAR) $(ADMITTED) $(VERFLAGS) $(filter-out TLS.fst,$^) $(addprefix --verify_module ,$(VERIFY))

# going beyond TLSVER, not necessarily working

api-ver: $(LIBFILES) $(TLSVER) TLS.fsti
	$(FSTAR) $(ADMITTED) $(VERFLAGS) $^

test-gcm: $(LIBFILES)
	$(FSTAR) --lax $(ADMITTED) --codegen OCaml --admit_fsi FStar.IO \
	--include $(PDIR) --include $(CDIR) \
	$^ FStar.IO.fsti $(call prefix_ver,AEAD_GCM,fst) StatefulLHAE.fst TestGCM.fst	

test-hmac:$(LIBFILES) TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst MAC_SHA256.fst MAC_SHA1.fst MAC.fst TestMAC.fst
	$(FSTAR) $(ADMITTED) $(VERLAGS) $^

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
	$(EXTRA_PATH) ./test.out

# ------------------ preprocessing :( -----------------------

# preprocessing is still a necessary pain; pls remove files below when possible
# Nonce still has an #ideal flag
# many files have __SOURCE_FILE__ __LINE__ macros
TLS_PP_FILES= TLSExtensions PMS DHGroup Sig PRF-redux TLSExtensions_Redux ENC
# DHGroup.p.fst PMS.p.fst \
	TLSExtensions.p.fst TLSPRF.p.fst \
	HSFragment.p.fst TLSFragment.p.fst StatefulPlain.p.fst \
	LHAEPlain.p.fst MAC_SHA256.p.fst MAC_SHA1.p.fst MAC.p.fst \
	ENC.fst AEAD_GCM.p.fst LHAE.p.fst \
	PRF.p.fst KEF.p.fst DH.p.fst RSA.p.fst SessionDB.p.fsti \
	HandshakeMessages.p.fst Handshake.p.fst

# Target to generate preprocessed files for atom-interactive
pp:: $(addsuffix .p.fst, $(TLS_PP_FILES))

ifeq ($(OS),Windows_NT)
    EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    CPP=cpp #-ffreestanding
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
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
