# These are all the known working targets in this file,
# check for regressions & comment about them!
all: mitls-lax
	make -C tls
# TODO compilation to ML & testing

clean:
	rm -rf tls-ml/*.ml tls/*.p.* tls-ml/*.cm* tls-ml/*.o tls-ml/*~ tls-ml/support.ml tls-lax/*.p.*

# ------------------ dependencies on Fstar & its libraries --------------------
ifndef FSTAR_HOME
FSTAR_HOME=../../FStar
endif
STDLIB_ADMITS=Set Map HyperHeap Char Seq
STDLIB=FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.Base.fst FStar.HyperHeap.fsi \
stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.Tot.Properties.fst FStar.List.Tot.fst FStar.List.fst seq.fsi \
FStar.Seq.fst #FStar.Int64.fst
CODEGEN_LIBS=CoreCrypto Platform Classical Seq.Base HyperHeap
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(STDLIB) $(addprefix --codegen-lib , $(CODEGEN_LIBS))

PDIR=$(FSTAR_HOME)/ucontrib/Platform/fst/
PDIR_ML=$(FSTAR_HOME)/ucontrib/Platform/ml/

PLATFORM=$(addprefix $(PDIR)Platform.,Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/ucontrib/CoreCrypto/fst/
CDIR_ML=$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/

CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

LIBFILES = $(PLATFORM) $(CRYPTO) $(DHDB)

# admitting things verified elsewhere; redundant with lax and --verify_module?
# No, --verify_module overrides --admit_fsi
ADMITTED=$(addprefix --admit_fsi ,$(addprefix FStar., $(STDLIB_ADMITS)) SessionDB UntrustedCert DHDB CoreCrypto Cert StatefulLHAE Handshake)

# these files should lax-typecheck in F pls document the purpose of the rest
TLSLAX= $(addprefix tls-lax/MiTLS.,TLSError.fst Nonce.p.fst TLSConstants.fst \
  RSAKey.fst DHGroup.p.fst ECGroup.p.fst CommonDH.p.fst PMS.p.fst HASH.fst \
	HMAC.p.fst  Sig.p.fst UntrustedCert.p.fsti Cert.p.fsti TLSInfo.fst \
	TLSExtensions.p.fst TLSPRF.p.fst Range.p.fst DataStream.p.fst \
	AppFragment.p.fst HSFragment.p.fst TLSFragment.p.fst StatefulPlain.p.fst \
	LHAEPlain.p.fst MAC_SHA256.p.fst MAC_SHA1.p.fst MAC.p.fst Encode.p.fst \
	ENC.p.fst AEAD_GCM.p.fst LHAE.p.fst StatefulLHAE.p.fst Record.p.fst \
	Alert.p.fst PRF.p.fst KEF.p.fst DH.p.fst RSA.p.fst SessionDB.p.fsti \
	HandshakeMessages.p.fst Handshake.p.fst AppData.p.fst Dispatch.p.fst TLS.fst)

mitls-lax: $(LIBFILES) $(TLSLAX)
	$(FSTAR) --lax --debug yes $(ADMITTED) $^
