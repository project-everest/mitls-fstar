#
# Makefile for FlexTLS*
#

FSTAR_HOME?=../../.fstar
MITLS_HOME?=../..

.PHONY: all lax codegen build world test clean cleanworld


all: build

lax:
# FlexTLS
	@echo $(CYAN)"[Make] Lax-typechecking FlexTLS."$(NORMAL)
	$(FSTAR) \
	$(addprefix --include ,$(FSTAR_INCLUDES)) \
	--explicit_deps \
	--lax \
	$(FSTAR_LIB) $(FSTAR_CONTRIB) $(MITLS_R) $(FLEXTLS)

codegen:
# FlexTLS
	@echo $(CYAN)"[Make] Lax-extracting FlexTLS."$(NORMAL)
	@mkdir -p $(PATH_ML)
	@$(FSTAR) \
	--odir $(PATH_ML) \
	$(addprefix --include ,$(FSTAR_INCLUDES)) \
	$(addprefix --codegen-lib ,$(FSTAR_CODEGENLIB)) \
	$(addprefix --no_extract ,$(FSTAR_NOEXTRACT) $(FSTAR_LIB:.fst=) $(FSTAR_CONTRIB:.fst=) $(MITLS:.fst=) $(MITLS:.p.fst=)) \
	--explicit_deps \
	--lax \
	--codegen OCaml \
	$(FSTAR_LIB) $(FSTAR_CONTRIB) $(MITLS_R) $(FLEXTLS)

build:
# FlexTLS
	@$(MAKE) lax
	@$(MAKE) codegen

world:
# F*
	@echo $(CYAN)"[Make] Compiling F*."$(NORMAL)
	@$(MAKE) -C $(FSTAR_HOME)/src/ocaml-output
# miTLS
	@echo $(CYAN)"[Make] Verifying miTLS."$(NORMAL)
	@$(MAKE) tls-ver -C ../tls
	@echo $(CYAN)"[Make] Lax-typechecking miTLS."$(NORMAL)
	@$(MAKE) tls-lax -C ../tls
	@echo $(CYAN)"[Make] Extracting miTLS."$(NORMAL)
	@$(MAKE) tls-gen -C ../tls
# FlexTLS
	@$(MAKE) build

test:
# Create test executable
	$(OCAML) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) $(MODULES_CMX) -I test test/main.ml -o flextest.out

clean:
# Clean FlexTLS
	@echo $(CYAN)"[Make] Clean FlexTLS."$(NORMAL)
	rm -rf ml/ build/ *.ml *.p.* *.cm* *.o *~ *.out
	(cd test; rm -rf *.p.* *.cm* *.o *~ *.out)

cleanworld:
# Clean F*
	@echo $(CYAN)"[Make] Clean F*."$(NORMAL)
	$(MAKE) clean -C $(FSTAR_HOME)/src
# Clean MiTLS
	@echo $(CYAN)"[Make] Clean MiTLS."$(NORMAL)
	$(MAKE) clean -C $(MITLS_HOME)/src/tls
# Clean FlexTLS
	$(MAKE) clean


# Paths
PATH_ML= ./ml
PATH_BUILD= ./build

# FlexTLS
FLEXTLS= FlexTLS.Types.fst FlexTLS.Constants.fst

# F* includes
FSTAR_INCLUDES= \
$(FSTAR_HOME)/lib \
$(FSTAR_HOME)/contrib/Platform/fst \
$(FSTAR_HOME)/contrib/CoreCrypto/fst

# F* libraries
FSTAR_LIB= \
FStar.Ghost.fst \
FStar.FunctionalExtensionality.fst \
FStar.Classical.fst \
FStar.Set.fst \
FStar.Heap.fst \
FStar.Map.fst \
FStar.List.Tot.fst \
FStar.HyperHeap.fsti \
stHyperHeap.fst \
allHyperHeap.fst \
FStar.Monotonic.RRef.fst \
FStar.Char.fsti \
FStar.String.fsti \
FStar.List.fst \
FStar.ListProperties.fst \
FStar.Seq.fst \
FStar.SeqProperties.fst \
FStar.IO.fsti

# Contrib librairies
FSTAR_CONTRIB= \
Platform.Bytes.fst \
Platform.Date.fst \
Platform.Error.fst \
Platform.Tcp.fst \
CoreCrypto.fst \
DHDB.fst

# F* codegen lib (--codegen-lib)
FSTAR_CODEGENLIB= \
CoreCrypto \
Platform \
Classical \
SeqProperties \
HyperHeap

# No Extract (--no_extract)
FSTAR_NOEXTRACT= \
FStar.All \
FStar.List \
FStar.Heap \
FStar.Set \
FStar.ST \
FStar.HyperHeap \
FStar.IO \
SessionDB \
DHDB \
CoreCrypto \
Cert \
Handshake

# MiTLS files
MITLS= \
TLSError.fst \
TLSConstants.fst \
Nonce.fst \
RSAKey.fst \
DHGroup.p.fst \
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
Record.fst \
TLSPRF.fst \
PRF.p.fst \
TLSExtensions.p.fst \
HandshakeMessages.fst \
Handshake.fst

MITLS_R= $(addprefix $(MITLS_HOME)/src/tls/,$(MITLS))


# F* and OCaml

FSTAR= $(FSTAR_HOME)/bin/fstar.exe
FSTAR_OPTIONS= #--universes

OCAML= ocamlfind ocamlopt
OCAML_OPTIONS= -package batteries,stdint,fileutils,sqlite3 -linkpkg -g -thread

OCAML_INCLUDE_PATHS= $(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml/hyperheap $(FSTAR_HOME)/lib/ml $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml/db)


MAKE= make
NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
