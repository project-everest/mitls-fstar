# A revamped Makefile inspired from HACL
# --------------------------------------

all: compile-all

SHELL		= /bin/bash

ifeq ($(shell uname -s),Darwin)
  ifeq (,$(shell which gsed))
    $(error gsed not found; try brew install gnu-sed)
  endif
  SED := gsed
  ifeq (,$(shell which gtime))
    $(error gtime not found; try brew install gnu-time)
  endif
  TIME := gtime
else
  SED := sed
  TIME := /usr/bin/time
endif

include Makefile.common

# Flat directory structure for miTLS
FSTAR_ROOTS	= $(wildcard *.fst *.fsti)

OUTPUT_DIR	= obj


##########################
# Pretty-printing helper #
##########################

SHELL=/bin/bash

to-obj-dir = $(addprefix $(OUTPUT_DIR)/,$(notdir $1))

# A helper to generate pretty logs, callable as:
#   $(call run-with-log,CMD,TXT,STEM)
#
# Arguments:
#  CMD: command to execute (may contain double quotes, but not escaped)
#  TXT: readable text to print out once the command terminates
#  STEM: path stem for the logs, stdout will be in STEM.out, stderr in STEM.err, CMD in STEM.cmd
ifeq (,$(NOSHORTLOG))
run-with-log = \
  @echo "$(subst ",\",$1)" > $3.cmd; \
  $(TIME) -q -f '%E' -o $3.time sh -c "$(subst ",\",$1)" > $3.out 2> >( tee $3.err 1>&2 ); \
  ret=$$?; \
  time=$$(cat $3.time); \
  if grep -q "admit_smt_queries true" $3.cmd; then \
    admitted=" (ADMITTED)"; \
  fi; \
  if [ $$ret -eq 0 ]; then \
    echo -e "$2\033[31m$$admitted\033[0m, $$time"; \
  else \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    echo -e "\033[31mFatal error while running\033[0m: $1"; \
    echo -e "\033[31mFailed after\033[0m: $$time"; \
    echo -e "\033[36mFull log is in $3.{out,err}, see excerpt below\033[0m:"; \
    tail -n 20 $3.err; \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    false; \
  fi
else
run-with-log = $1
endif

#########
# FStar #
#########

FSTAR_HINTS ?= --use_hints --use_hint_hashes --record_hints

# 272: top-level bindings must be total
# 247: checked file not written because some of its dependencies...
# 241: corrupt cache file AND stale cache file (argh!) we wish to make the
#      former fatal, and the latter non-fatal if it's the file we're about to
#      verify... see https://github.com/FStarLang/FStar/issues/1652
FSTAR_NO_FLAGS = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_HINTS) \
  --odir $(OUTPUT_DIR) --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport Hacl EverCrypt Vale LowParse LowParseWriters Lib Spec Meta -FStar.Old.Endianness -FStar.Test -C.Compat' \
  --warn_error '+241@247-272+285' \
  --cache_dir $(OUTPUT_DIR)

FSTAR = $(FSTAR_NO_FLAGS) $(OTHERFLAGS)


########################
# Parser re-generation #
########################

.PHONY: parsers
parsers:
	$(MAKE) -C ../parsers


##########
# Depend #
##########


ifndef NODEPEND
ifndef MAKE_RESTARTS
# Note that the dependency is marked as .PHONY which forces re-generation of
# .depend no matter what. (Achieved via .FORCE in the HACL* Makefile.)
.depend: parsers
	@echo "⚠ Starting dependency analysis... may take a couple minutes. Remember to run subsequent builds with NODEPEND=1 !"
	$(call run-with-log,\
	  $(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) \
	    > $@ \
	  ,[DEPEND],$(call to-obj-dir,$@))
endif
endif

prune-dep-graph: dep.graph
	cat dep.graph | grep -v fstar_| grep -v prims | grep -v parsers_ | grep -v lowstar_ | grep -v lowparse_ | grep -v evercrypt | grep -v hacl  | grep -v vale | grep -v lib_ | grep -v spec_ | grep -v tlsconstants | grep -v mem | grep -v tls_result |  grep -v debug | grep -v flags | grep -v tlsinfo | grep -v mitls_repr | grep -v hashing_spec | grep -v declassify | grep -v handshakemessages | grep -v format_ | grep -v tls_tracing | grep -v parse | grep -v _crf | grep -v "\"c_" | grep -v "\"crypto_" | grep -v meta_ | grep -v "\"tls_handshake_transcript\" ->" | grep -v "\"aeadprovider\" ->" | grep -v digraph | sort -u > dep.graph.tmp
	echo "digraph {" > quic-dep.graph
	cat dep.graph.tmp >> quic-dep.graph
	echo "If you have GraphViz, run 'fdp -Tpng -oquic-dep.png quic-dep.graph'"

quic-dep-graph: parsers
	$(FSTAR_NO_FLAGS) --dep graph QUIC.fst
	$(MAKE) prune-dep-graph
# Known targets that don't need to trigger dependency regeneration
ifeq ($(MAKECMDGOALS),clean)
  SKIPDEPEND=1
else ifneq ($(MAKECMDGOALS),$(filter-out %.fsti-in %.fst-in,$(MAKECMDGOALS)))
  SKIPDEPEND=1
endif

ifndef SKIPDEPEND
include .depend
endif


#############################
# Verification & extraction #
#############################

hints:
	mkdir -p $@

ifndef VERIFY_PARSERS
$(OUTPUT_DIR)/Parsers_%.krml \
$(OUTPUT_DIR)/Parsers.%.checked: FSTAR_FLAGS=--admit_smt_queries true \
  --__temp_fast_implicits
$(OUTPUT_DIR)/Parsers_%.krml \
$(OUTPUT_DIR)/Parsers.%.checked: FSTAR_HINTS=
endif

%.checked: FSTAR_FLAGS=
%.checked: | hints
	$(call run-with-log,\
	  $(FSTAR) $< $(FSTAR_FLAGS) \
	    --hint_file hints/$(notdir $*).hints \
	    && \
	    touch -c $@ \
	  ,[VERIFY] $(notdir $*),$(call to-obj-dir,$@))

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(call run-with-log,\
	  $(FSTAR) --codegen Kremlin \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<)) && \
	  touch $@ \
	  ,[EXTRACT-KRML] $*,$@)


#############################
# KreMLin and C compilation #
#############################

compile-all: compile-compact compile-compact-msvc compile-test

KRML = $(KREMLIN_HOME)/krml

HAND_WRITTEN_C_FILES = $(wildcard cstubs/*.c)
HAND_WRITTEN_H_FILES = $(wildcard cstubs/*.h) ../../libs/ffi/mitlsffi.h ../pki/mipki.h

HAND_WRITTEN_FILES = $(HAND_WRITTEN_C_FILES) $(HAND_WRITTEN_H_FILES)

# Notes:
# - Token.UF1CMA does not extract
# - AEAD.Pkg does not extract (type-checks against a fictitious AEAD interface)
# - KreMLin bug in anonymous unions, hence the -fno-anonymous-unions
# - many void* pointers being assigned due to debug flags; is the code even
#   runnable without debug?
# - spurious error: StreamAE.c: In function ‘StreamAE_decrypt’:
#    StreamAE.c:255:13: error: ‘*((void *)&f1+1)’ may be used uninitialized in
#    this function [-Werror=maybe-uninitialized]
# - forcing Parsers.ClientHello to remain visible to support linkage with the
#   test later on; eventually, we can remove the left-hand side of that bundle

DEBUG_FLAGS= -DDEBUGFLAGS_DEBUG,-DDEBUGFLAGS_DEBUG_CDH,-DDEBUGFLAGS_DEBUG_EPOCHS,-DDEBUGFLAGS_DEBUG_FFI,-DDEBUGFLAGS_DEBUG_HS,-DDEBUGFLAGS_DEBUG_HSL,-DDEBUGFLAGS_DEBUG_KS,-DDEBUGFLAGS_DEBUG_NGO,-DDEBUGFLAGS_DEBUG_QUIC,-DDEBUGFLAGS_DEBUG_RECORD,-DDEBUGFLAGS_DEBUG_TLS,-DDEBUGFLAGS_DEBUG_AEP

KRML_OPTS = \
  -skip-compilation \
  -silent \
  -warn-error -9-7-6@4-14-15+11-20 \
  -add-include '"kremlin/internal/compat.h"' \
  -ccopts -Wno-type-limits,-Wno-unused,-Wno-uninitialized \
  -ccopts $(DEBUG_FLAGS) \
  -fnoanonymous-unions -fparentheses -fno-shadow -fcurly-braces \
  -drop DebugFlags \
  -library EverCrypt,EverCrypt.* \
  -no-prefix MITLS.Init

KRML_FLAGS = \
  $(KRML_OPTS) \
  -add-early-include '"log_to_choice.h"' \
  -bundle 'EverCrypt,EverCrypt.\*[rename=EverCrypt]' \
  -bundle 'Vale.*,Hacl.*[rename=Unused1]' \
  -bundle 'LowParse.\*,LowParseWrappers,LowParseWriters,LowParseWriters.\*[rename=LowParse]' \
  -bundle 'Format.\*' \
  -bundle 'FStar.\*,LowStar.\*,C,C.\*[rename=Mitls_Kremlib]' \
  -bundle 'Parsers.ClientHello=Parsers.\*,ParsersAux.\*[rename=Parsers]' \
  -bundle 'Spec.\*' \
  -bundle 'Test.\*' \
  -bundle 'Meta.\*' \
  -bundle Lib.*[rename=Hacl_Lib] \
  -bundle TLSConstants=QD.TLS_protocolVersion,List.Helpers \
  -bundle Hashing=Hashing.Spec,Hashing,Hashing.CRF,HMAC,HKDF,HMAC.UFCMA \
  -bundle 'TLS.Handshake=TLS.Handshake.\*,Old.HMAC.UFCMA,Old.Epochs,Old.KeySchedule[rename=Handshake]' \
  -bundle StatefulLHAE=AEAD_GCM,LHAEPlain,StatefulPlain \
  -bundle StreamPlain+StreamAE=[rename=StreamAE] \
  -bundle TLS.Curve25519+DHGroup+ECGroup+CommonDH=[rename=CommonDH] \
  -bundle Content=DataStream \
  -bundle Record+StAE=Transport,StreamDeltas[rename=Record] \
  -bundle PMS=RSAKey,TLSPRF \
  -bundle MITLS.Repr.*[rename=Reprs] \
  -bundle Buffer.Utils,Crypto.Indexing,Crypto.Plain,Crypto.Symmetric.Bytes[rename=Crypto_Plain] \
  -bundle Flags,Flag,TLSInfoFlags[rename=Flags] \
  -bundle 'Model,Model.\*[rename=Unused]' \
  -bundle 'Token.UF1CMA,AEAD,AEAD.Pkg'

BUILD_FILES=dist/Makefile $(wildcard dist/libmitls_*_script)

ALL_KRML_FILES := $(filter-out $(OUTPUT_DIR)/Negotiation_Writers_LayeredEffects.krml $(OUTPUT_DIR)/Negotiation_Writers_Sealed.krml,$(ALL_KRML_FILES))

.PHONY: compile-%
compile-%: $(BUILD_FILES) dist/%/Makefile.basic
	[ "$*" != "test" ] && cp $(BUILD_FILES) dist/$*/ || true
	$(MAKE) -C dist/$*

compile-test: compile-compact

dist/compact-msvc/Makefile.basic: KRML_FLAGS += -falloca -ftail-calls

.PRECIOUS: dist/%/Makefile.basic

dist/%/Makefile.basic: $(ALL_KRML_FILES)
	mkdir -p $(dir $@)
	cp $(HAND_WRITTEN_FILES) $(dir $@)
	for f in \
	  $(filter %.krml,$^) \
	  $(notdir $(HAND_WRITTEN_C_FILES)) \
	; do echo $$f ; done > $@.rsp
	$(KRML) $(KOPTS) $(KRML_FLAGS) \
	  @$@.rsp \
	  -tmpdir $(dir $@)  \
	  -o libmitls.a
	rm -f $@.rsp

# Comma-separated list of miTLS modules (because we still don't have a TLS
# namespace).
MITLS_FSTS	:= $(patsubst %.fst,%,$(filter-out Test Test.%,$(wildcard *.fst)))
MITLS_MODULES	:= $(shell echo $(MITLS_FSTS) | tr ' ' ',')

dist/test/Makefile.basic: $(ALL_KRML_FILES)
	for f in \
	  $(filter %.krml,$^) \
	; do echo $$f ; done > $@.rsp
	$(KRML) $(KRML_OPTS) \
	  @$@.rsp \
	  -no-prefix Test.Main \
	  -bundle 'Test.Main=Test.*[rename=Test]' \
	  -bundle '\*[rename=Test_miTLS]' \
	  -library $(MITLS_MODULES) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -silent \
	  -warn-error -4-6+9 \
	  -o test.exe
	rm -f $@.rsp

#########
# Tests #
#########

.PHONY: test
test: compile-test
	$(MAKE) -C dist/test test

#####################
# Verification only #
#####################

# NOTE: this rule is subsumed by $(ALL_KRML_FILES) so it need not be
# explicitly added to `all`.

.PHONY: verify-all
verify-all: $(ALL_CHECKED_FILES)
