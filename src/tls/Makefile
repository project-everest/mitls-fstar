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
  --already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport Hacl EverCrypt Vale LowParse Lib Spec -FStar.Old.Endianness -FStar.Test -C.Compat' \
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

HAND_WRITTEN_FILES = $(HAND_WRITTEN_C_FILES) $(HAND_WRITTEN_H_FILES)

# Notes:
# - Token.UF1CMA does not extract
# - AEAD.Pkg does not extract (type-checks against a fictitious AEAD interface)
# - KreMLin bug in anonymous unions
# - many void* pointers being assigned due to debug flags...
KRML_FLAGS = \
  -skip-compilation \
  -silent \
  -warn-error -9-7-6@4-14-15+11-20 \
  -add-include '"kremlin/internal/compat.h"' \
  -ccopts -Wno-type-limits,-Wno-unused \
  -fnoanonymous-unions -fparentheses -fno-shadow -fcurly-braces \
  \
  -drop DebugFlags \
  -library EverCrypt,EverCrypt.* \
  -bundle 'EverCrypt,EverCrypt.\*[rename=EverCrypt]' \
  -bundle 'Vale.*,Hacl.*[rename=Unused1]' \
  -bundle 'LowParse.\*,LowParseWrappers[rename=LowParse]' \
  -bundle 'Format.\*' \
  -bundle 'FStar.\*,LowStar.\*,C,C.\*[rename=Mitls_Kremlib]' \
  -bundle 'Parsers=Parsers.\*,ParsersAux.\*' \
  -bundle 'Spec.\*' \
  -bundle Lib.*[rename=Hacl_Lib] \
  -bundle TLSConstants=TLSConstants,QD.TLS_protocolVersion,List.Helpers \
  -bundle Hashing=Hashing.Spec,Hashing,Hashing.CRF,HMAC,HKDF,HMAC.UFCMA \
  -bundle Old.Handshake=Old.HMAC.UFCMA,Old.Epochs,Old.KeySchedule,Old.Handshake \
  -bundle StatefulLHAE=AEAD_GCM,LHAEPlain,StatefulPlain,StatefulLHAE \
  -bundle StreamAE=StreamPlain,StreamAE \
  -bundle CommonDH=TLS.Curve25519,DHGroup,ECGroup,CommonDH \
  -bundle Content=Content,DataStream \
  -bundle Record=Record,StAE,Transport,StreamDeltas \
  -bundle PMS=PMS,RSAKey,TLSPRF \
  -bundle Crypto.Plain=Buffer.Utils,Crypto.Indexing,Crypto.Plain,Crypto.Symmetric.Bytes \
  -bundle Flags=Flags,Flag,TLSInfoFlags \
  -bundle 'Model,Model.\*[rename=Unused]' \
  -bundle 'Token.UF1CMA,AEAD,AEAD.Pkg'

dist/compact-msvc/Makefile.basic: KRML_FLAGS += -falloca -ftail-calls

compile-%: dist/%/Makefile.basic
	$(MAKE) -C $(dir $^) -f Makefile.basic

.PRECIOUS: dist/%/Makefile.basic

dist/%/Makefile.basic: $(ALL_KRML_FILES)
	mkdir -p $(dir $@)
	#cp $(HAND_WRITTEN_FILES) $(dir $@)
	$(KRML) $(KOPTS) $(KRML_FLAGS) \
	  $(filter %.krml,$^) \
	  -tmpdir $(dir $@)  \
	  $(notdir $(HAND_WRITTEN_C_FILES)) \
	  -o libmitls.a

dist/test/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) \
	  -bundle 'Test,Test.*=[rename=Test]' \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -silent \
	  -warn-error -4-6+9 \
	  -o test.exe


#########
# Tests #
#########

ifeq ($(OS),Windows_NT)
  LD_EXTRA = PATH="$(MITLS_HOME)/src/tls/dist/compact:$$PATH"
else ifeq ($(shell uname -s),Darwin)
  LD_EXTRA = DYLD_LIBRARY_PATH="$(MITLS_HOME)/src/tls/dist/compact"
else
  LD_EXTRA = LD_LIBRARY_PATH="$(MITLS_HOME)/src/tls/dist/compact"
endif

test: compile-test
	$(LD_EXTRA) dist/test/test.exe

