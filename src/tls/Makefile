# A revamped Makefile inspired from HACL
# --------------------------------------

all: compile

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

MITLS_HOME	?= ../..
FSTAR_HOME	?= $(MITLS_HOME)/../FStar
KREMLIN_HOME	?= $(MITLS_HOME)/../kremlin
HACL_HOME	?= $(MITLS_HOME)/../hacl-star
MLCRYPTO_HOME	?= $(MITLS_HOME)/../MLCrypto
QD_HOME		?= $(MITLS_HOME)/../quackyducky

include $(HACL_HOME)/Makefile.include

INCLUDE_PATHS 	= \
  $(ALL_HACL_DIRS) \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib/compat \
  $(KREMLIN_HOME)/kremlib \
  $(MITLS_HOME)/libs/ffi \
  $(MITLS_HOME)/../quackyducky/src/lowparse \
  $(MITLS_HOME)/src/parsers/generated

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
  if [ $$ret -eq 0 ]; then \
    echo "$2, $$time"; \
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

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDE_PATHS))

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

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDES)


########################
# Parser re-generation #
########################

.PHONY: parsers
parsers:
	$(MAKE) -C ../parsers


##########
# Depend #
##########

.PHONY: depend-warning
depend-warning:
	@echo "⚠ Starting dependency analysis... may take up to ten minutes. Remember to run subsequent builds with NODEPEND=1 !"

ifndef NODEPEND
ifndef MAKE_RESTARTS
# Note that the dependencies are marked as .PHONY which forces re-generation of
# .depend no matter what.
.depend: parsers depend-warning
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

compile: $(ALL_KRML_FILES)
	echo $^
