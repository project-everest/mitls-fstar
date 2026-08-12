EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
export PATH := $(Z3_DIR):$(PATH)

CACHE_DIR = _cache
SPEC_DIR = spec
DY_DIR = $(SPEC_DIR)/dy
DY_HOME ?= ../third_party/dolev-yao-star-extrinsic
DY_CORE_DIR = $(DY_HOME)/src/core
DY_CACHE_DIR = $(DY_HOME)/cache

COMMON_FILES = \
	../common/Common.StateMachine.fst \
	../common/Common.Protocol.Labelled.fst \
	../common/Common.Protocol.System.fst \
	../common/Common.Protocol.Interpretation.fst

SPEC_FILES = \
	$(SPEC_DIR)/NSL.Sample.Types.fst \
	$(SPEC_DIR)/NSL.Sample.Wire.fst \
	$(SPEC_DIR)/NSL.Sample.Crypto.fsti \
	$(SPEC_DIR)/NSL.Sample.StateMachine.fst \
	$(SPEC_DIR)/NSL.Sample.Protocol.fst

DY_FILES = \
	$(DY_DIR)/NSL.Sample.DY.Terms.fst \
	$(DY_DIR)/NSL.Sample.DY.Profile.fst \
	$(DY_DIR)/NSL.Sample.DY.Model.fst \
	$(DY_DIR)/NSL.Sample.DY.Invariant.fst \
	$(DY_DIR)/NSL.Sample.DY.Coherence.fst \
	$(DY_DIR)/NSL.Sample.DY.Security.fst

ALL_FILES = $(COMMON_FILES) $(SPEC_FILES) $(DY_FILES)

FSTAR_FLAGS = \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached 'Prims,FStar,Pulse,PulseCore,DY' \
	--warn_error -321-241-272-288 \
	--report_assumes warn \
	--ext optimize_let_vc \
	--include ../common \
	--include $(SPEC_DIR) \
	--include $(DY_DIR) \
	--include $(DY_CORE_DIR) \
	--include $(DY_CACHE_DIR)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

.PHONY: all verify verify-core clean check-architecture check-admits check-rlimits

all: verify

.depend: $(ALL_FILES)
	@$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

include .depend

$(CACHE_DIR):
	@mkdir -p $@

$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	@echo "Verifying $<"
	@$(FSTAR) $<
	@touch $@

verify-core: check-architecture check-admits check-rlimits \
	$(filter-out $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(DY_FILES))),$(ALL_CHECKED_FILES))
	@echo "Fresh labelled NSL endpoint architecture verified"

verify: check-architecture check-admits check-rlimits $(ALL_CHECKED_FILES)
	@echo "Fresh labelled NSL architecture and direct DY* proof verified"

check-architecture:
	@test ! -d attic
	@test ! -e $(SPEC_DIR)/NSL.Sample.System.fst
	@test ! -e $(SPEC_DIR)/NSL.Sample.Audit.fst
	@test ! -d $(SPEC_DIR)/symbolic
	@! grep -R "NSL.Sample.System\\|NSL.Sample.Audit\\|NSL.Sample.Symbolic" \
		$(SPEC_DIR) ../common/Common.Protocol.Labelled.fst \
		../common/Common.Protocol.System.fst \
		../common/Common.Protocol.Interpretation.fst
	@! grep -R "nsl_pk\\|DY\\.Example\\|DY\\.Lib\\|examples/" $(DY_DIR)

check-admits:
	@! grep -R -nE 'admit[[:space:]]*[(]|admit1|assume[[:space:]]+val|assert_norm' \
		$(SPEC_DIR) ../common/Common.Protocol.Labelled.fst \
		../common/Common.Protocol.System.fst \
		../common/Common.Protocol.Interpretation.fst

check-rlimits:
	@! grep -R -nE -- '--z3rlimit (1[1-9]|[2-9][0-9]|[1-9][0-9]{2,})' \
		$(SPEC_DIR) ../common/Common.Protocol.Labelled.fst \
		../common/Common.Protocol.System.fst \
		../common/Common.Protocol.Interpretation.fst

clean:
	rm -rf $(CACHE_DIR) _symcache
	rm -f .depend .depend.symbolic
