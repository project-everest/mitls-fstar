# ═══════════════════════════════════════════════════════════════════
# DH Sample: Makefile (pure specification + Pulse implementation)
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental and parallel builds, exactly
# like calc_sample.  This verifies both the pure spec modules under spec/
# and the verified Pulse implementation under impl/ (plus the neutral
# framework modules under ../common that they depend on).  There is no
# extraction step yet.

# ── Toolchain ──────────────────────────────────────────────────────
# Use the same Pulse-capable EverParse/F* toolchain as the root build.
# Override these variables to test with a different compatible toolchain.
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
FSTAR_LIB ?= $(shell $(FSTAR_EXE) --locate_lib)
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR = _cache
SPEC_DIR  = spec
IMPL_DIR  = impl

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore' \
  --warn_error -321-241-272-288 \
  --report_assumes warn \
  --ext optimize_let_vc \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
# The neutral framework modules needed by the spec AND the impl.  The impl
# refines Common.ProtocolImplementation (a Pulse module), so it is added here.
COMMON_FILES = \
  ../common/Common.StateMachine.fst \
  ../common/Common.WireFormat.fst \
  ../common/Common.WireFormatStateMachine.fst \
  ../common/Common.TCP.fsti \
  ../common/Common.ProtocolImplementation.fst
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(SPEC_FILES) $(IMPL_FILES)

# ── Main Targets (MUST come before .depend include) ───────────────
.PHONY: all verify clean check-admits check-forbidden stats help

all: verify

# ── Dependency Analysis ────────────────────────────────────────────
.depend: $(ALL_FILES)
	@echo "Generating dependencies..."
	@$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

-include .depend

# ── Generic Verification Rule ──────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	@echo "Verifying $<"
	@$(FSTAR) $<
	@touch $@

$(CACHE_DIR):
	@mkdir -p $@

# Verify all modules (ALL_CHECKED_FILES is defined in .depend)
verify: $(ALL_CHECKED_FILES)
	@echo "✅ All DH sample spec + impl modules verified successfully"

# ── Admit / forbidden-construct hygiene ────────────────────────────
check-admits:
	@echo "Checking for admits/assumes..."
	@if grep -rn "admit ()\|admit()\|assume val\|assume (\|assert_norm" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null; then \
		echo "❌ ERROR: Found admit/assume/assert_norm!"; exit 1; \
	else echo "✅ None found"; fi

check-forbidden:
	@echo "Checking that no DY / iso_dh imports are present..."
	@if grep -rn "DY\.\|dolev-yao\|iso_dh" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null; then \
		echo "❌ ERROR: Found forbidden dependency!"; exit 1; \
	else echo "✅ No forbidden DY dependencies"; fi

# ── Statistics ─────────────────────────────────────────────────────
stats:
	@echo "=== DH Sample Statistics ==="
	@echo "Spec files: $(words $(SPEC_FILES))"
	@echo "Impl files: $(words $(IMPL_FILES))"
	@wc -l $(SPEC_DIR)/*.fst $(IMPL_DIR)/*.fst 2>/dev/null | tail -1 || echo "  0 total"

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "DH Sample - Makefile targets:"
	@echo "  make            - Verify all spec + Pulse impl modules (default)"
	@echo "  make verify     - Verify all modules (incremental, supports -j)"
	@echo "  make -j$$(nproc)     - Parallel verification with all available cores"
	@echo "  make check-admits    - Ensure no admit/assume/assert_norm"
	@echo "  make check-forbidden - Ensure no DY/iso_dh dependency"
	@echo "  make stats      - Show line counts"
	@echo "  make clean      - Remove build artifacts"
