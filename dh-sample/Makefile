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
.PHONY: all verify verify-symbolic-lift verify-symbolic-invariant verify-symbolic-security clean check-admits check-forbidden check-symbolic-forbidden stats help

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

# Verify all modules (ALL_CHECKED_FILES is defined in .depend).  The symbolic
# composed-system development (SYMBOLIC_CHECKED_FILES) is added as an extra
# prerequisite AFTER `-include .depend.symbolic` below (that variable is not yet
# defined at this point), so the single `make verify` covers the DY-free spec +
# Pulse impl AND the DY*-backed symbolic product-system simulation.
verify: $(ALL_CHECKED_FILES)
	@echo "✅ All DH sample spec + impl + symbolic system modules verified successfully"

# ── Admit / forbidden-construct hygiene ────────────────────────────
check-admits:
	@echo "Checking for proof-local admits/assumes..."
	@if grep -rn "admit ()\|admit()\|assume val\|assume (\|assert_norm" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null; then \
		echo "❌ ERROR: Found admit/assume/assert_norm!"; exit 1; \
	else echo "✅ None found"; fi
	@test -f $(SPEC_DIR)/DH.Sample.Crypto.fsti
	@test ! -e $(SPEC_DIR)/DH.Sample.Crypto.fst
	@echo "ℹ️  DH.Sample.Crypto.fsti is the intentional unimplemented cryptographic trust boundary"

check-forbidden:
	@echo "Checking that no DY / iso_dh imports are present in the DY-free spec/impl..."
	@if grep -rn "DY\.\|dolev-yao\|iso_dh" $(SPEC_DIR) $(IMPL_DIR) --exclude-dir=symbolic 2>/dev/null; then \
		echo "❌ ERROR: Found forbidden dependency!"; exit 1; \
	else echo "✅ No forbidden DY dependencies in the DY-free spec/impl"; fi

# ── Statistics ─────────────────────────────────────────────────────
stats:
	@echo "=== DH Sample Statistics ==="
	@echo "Spec files: $(words $(SPEC_FILES))"
	@echo "Impl files: $(words $(IMPL_FILES))"
	@wc -l $(SPEC_DIR)/*.fst $(IMPL_DIR)/*.fst 2>/dev/null | tail -1 || echo "  0 total"

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(SYM_CACHE_DIR)
	rm -f .depend .depend.symbolic
	@echo "Cleaned build artifacts"

help:
	@echo "DH Sample - Makefile targets:"
	@echo "  make            - Verify everything: DY-free spec + Pulse impl + symbolic system (default)"
	@echo "  make verify     - Verify all modules incl. the symbolic composed-system simulation (supports -j)"
	@echo "  make verify-symbolic-lift - Verify only the symbolic development (DY* core)"
	@echo "  make verify-symbolic-invariant - Verify the protocol_invariants / product_invariant milestone"
	@echo "  make verify-symbolic-security - Verify the authentication / secrecy security consequences milestone"
	@echo "  make -j$$(nproc)     - Parallel verification with all available cores"
	@echo "  make check-admits    - Ensure no admit/assume/assert_norm in spec/impl"
	@echo "  make check-forbidden - Ensure DY-free spec/impl has no DY/iso_dh dependency"
	@echo "  make check-symbolic-forbidden - Ensure symbolic uses DY* core, never an example"
	@echo "  make stats      - Show line counts"
	@echo "  make clean      - Remove build artifacts"

# ═══════════════════════════════════════════════════════════════════
# Symbolic (Dolev-Yao / DY*-backed) incremental verification
# ═══════════════════════════════════════════════════════════════════
# The symbolic lifting development under spec/symbolic depends on the DY* CORE
# library (third_party/dolev-yao-star-extrinsic/src/core, consumed via its
# committed cache) IN ADDITION to the standalone dh-sample pure spec and the
# neutral common framework.  It has a SEPARATE dependency scan, flag set and
# cache directory so it never perturbs the DY-free spec/impl build above.  It
# depends ONLY on DY* CORE and never on any DY* example (examples/iso_dh).

DY_HOME      ?= ../third_party/dolev-yao-star-extrinsic
DY_CORE_DIR   = $(DY_HOME)/src/core
DY_CACHE_DIR  = $(DY_HOME)/cache
SYMBOLIC_DIR  = $(SPEC_DIR)/symbolic
SYM_CACHE_DIR = _symcache

SYMBOLIC_INCLUDES = \
  --include ../common \
  --include $(SPEC_DIR) \
  --include $(SYMBOLIC_DIR) \
  --include $(DY_CORE_DIR) \
  --include $(DY_CACHE_DIR)

SYMBOLIC_FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(SYM_CACHE_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore,DY' \
  --warn_error -321-241-272-288 \
  --report_assumes warn \
  --ext optimize_let_vc \
  $(SYMBOLIC_INCLUDES)

SYMBOLIC_FSTAR = $(FSTAR_EXE) $(SYMBOLIC_FSTAR_FLAGS)

# The DY-free spec + common modules the symbolic development depends on.  The
# Pulse implementation is intentionally NOT among them: the simulation relates
# to the pure state machine only.
SYMBOLIC_SPEC_DEPS = \
  ../common/Common.StateMachine.fst \
  ../common/Common.WireFormat.fst \
  ../common/Common.WireFormatStateMachine.fst \
  ../common/Common.TCP.fsti \
  $(SPEC_DIR)/DH.Sample.Types.fst \
  $(SPEC_DIR)/DH.Sample.Crypto.fsti \
  $(SPEC_DIR)/DH.Sample.Wire.fst \
  $(SPEC_DIR)/DH.Sample.StateMachine.fst \
  $(SPEC_DIR)/DH.Sample.System.fst

SYMBOLIC_SRC = $(wildcard $(SYMBOLIC_DIR)/*.fst $(SYMBOLIC_DIR)/*.fsti)
SYMBOLIC_ALL = $(SYMBOLIC_SPEC_DEPS) $(SYMBOLIC_SRC)

$(SYM_CACHE_DIR):
	@mkdir -p $@

# Separate dependency scan; rename ALL_CHECKED_FILES to SYMBOLIC_CHECKED_FILES so
# it cannot collide with the DY-free build's variable of the same name.
.depend.symbolic: $(SYMBOLIC_ALL) | $(SYM_CACHE_DIR)
	@echo "Generating symbolic dependencies..."
	@$(SYMBOLIC_FSTAR) --dep full $(SYMBOLIC_ALL) --output_deps_to $@.tmp
	@sed 's/ALL_CHECKED_FILES/SYMBOLIC_CHECKED_FILES/g' $@.tmp > $@
	@rm -f $@.tmp

-include .depend.symbolic

# The symbolic checked files are an EXTRA prerequisite of the top-level `verify`
# target.  This prerequisite-only line is placed AFTER `-include .depend.symbolic`
# (which defines SYMBOLIC_CHECKED_FILES); listing it on the earlier `verify:` rule
# would expand to nothing because the variable is not yet defined there.  So the
# single `make verify` builds the DY-free spec + Pulse impl AND the symbolic system.
verify: $(SYMBOLIC_CHECKED_FILES)

$(SYM_CACHE_DIR)/%.checked: | $(SYM_CACHE_DIR)
	@echo "Verifying (symbolic) $<"
	@$(SYMBOLIC_FSTAR) $<
	@touch $@

# The FIRST symbolic milestone: verify the whole symbolic lifting development
# (Terms, Product, Lifting, Provenance) plus its DY-free dependencies,
# incrementally and in parallel (supports -j).
verify-symbolic-lift: $(SYMBOLIC_CHECKED_FILES)
	@echo "✅ DH sample symbolic lifting milestone verified successfully"

# The SECOND symbolic milestone: verify the protocol-specific DY* CORE
# `protocol_invariants` instance and the combined coherence + trace-invariant
# development (DH.Sample.Symbolic.Invariant), on top of Terms/Product/Lifting/
# Provenance.  This is the module that installs `product_invariant`, proves
# `product_step_preserves_invariant` (the case-exhaustive one-step
# preservation theorem) and the reachable-state theorem.  Depends on the same
# incremental `.checked` cache as `verify-symbolic-lift`, so it only pays for
# the ONE extra module when the rest is already up to date.
verify-symbolic-invariant: check-admits check-symbolic-forbidden $(SYM_CACHE_DIR)/DH.Sample.Symbolic.Invariant.fst.checked
	@echo "✅ DH sample symbolic protocol-invariant milestone verified successfully"

# The THIRD symbolic milestone: verify the genuine SECURITY CONSEQUENCES the
# installed compromise-aware invariant buys — mutual authentication, session-key
# secrecy / agreement, the end-to-end theorem from a concrete system execution,
# and the honest-run non-vacuity witness (DH.Sample.Symbolic.Security), on top of
# Terms/Product/Lifting/Provenance/Invariant.  Like the invariant milestone it is
# gated on the admit- and DY*-example-hygiene checks, and depends on the same
# incremental `.checked` cache, so it only pays for the ONE extra module when the
# rest is already up to date.  It is ALSO covered by the top-level `make verify`
# (Security.fst is part of SYMBOLIC_SRC, hence SYMBOLIC_CHECKED_FILES).
verify-symbolic-security: check-admits check-symbolic-forbidden $(SYM_CACHE_DIR)/DH.Sample.Symbolic.Security.fst.checked
	@echo "✅ DH sample symbolic security milestone verified successfully"

# Guard: the symbolic development may use DY* core but never a DY* example.
check-symbolic-forbidden:
	@echo "Checking that symbolic sources use DY* core only..."
	@if grep -rn "iso_dh\|DY\.Example\|DY\.Lib\|examples/" $(SYMBOLIC_DIR) 2>/dev/null; then \
		echo "❌ ERROR: symbolic source references a non-core DY* module/example!"; exit 1; \
	else echo "✅ symbolic sources depend on DY* core only"; fi
