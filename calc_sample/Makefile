# ═══════════════════════════════════════════════════════════════════
# Calculator Sample: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental and parallel builds

# ── Toolchain ──────────────────────────────────────────────────────
FSTAR_EXE ?= fstar.exe

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR = _cache
SPEC_DIR  = spec
IMPL_DIR  = impl

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore' \
  --warn_error -321-241-272-288 \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(SPEC_FILES) $(IMPL_FILES)

# ── Main Targets (MUST come before .depend include) ───────────────
.PHONY: all verify clean check-admits stats help

# Default target (defined before including .depend to ensure it's the default)
all: verify

# ── Dependency Analysis ────────────────────────────────────────────
# Generate dependencies using F*'s --dep full
.depend: $(ALL_FILES)
	@echo "Generating dependencies..."
	@$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

# Include generated dependencies (defines ALL_CHECKED_FILES and .checked rules)
-include .depend

# ── Generic Verification Rules ────────────────────────────────────
# Generic rule: verify any .fst/.fsti file to produce .checked
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	@echo "Verifying $<"
	@$(FSTAR) $<
	@touch $@

$(CACHE_DIR):
	@mkdir -p $@

# Verify all modules (ALL_CHECKED_FILES is defined in .depend)
verify: $(ALL_CHECKED_FILES)
	@echo "✅ All modules verified successfully"

# Check for admits
check-admits:
	@echo "Checking for admits..."
	@if grep -rn "admit()" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null; then \
		echo "❌ ERROR: Found admits!"; \
		exit 1; \
	else \
		echo "✅ No admits found"; \
	fi

# Statistics
stats:
	@echo "=== Calc Sample Statistics ==="
	@echo "Source files:  $(words $(ALL_FILES))"
	@echo "Spec files:    $(words $(SPEC_FILES))"
	@echo "Impl files:    $(words $(IMPL_FILES))"
	@echo ""
	@echo "Lines of code:"
	@wc -l $(SPEC_DIR)/*.fst $(IMPL_DIR)/*.fst 2>/dev/null | tail -1 || echo "  0 total"
	@echo ""
	@echo "Admits:"
	@if grep -r "admit()" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null | wc -l | grep -q "^0"; then \
		echo "  0 ✅"; \
	else \
		grep -r "admit()" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null | wc -l; \
	fi

# Clean build artifacts
clean:
	rm -rf $(CACHE_DIR)
	rm -f .depend
	rm -f $(SPEC_DIR)/*.checked $(IMPL_DIR)/*.checked
	@echo "Cleaned build artifacts"

# Help
help:
	@echo "Calculator Sample - Makefile targets:"
	@echo ""
	@echo "  make all          - Verify all modules (default)"
	@echo "  make verify       - Verify all modules (incremental, supports -j)"
	@echo "  make check-admits - Check for admits (should be 0)"
	@echo "  make stats        - Show project statistics"
	@echo "  make clean        - Remove build artifacts"
	@echo "  make help         - Show this help"
	@echo ""
	@echo "Parallel build:"
	@echo "  make -j4          - Build with 4 parallel jobs"
	@echo ""
	@echo "Incremental builds: Only changed files and their dependents are reverified"
	@echo "Expected result: All modules verify with 0 admits"
