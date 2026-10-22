# ═══════════════════════════════════════════════════════════════════
# Calculator Sample: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental and parallel builds

# ── Toolchain ──────────────────────────────────────────────────────
# Use the same Pulse-capable EverParse/F* toolchain as the root build.
# Override these variables to test with a different compatible toolchain.
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
FSTAR_LIB ?= $(shell $(FSTAR_EXE) --locate_lib)
export PATH := $(Z3_DIR):$(PATH)

# Z3 version used by every F* invocation; see the root Makefile for why 4.15.3.
# Pinned in scripts/z3-version.txt at the repo root -- single source of truth
# shared with the root Makefile, scripts/install-z3.sh and the CI dev-container
# cache key.
Z3_VERSION_FILE ?= ../scripts/z3-version.txt
Z3_VERSION ?= $(strip $(shell cat $(Z3_VERSION_FILE)))
ifeq ($(Z3_VERSION),)
$(error Could not read the pinned Z3 version from $(Z3_VERSION_FILE))
endif

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR = _cache
SPEC_DIR  = spec
IMPL_DIR  = impl
EXTERN_DIR = ../src/impl/extern
OUTPUT_DIR = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(EXTERN_DIR) \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

FSTAR_FLAGS = \
  --z3version $(Z3_VERSION) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore' \
  --warn_error -321-241-272-288 \
  --report_assumes warn \
  --ext optimize_let_vc \
  --ext fly_deps \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
COMMON_FILES = $(wildcard ../common/*.fst ../common/*.fsti)
EXTERN_FILES = $(EXTERN_DIR)/Common.Memmove.fsti
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(EXTERN_FILES) $(SPEC_FILES) $(IMPL_FILES)

# ── Main Targets (MUST come before .depend include) ───────────────
.PHONY: all verify clean check-admits stats help extract extract-c test-c

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
	@touch -c $@
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
	rm -rf $(OUTPUT_DIR)
	rm -rf $(EXTRACT_DIR)
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
	@echo "  make extract      - Extract to C (same as extract-c)"
	@echo "  make extract-c    - Extract F* to C with Custard's C backend"
	@echo "  make test-c       - Compile and run C test"
	@echo "  make clean        - Remove build artifacts"
	@echo "  make help         - Show this help"
	@echo ""
	@echo "Parallel build:"
	@echo "  make -j4          - Build with 4 parallel jobs"
	@echo ""
	@echo "Incremental builds: Only changed files and their dependents are reverified"
	@echo "Expected result: All modules verify with 0 admits"

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════

# ── Modules to Extract ─────────────────────────────────────────────
IMPL_MODULES = \
  Calc.Impl.Types \
  Calc.Impl.Parser \
  Calc.Impl.Push \
  Calc.Impl.Peek \
  Calc.Impl.Add \
  Calc.Impl.Sub \
  Calc.Impl.Mul \
  Calc.Impl.Div \
  Calc.Server \
  Calc.Server.CanonicalProtocol \
  Calc.Server.Endpoint \
  Calc.Server.EndpointRunner

# Custard (F*'s whole-program extractor) extracts, from the checked files, the
# endpoint runner test_main.c calls and everything it reaches, straight to one
# C file (--codegen C).  It takes a single file on the command line and loads
# the other modules on demand.  Common.TCP's abstract types are defined by
# c_stubs/common_tcp_custard.h, which the generated header includes.
CALC_C = $(EXTRACT_DIR)/Calc_Server.c

$(EXTRACT_DIR):
	@mkdir -p $@

$(CALC_C): verify | $(EXTRACT_DIR)
	@echo "Extracting Calc.Server.EndpointRunner to C"
	@$(FSTAR) --codegen C \
	  --custard_entry Calc.Server.EndpointRunner.run_channel_endpoint \
	  --custard_c_no_prefix Calc.Server.EndpointRunner \
	  --custard_extern_type Common.TCP.channel@common_tcp_custard.h \
	  --custard_extern_type Common.TCP.listener@common_tcp_custard.h \
	  $(IMPL_DIR)/Calc.Server.EndpointRunner.fst -o $@
	@echo "✅ C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/Calc_Server.c $(EXTRACT_DIR)/Calc_Server.h

extract-c: $(CALC_C)

extract: extract-c

# ── C Compilation and Testing ──────────────────────────────────────
CFLAGS_C = -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra -I$(EXTRACT_DIR) -I../c_stubs

test-c: extract-c
	@echo "Compiling C test..."
	@gcc $(CFLAGS_C) -c $(CALC_C) -o $(EXTRACT_DIR)/Calc_Server.o
	@gcc $(CFLAGS_C) \
	  -o $(EXTRACT_DIR)/calc_test \
	  $(EXTRACT_DIR)/Calc_Server.o \
	  ../c_stubs/common_tcp_custard.c \
	  ../c_stubs/common_tcp_stubs.c \
	  test_main.c \
	  -pthread
	@echo "✅ C code compiled successfully"
	@echo ""
	@echo "Running C test..."
	@$(EXTRACT_DIR)/calc_test
