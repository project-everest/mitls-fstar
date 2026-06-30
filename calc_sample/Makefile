# ═══════════════════════════════════════════════════════════════════
# Calculator Sample: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental and parallel builds

# ── Toolchain ──────────────────────────────────────────────────────
# Use the same Pulse-capable EverParse/F*/KaRaMeL toolchain as the root build.
# Override these variables to test with a different compatible toolchain.
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME ?= $(FSTAR_HOME)/karamel
KRML ?= $(KRML_HOME)/out/bin/krml
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
FSTAR_LIB ?= $(shell $(FSTAR_EXE) --locate_lib)
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR = _cache
SPEC_DIR  = spec
IMPL_DIR  = impl
OUTPUT_DIR = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

FSTAR_FLAGS = \
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
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(SPEC_FILES) $(IMPL_FILES)

# ── Main Targets (MUST come before .depend include) ───────────────
.PHONY: all verify clean check-admits stats help extract extract-krml extract-c test-c

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
	@echo "  make extract      - Extract to C (verify + extract-krml + extract-c)"
	@echo "  make extract-krml - Extract F* to .krml files"
	@echo "  make extract-c    - Run KaRaMeL to generate C code"
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
  Calc.Server.Socket \
  Calc.Server.EndpointRunner

COMMON_EXTRACT_MODULES = \
  Common.TCP

# Convert module names to .krml filenames
KRML_FILES = \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(COMMON_EXTRACT_MODULES))) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(IMPL_MODULES))) \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

$(OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1: F* → .krml ────────────────────────────────────────────
$(OUTPUT_DIR)/Common_TCP.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting Common.TCP to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module Common.TCP \
	  --odir $(OUTPUT_DIR) \
	  ../common/Common.TCP.fsti --krmloutput $@

$(OUTPUT_DIR)/Common_%.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting Common.$(subst _,.,$*) to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module Common.$(subst _,.,$*) \
	  --odir $(OUTPUT_DIR) \
	  ../common/Common.$(subst _,.,$*).fst

# Pattern rule: _output/Calc_Server.krml from Calc.Server
$(OUTPUT_DIR)/%.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting $(subst _,.,$*) to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module $(subst _,.,$*) \
	  --odir $(OUTPUT_DIR) \
	  $(IMPL_DIR)/$(subst _,.,$*).fst

$(OUTPUT_DIR)/FStar_Pervasives_Native.krml: | $(OUTPUT_DIR)
	@echo "Extracting FStar.Pervasives.Native to .krml"
	@$(FSTAR_EXE) --odir $(OUTPUT_DIR) --already_cached 'Prims,FStar' \
	  --codegen krml --extract_module FStar.Pervasives.Native \
	  $(FSTAR_LIB)/ulib/FStar.Pervasives.Native.fst --krmloutput $@

extract-krml: $(KRML_FILES)
	@echo "✅ All modules extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17 \
	  -add-include '"common_tcp_karamel_compat.h"' \
	  -library Common.TCP \
	  -bundle 'Calc.Server.EndpointRunner=Calc.*[rename=Calc_Server]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix Calc.Server.EndpointRunner \
	  $(KRML_FILES)
	@echo "✅ C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/Calc_Server.c $(EXTRACT_DIR)/Calc_Server.h

extract: extract-c

# ── C Compilation and Testing ──────────────────────────────────────
KRML_INCLUDE = $(KRML_HOME)/include
KRML_RUNTIME = $(KRML_HOME)/krmllib/dist/minimal

test-c: extract-c
	@echo "Compiling C test..."
	@gcc -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR) -I../c_stubs \
	  -c $(EXTRACT_DIR)/Calc_Server.c -o $(EXTRACT_DIR)/Calc_Server.o
	@gcc -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR) -I../c_stubs \
	  -o $(EXTRACT_DIR)/calc_test \
	  $(EXTRACT_DIR)/Calc_Server.o \
	  ../c_stubs/common_tcp_karamel.c \
	  ../c_stubs/common_tcp_stubs.c \
	  test_main.c \
	  -pthread
	@echo "✅ C code compiled successfully"
	@echo ""
	@echo "Running C test..."
	@$(EXTRACT_DIR)/calc_test
