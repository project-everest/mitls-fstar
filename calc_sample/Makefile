# ═══════════════════════════════════════════════════════════════════
# Calculator Sample: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental and parallel builds

# ── Toolchain ──────────────────────────────────────────────────────
FSTAR_EXE ?= fstar.exe

# EverParse toolchain: provides LowParse (+ LowParse.Pulse) that the generated
# QuackyDucky codec depends on, the KaRaMeL compiler + C runtime, and the pinned
# Z3.  Override EVERPARSE_HOME to point at a different toolchain checkout.
EVERPARSE_HOME ?= $(realpath $(CURDIR)/../tools/everparse)
LOWPARSE_HOME  ?= $(EVERPARSE_HOME)/src/lowparse
KRML_HOME      ?= $(EVERPARSE_HOME)/opt/FStar/karamel
KRML           ?= $(KRML_HOME)/out/bin/krml
# F* locates Z3 by looking for z3-<version> on PATH; the toolchain ships it.
Z3_DIR         ?= $(EVERPARSE_HOME)/opt/z3
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR = _cache
SPEC_DIR  = spec
IMPL_DIR  = impl
GENERATED_DIR = generated
OUTPUT_DIR = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR) \
  --include $(GENERATED_DIR) \
  --include $(LOWPARSE_HOME) \
  --include $(LOWPARSE_HOME)/pulse

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore,LowParse,LowStar,C,Spec.Loops' \
  --warn_error -321-241-272-288 \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(SPEC_FILES) $(IMPL_FILES)

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

# ── Extraction config ──────────────────────────────────────────────
# The calc program (impl + generated codec + LowParse) is extracted WITHOUT the
# concrete Pulse runtime libraries: as already-cached dependencies F* only sees
# their interfaces, so e.g. Pulse.Lib.Slice.slice stays abstract.  The concrete
# definitions (Slice -> {ptr,len}, Vec -> heap array, ...) are produced by
# extracting each runtime module on its own with --extract_module (which reveals
# the .fst struct), then handed to KaRaMeL alongside out.krml.  Providing the
# concrete slice type is also what lets KaRaMeL's remove-unused-parameters pass
# see the real arity of the Slice operations used inside the generated codec.
KRML_EXTRACT = *,-FStar.Tactics,-FStar.Reflection,-Pulse

# Pulse runtime libraries whose concrete C definitions the impl needs.
PULSE_LIB      ?= $(EVERPARSE_HOME)/opt/FStar/pulse/lib/pulse/lib
PULSE_CHK      ?= $(EVERPARSE_HOME)/opt/FStar/pulse/build/lib.pulse.checked
PULSE_KRML_DIR  = $(OUTPUT_DIR)/pulse
PULSE_RT_MODULES = \
  Pulse.Lib.ArrayPtr \
  Pulse.Lib.Slice \
  Pulse.Lib.Reference \
  Pulse.Lib.Box \
  Pulse.Lib.Vec \
  Pulse.Lib.Pervasives
PULSE_RT_KRML = $(patsubst %,$(PULSE_KRML_DIR)/%.krml,$(subst .,_,$(PULSE_RT_MODULES)))

# F* invocation used to extract a single Pulse runtime module from its source
# (so the abstract interface type is revealed to its concrete struct).  Reads the
# pre-built Pulse library .checked read-only; does not write into the install.
PULSE_FSTAR = $(FSTAR_EXE) --cache_dir $(PULSE_CHK) \
  --already_cached 'Prims,FStar,PulseCore,LowStar,C,Spec.Loops' \
  --include $(PULSE_LIB) --warn_error -321-241-272-288-247-274

$(OUTPUT_DIR):
	@mkdir -p $@

$(PULSE_KRML_DIR): | $(OUTPUT_DIR)
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1a: F* → .krml (calc whole program, Pulse runtime abstract) ──
$(OUTPUT_DIR)/out.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting calc whole program to .krml"
	@$(FSTAR) --codegen krml --odir $(OUTPUT_DIR) \
	  --extract '$(KRML_EXTRACT)' \
	  $(IMPL_DIR)/Calc.Server.fst

# ── Phase 1b: F* → .krml (one concrete Pulse runtime module each) ──────
# _output/pulse/Pulse_Lib_Slice.krml from Pulse.Lib.Slice, etc.
$(PULSE_KRML_DIR)/%.krml: | $(PULSE_KRML_DIR)
	@echo "Extracting Pulse runtime $(subst _,.,$*) to .krml"
	@$(PULSE_FSTAR) --codegen krml --odir $(PULSE_KRML_DIR) \
	  --extract_module $(subst _,.,$*) \
	  $(PULSE_LIB)/$(subst _,.,$*).fst

extract-krml: $(OUTPUT_DIR)/out.krml $(PULSE_RT_KRML)
	@echo "✅ Extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
# Bundle all calc + generated + LowParse code into one Calc_Server.{c,h}; the
# Pulse runtime and the FStar/LowStar/C runtime go into their own units.  The
# concrete Pulse runtime .krml come first so their definitions win.
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17-18 \
	  -drop FStar.Tactics -drop FStar.Reflection \
	  -bundle 'Calc.Server=Calc.*,LowParse.*[rename=Calc_Server]' \
	  -bundle 'Pulse.*,PulseCore.*[rename=Calc_Pulse]' \
	  -bundle 'FStar.*,LowStar.*,C.*,Prims[rename=Calc_Krmllib]' \
	  -no-prefix Calc.Server \
	  $(PULSE_RT_KRML) \
	  $(OUTPUT_DIR)/out.krml
	@echo "✅ C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/*.c $(EXTRACT_DIR)/*.h 2>/dev/null

extract: extract-c

# ── C Compilation and Testing ──────────────────────────────────────
KRML_INC = $(KRML_HOME)/include
KRML_MIN = $(KRML_HOME)/krmllib/dist/minimal

test-c: extract-c
	@echo "Compiling C test..."
	gcc -std=c11 -Wall -Wno-unused-variable -Wno-unused-parameter -Wno-unused-function \
	  -I$(KRML_INC) -I$(KRML_MIN) -I$(EXTRACT_DIR) \
	  $(wildcard $(EXTRACT_DIR)/*.c) test_main.c \
	  -o $(EXTRACT_DIR)/calc_test
	@echo "✅ C code compiled successfully"
	@echo ""
	@echo "Running C test..."
	@$(EXTRACT_DIR)/calc_test
