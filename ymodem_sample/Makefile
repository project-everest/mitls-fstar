# ═══════════════════════════════════════════════════════════════════
# YMODEM sample: Makefile (specification verification)
# ═══════════════════════════════════════════════════════════════════
# Verifies the YMODEM *specification* layer: the QuackyDucky-generated wire
# format (a leading-byte-discriminated packet/control union), the wire_format
# instance, and the stop-and-wait ARQ state-machine + file_transfer instances.
#
# NOTE (Milestone A): the executable Pulse implementation (leaves,
# protocol_implementation instances) and the interop wrappers were removed when
# the wire format and state machines were reworked into the reliable-delivery
# (ARQ) model; they are rebuilt against the new spec in Milestone B.  Git history
# preserves the previous download-only implementation.

# ── Toolchain ──────────────────────────────────────────────────────
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
QD ?= $(EVERPARSE_HOME)/bin/qd.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
LOWPARSE_HOME ?= $(EVERPARSE_HOME)/src/lowparse
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
SPEC_DIR    = spec
OUTPUT_DIR  = _output

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(LOWPARSE_HOME) \
  --include $(LOWPARSE_HOME)/pulse \
  --include $(SPEC_DIR)

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse' \
  --warn_error -321-241-272-288 \
  --report_assumes warn \
  --ext optimize_let_vc \
  --ext fly_deps \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
COMMON_FILES = $(wildcard ../common/*.fst ../common/*.fsti)
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(SPEC_FILES)

.PHONY: all verify gen clean help

all: verify

# ── Dependency Analysis ────────────────────────────────────────────
.depend: $(ALL_FILES)
	@echo "Generating dependencies..."
	@$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

-include .depend

# ── Generic Verification Rules ────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	@echo "Verifying $<"
	@$(FSTAR) $<
	@touch $@

$(CACHE_DIR):
	@mkdir -p $@

verify: $(ALL_CHECKED_FILES)
	@echo "All YMODEM specification modules verified"

# ── Regenerate the wire format from the QuackyDucky description ─────
# (Run after editing ymodem.qd.rfc; then `make verify` to refresh .checked.)
gen:
	@echo "Regenerating YModem.Wire.Generated.* from ymodem.qd.rfc ..."
	$(QD) -pulse -prefix "YModem.Wire.Generated." -odir $(SPEC_DIR) ymodem.qd.rfc
	@echo "Regenerated — now run 'make verify'."

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "YMODEM sample - Makefile targets:"
	@echo "  make verify  - Verify all YMODEM specification modules (default)"
	@echo "  make gen     - Regenerate YModem.Wire.Generated.* from ymodem.qd.rfc"
	@echo "  make clean   - Remove build artifacts"
