# ═══════════════════════════════════════════════════════════════════
# FTP block-mode (MODE B) sample: Makefile (verify only)
# ═══════════════════════════════════════════════════════════════════
# Verifies the FTP block-mode (RFC 959 §3.4.2) data-block specification: the
# QuackyDucky-generated wire format (a 2-byte length-prefixed data block) and
# the hand-written Common.WireFormat / Common.WireFormatStateMachine + protocol
# instances built on top of it.
#
# This sample is SPEC-ONLY: it has no executable (impl/) layer, no C extraction
# and no interop harness — only the F* specification is verified.  The other
# samples (calc/tftp/ymodem) additionally extract verified driver loops to C.
#
#   make verify   Verify all FTPBlock.* modules (default).
#   make gen      Regenerate FTPBlock.Wire.Generated.* from ftp_block.qd.rfc.
#   make clean    Remove build artifacts.

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

.PHONY: all verify gen clean check-admits help

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
	@echo "All FTPBlock modules verified"

check-admits:
	@echo "Checking for admits ..."
	@grep -rn "admit *()" $(SPEC_DIR) 2>/dev/null || echo "  none"

# ── Regenerate the wire format from the QuackyDucky description ─────
# (Run after editing ftp_block.qd.rfc; then `make verify` to refresh .checked.)
gen:
	@echo "Regenerating FTPBlock.Wire.Generated.* from ftp_block.qd.rfc ..."
	$(QD) -pulse -prefix "FTPBlock.Wire.Generated." -odir $(SPEC_DIR) ftp_block.qd.rfc
	@echo "Regenerated — now run 'make verify'."

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "FTP block-mode sample - Makefile targets:"
	@echo "  make verify        - Verify all FTPBlock.* modules (default)"
	@echo "  make gen           - Regenerate FTPBlock.Wire.Generated.* from ftp_block.qd.rfc"
	@echo "  make check-admits  - List admits in spec/"
	@echo "  make clean         - Remove build artifacts"
