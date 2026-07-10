# ═══════════════════════════════════════════════════════════════════
# TFTP sample: Makefile (verify + KaRaMeL C extraction)
# ═══════════════════════════════════════════════════════════════════
# Verifies the IETF TFTP (RFC 1350) reliable-delivery specification and
# executable layer, and (in later phases) extracts the verified codec + driver
# loops to C for the interop wrappers.  Structure mirrors ../ymodem_sample, with
# ONE deliberate difference: there is NO QuackyDucky `gen` target, because the
# TFTP wire format exceeds the expressive power of EverParse/QuackyDucky (NUL-
# terminated variable-length strings and a datagram-length-implicit DATA payload)
# and is therefore written and proved BY HAND over FStar.Seq in spec/TFTP.Wire.fst.
#
#   * Specification layer (spec/):
#       - TFTP.Wire       : hand-written RFC 1350 wire format (the five packet
#         types RRQ/WRQ/DATA/ACK/ERROR as a tagged union `tftp_message`), the
#         Common.WireFormat.wire_format instance, and its round-trip law.  Note:
#         DATA is datagram-delimited (implicit payload length), so it is NOT a
#         strong (prefix) parser and the OPTIONAL Common.WireFormat stream laws
#         are deliberately not instantiated; the driver only needs per-datagram
#         wf_parse (one datagram per read).
#       - TFTP.Protocol   : (later) the stop-and-wait ARQ state machines +
#         Common.FileTransfer instance for the RRQ/download direction.
#
#   * Executable layer (impl/): (later phases) verified Pulse codec leaves and
#     driver loops, plus the Common.ProtocolImplementation / ProtocolEndpoint
#     dictionaries that drive them.

# ── Toolchain ──────────────────────────────────────────────────────
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME ?= $(FSTAR_HOME)/karamel
KRML ?= $(KRML_HOME)/out/bin/krml
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
LOWPARSE_HOME ?= $(EVERPARSE_HOME)/src/lowparse
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
SPEC_DIR    = spec
IMPL_DIR    = impl
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(LOWPARSE_HOME) \
  --include $(LOWPARSE_HOME)/pulse \
  --include $(SPEC_DIR) \
  --include $(IMPL_DIR)

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
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(SPEC_FILES) $(IMPL_FILES)

.PHONY: all verify clean check-admits help

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
	@echo "All TFTP modules verified"

check-admits:
	@echo "Checking for admits..."
	@grep -rn "admit *()" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null || echo "  none"

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "TFTP sample - Makefile targets:"
	@echo "  make verify        - Verify all TFTP modules (default)"
	@echo "  make check-admits  - List admits in spec/ and impl/"
	@echo "  make clean         - Remove build artifacts"
	@echo "  (no 'gen' target: the TFTP wire format is hand-written, not QuackyDucky)"
