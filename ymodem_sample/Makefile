# ═══════════════════════════════════════════════════════════════════
# YMODEM sample: Makefile (verify + KaRaMeL C extraction)
# ═══════════════════════════════════════════════════════════════════
# Inspired by ../calc_sample/Makefile.  Verifies the YMODEM spec, wire format,
# state-machine instances and the (skeleton) Pulse implementation, and extracts
# the implementation entry points to C via KaRaMeL for the interop wrappers.
#
# Two-layer implementation (mirrors calc_sample):
#   * YModem.Impl.Server / YModem.Impl.Client hold the executable *leaf*
#     operations (emit_block, recv_block).  They are standalone (only Pulse/F*
#     array primitives), so KaRaMeL extracts them to two small, self-contained C
#     files with unprefixed names — the ABI the interop wrappers link against.
#     They are fully VERIFIED against the QuackyDucky wire format (emit_block
#     proves `out` holds the serialization of a ymodem_packet with the given
#     128-byte payload; recv_block proves the dual for parsing) and carry a
#     matching .fsti (needed so the .fst may `friend` the generated wire modules).
#   * YModem.Impl.Server.CanonicalProtocol / YModem.Impl.Client.CanonicalProtocol
#     hold the Common.ProtocolImplementation.protocol_implementation instances
#     (the verified refinement witnesses for ymodem_server_wfsm / ymodem_client_wfsm),
#     whose pi_process_local / pi_process_network drive those leaf operations.
#     Like every type-class dictionary these instances carry separation-logic and
#     ghost/stt fields, so they are NOT Low* — they are verified by `make verify`
#     but not extracted to C (KaRaMeL cannot lower a dictionary; cf. calc's
#     calc_server_protocol_implementation).  Only the leaves they drive lower to C.

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

.PHONY: all verify clean check-admits extract extract-krml extract-c help

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
	@echo "All YMODEM modules verified"

check-admits:
	@echo "Checking for admits (the emit_block/recv_block leaves are verified; CanonicalProtocol instance process/ghost fns may still be admit-based)..."
	@grep -rn "admit *()" $(IMPL_DIR) 2>/dev/null || echo "  none"

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════
# The executable *leaf* modules to extract.  They are standalone (they use only
# Pulse/F* array primitives), so KaRaMeL bundles away the FStar/Pulse/Prims
# support and emits one C file per module with unprefixed function names.  The
# CanonicalProtocol instance modules that drive these leaves are verified but are
# not extracted here: a protocol_implementation dictionary is not Low* (it holds
# separation-logic and ghost/stt fields), so it does not lower to C.
IMPL_MODULES = \
  YModem.Impl.Server \
  YModem.Impl.Client

KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(IMPL_MODULES)))

$(OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1: F* → .krml ────────────────────────────────────────────
$(OUTPUT_DIR)/YModem_Impl_%.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting YModem.Impl.$* to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module YModem.Impl.$* \
	  --odir $(OUTPUT_DIR) \
	  $(IMPL_DIR)/YModem.Impl.$*.fst --krmloutput $@

extract-krml: $(KRML_FILES)
	@echo "All implementation modules extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17 \
	  -bundle 'YModem.Impl.Server=[rename=YModem_Impl_Server]' \
	  -bundle 'YModem.Impl.Client=[rename=YModem_Impl_Client]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix YModem.Impl.Server \
	  -no-prefix YModem.Impl.Client \
	  $(KRML_FILES)
	@echo "C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/YModem_Impl_Server.c $(EXTRACT_DIR)/YModem_Impl_Client.c 2>/dev/null || true

extract: extract-c

# ── C wrappers (unverified interop drivers) ────────────────────────
# Compile the `rb`/`sb`-style interop wrappers against the extracted C.  This
# links the verified extracted leaves (emit_block/recv_block); the executables
# are produced for ABI/compile checking and are not exercised here.
KRML_INCLUDE = $(KRML_HOME)/include
KRML_RUNTIME = $(KRML_HOME)/krmllib/dist/minimal
INTEROP_DIR  = interop
CC ?= gcc
CFLAGS_WRAP = -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra \
  -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR)

.PHONY: wrappers
wrappers: extract-c
	@echo "Compiling YMODEM interop wrappers (not run)..."
	$(CC) $(CFLAGS_WRAP) -o $(EXTRACT_DIR)/ymodem_rb \
	  $(INTEROP_DIR)/ymodem_rb.c $(EXTRACT_DIR)/YModem_Impl_Client.c
	$(CC) $(CFLAGS_WRAP) -o $(EXTRACT_DIR)/ymodem_sb \
	  $(INTEROP_DIR)/ymodem_sb.c $(EXTRACT_DIR)/YModem_Impl_Server.c
	@echo "Wrappers compiled to $(EXTRACT_DIR)/ymodem_rb and $(EXTRACT_DIR)/ymodem_sb (do not run)."

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "YMODEM sample - Makefile targets:"
	@echo "  make verify        - Verify all YMODEM modules (default)"
	@echo "  make check-admits  - List admits (leaves verified; instances may still have them)"
	@echo "  make extract-krml  - Extract the impl modules to .krml"
	@echo "  make extract-c     - Run KaRaMeL to generate C (into _extract/)"
	@echo "  make extract       - verify + extract-krml + extract-c"
	@echo "  make wrappers      - Compile the rb/sb interop wrappers (not run)"
	@echo "  make clean         - Remove build artifacts"
