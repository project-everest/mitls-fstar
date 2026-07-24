# ═══════════════════════════════════════════════════════════════════
# YMODEM sample: Makefile (verify + KaRaMeL C extraction)
# ═══════════════════════════════════════════════════════════════════
# Verifies the YMODEM reliable-delivery (ARQ) specification and executable layer,
# and extracts the verified codec leaf to C for the interop wrappers.
#
#   * Specification layer (spec/): the QuackyDucky-generated wire format (a
#     leading-byte-discriminated packet/control union `ymodem_message`), the
#     wire_format instance, and the stop-and-wait ARQ state-machine +
#     file_transfer instances (YModem.Protocol).
#
#   * Executable layer (impl/):
#       - YModem.Impl.Codec holds the executable *leaf* codecs:
#         `ymodem_emit_data_block` (serialize a Body_soh data packet) and
#         `ymodem_recv_data_block` (parse one).  They are standalone (only Pulse/
#         F* array primitives), fully VERIFIED against the QuackyDucky wire
#         format, and KaRaMeL extracts them to one small self-contained C file
#         with unprefixed names — the ABI the interop wrappers link against.  The
#         control frames (EOT/ACK/NAK/CAN/'C') are single literal bytes handled
#         directly in the wrappers, so they need no leaf.
#       - YModem.Impl.{Server,Client}.CanonicalProtocol hold the
#         Common.ProtocolImplementation.protocol_implementation instances (the
#         verified refinement witnesses for ymodem_{server,client}_wfsm) that
#         drive those leaves.  Like every type-class dictionary they carry
#         separation-logic and ghost/stt fields, so they are NOT Low* — verified
#         by `make verify` but not extracted (KaRaMeL cannot lower a dictionary;
#         cf. calc's calc_server_protocol_implementation).

# ── Toolchain ──────────────────────────────────────────────────────
EVERPARSE_HOME ?= $(abspath ../tools/everparse)
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME ?= $(EVERPARSE_HOME)/opt/karamel
KRML ?= $(KRML_HOME)/out/bin/krml
QD ?= $(EVERPARSE_HOME)/bin/qd.exe
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
LOWPARSE_HOME ?= $(EVERPARSE_HOME)/src/lowparse
export PATH := $(Z3_DIR):$(PATH)

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
SPEC_DIR    = spec
IMPL_DIR    = impl
EXTERN_DIR  = ../src/impl/extern
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include ../common \
  --include $(EXTERN_DIR) \
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
EXTERN_FILES = $(EXTERN_DIR)/Common.Memmove.fsti
SPEC_FILES = $(wildcard $(SPEC_DIR)/*.fst $(SPEC_DIR)/*.fsti)
IMPL_FILES = $(wildcard $(IMPL_DIR)/*.fst $(IMPL_DIR)/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(EXTERN_FILES) $(SPEC_FILES) $(IMPL_FILES)

.PHONY: all verify gen extract extract-krml extract-c wrappers clean check-admits help

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
	@echo "Checking for admits (the codec leaves are verified; CanonicalProtocol instances too)..."
	@grep -rn "admit *()" $(IMPL_DIR) 2>/dev/null || echo "  none"

# ── Regenerate the wire format from the QuackyDucky description ─────
# (Run after editing ymodem.qd.rfc; then `make verify` to refresh .checked.)
gen:
	@echo "Regenerating YModem.Wire.Generated.* from ymodem.qd.rfc ..."
	$(QD) -pulse -prefix "YModem.Wire.Generated." -odir $(SPEC_DIR) ymodem.qd.rfc
	@echo "Regenerated — now run 'make verify'."

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════
# The executable *leaf* module to extract.  It is standalone (it uses only
# Pulse/F* array primitives), so KaRaMeL bundles away the FStar/Pulse/Prims
# support and emits one C file with unprefixed function names — the ABI the
# interop wrappers link against.  The CanonicalProtocol instance modules that
# drive these leaves are verified but not extracted: a protocol_implementation
# dictionary is not Low* (it holds separation-logic and ghost/stt fields).
IMPL_MODULES = YModem.Impl.Codec

KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(IMPL_MODULES)))

$(OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1: F* → .krml ────────────────────────────────────────────
$(OUTPUT_DIR)/YModem_Impl_Codec.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting YModem.Impl.Codec to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module YModem.Impl.Codec \
	  --odir $(OUTPUT_DIR) \
	  $(IMPL_DIR)/YModem.Impl.Codec.fst --krmloutput $@

extract-krml: $(KRML_FILES)
	@echo "All implementation modules extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17 \
	  -bundle 'YModem.Impl.Codec=[rename=YModem_Impl_Codec]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix YModem.Impl.Codec \
	  $(KRML_FILES)
	@echo "C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/YModem_Impl_Codec.c 2>/dev/null || true

extract: extract-c

# ── C wrappers (unverified interop drivers) ────────────────────────
# Compile the `rb`/`sb`-style interop wrappers against the extracted C.  Both
# wrappers link the single verified codec (emit/recv data block).
KRML_INCLUDE = $(KRML_HOME)/include
KRML_RUNTIME = $(KRML_HOME)/krmllib/dist/minimal
INTEROP_DIR  = interop
CC ?= gcc
CFLAGS_WRAP = -std=c11 -D_DEFAULT_SOURCE -Wall -Wextra \
  -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR)

wrappers: extract-loops
	@echo "Compiling YMODEM interop drivers over the VERIFIED loops..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/ymodem_rb \
	  $(INTEROP_DIR)/ymodem_rb.c $(VERIFIED_DIR)/pulse_array_shim.c \
	  $(EXTRACT_DIR)/YModem_Verified.c $(EXTRACT_DIR)/Common_ProtocolImplementation.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/ymodem_sb \
	  $(INTEROP_DIR)/ymodem_sb.c $(VERIFIED_DIR)/pulse_array_shim.c \
	  $(EXTRACT_DIR)/YModem_Verified.c $(EXTRACT_DIR)/Common_ProtocolImplementation.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "Interop drivers ymodem_rb / ymodem_sb (verified loops) compiled to $(EXTRACT_DIR)/."

# ── Verified driver loops → C + end-to-end test ────────────────────
# Extract the VERIFIED YMODEM driver loops (ymodem_client_run / ymodem_server_run
# in YModem.Impl.{Client,Server}.Loop) — which reuse the verified process_network
# leaf and the verified send wrappers — to a single self-contained C bundle
# (_extract/YModem_Verified.c), then link the socketpair test harness that runs a
# real file transfer through them (verified sender -> verified receiver) and
# checks the reconstructed bytes.  Unlike the endpoint / drive_steps model (which
# is a verified but non-extractable orchestration over typeclass dictionaries),
# these loops lower to first-order Low* C, so they are the *runnable* verified
# orchestration.  pulse_array_shim.c is the trusted C realization of the Pulse
# library's verified memcpy_l (as the TCP stub is the trusted realization of the
# verified read/write interface).
VERIFIED_DIR = verified
STUBS_DIR    = ../c_stubs
CFLAGS_VLOOP = -std=c11 -D_DEFAULT_SOURCE -DCOMMON_TCP_KARAMEL_FULL_DECLS \
  -include $(STUBS_DIR)/common_tcp_karamel.h -Wall -Wno-unused-function \
  -Wno-unused-parameter -Wno-implicit-function-declaration \
  -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR) -I$(STUBS_DIR)

extract-loops: verify
	@echo "Extracting the verified driver loops to C ..."
	@EVERPARSE_HOME=$(EVERPARSE_HOME) bash extract_loops.sh

vloop-test: extract-loops
	@echo "Building the verified-loop transfer test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/vloop_test \
	  $(VERIFIED_DIR)/vloop_test.c $(VERIFIED_DIR)/pulse_array_shim.c \
	  $(EXTRACT_DIR)/YModem_Verified.c $(EXTRACT_DIR)/Common_ProtocolImplementation.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified server loop  ->  verified client loop  (over a socketpair)"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/vloop_test $(INTEROP_DIR)/dummy.txt

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "YMODEM sample - Makefile targets:"
	@echo "  make verify        - Verify all YMODEM modules (default)"
	@echo "  make gen           - Regenerate YModem.Wire.Generated.* from ymodem.qd.rfc"
	@echo "  make check-admits  - List admits in impl/"
	@echo "  make extract-krml  - Extract the codec leaf to .krml"
	@echo "  make extract-c     - Run KaRaMeL to generate C (into _extract/)"
	@echo "  make extract       - verify + extract-krml + extract-c"
	@echo "  make wrappers      - Compile the rb/sb interop wrappers"
	@echo "  make extract-loops - Extract the verified driver loops to C (_extract/YModem_Verified.c)"
	@echo "  make vloop-test    - Build + run the verified server->client transfer test"
	@echo "  make clean         - Remove build artifacts"
