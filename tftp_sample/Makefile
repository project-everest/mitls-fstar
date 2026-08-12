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
KRML_HOME ?= $(EVERPARSE_HOME)/opt/karamel
KRML ?= $(KRML_HOME)/out/bin/krml
Z3_DIR ?= $(EVERPARSE_HOME)/opt/z3
LOWPARSE_HOME ?= $(EVERPARSE_HOME)/src/lowparse
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
  --z3version $(Z3_VERSION) \
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

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════
# The verified codec leaf `TFTP.Impl.Codec` is standalone (only Pulse/F* array
# primitives + the hand-written TFTP.Wire spec it proves against), so KaRaMeL
# bundles away the FStar/Pulse/Prims support and emits one C file with unprefixed
# function names — the ABI the interop wrappers (P5) link against.
IMPL_MODULES = TFTP.Impl.Codec

KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(IMPL_MODULES)))

$(OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1: F* → .krml ────────────────────────────────────────────
$(OUTPUT_DIR)/TFTP_Impl_Codec.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting TFTP.Impl.Codec to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module TFTP.Impl.Codec \
	  --odir $(OUTPUT_DIR) \
	  $(IMPL_DIR)/TFTP.Impl.Codec.fst --krmloutput $@

extract-krml: $(KRML_FILES)
	@echo "All implementation modules extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17 \
	  -bundle 'TFTP.Impl.Codec=[rename=TFTP_Impl_Codec]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix TFTP.Impl.Codec \
	  $(KRML_FILES)
	@echo "C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/TFTP_Impl_Codec.c 2>/dev/null || true

extract: extract-c

# ═══════════════════════════════════════════════════════════════════
# Verified driver loops → C + end-to-end (verified-loop) test
# ═══════════════════════════════════════════════════════════════════
# Extract the VERIFIED TFTP driver loops (tftp_client_run / tftp_server_run in
# TFTP.Impl.{Client,Server}.Loop) — which reuse the verified codec leaves and
# the CanonicalProtocol process_network/process_local — to one self-contained C
# bundle (_extract/TFTP_Verified.c), then link a socketpair test harness that
# runs a real file transfer through them (verified sender -> verified receiver)
# and checks the reconstructed bytes.  Unlike YMODEM, the socketpair is
# SOCK_DGRAM (each Common_TCP_read returns exactly one datagram), realizing the
# one-datagram-per-read discipline TFTP's implicit-length DATA relies on.
# pulse_array_shim.c is the trusted C realization of the Pulse library's verified
# memcpy_l (as the TCP stub is the trusted realization of read/write).
VERIFIED_DIR = verified
STUBS_DIR    = ../c_stubs
KRML_INCLUDE = $(KRML_HOME)/include
KRML_RUNTIME = $(KRML_HOME)/krmllib/dist/minimal
INTEROP_DIR  = interop
CC ?= gcc
CFLAGS_VLOOP = -std=c11 -D_DEFAULT_SOURCE -DCOMMON_TCP_KARAMEL_FULL_DECLS \
  -include $(STUBS_DIR)/common_tcp_karamel.h -Wall -Wno-unused-function \
  -Wno-unused-parameter -Wno-implicit-function-declaration \
  -I$(KRML_INCLUDE) -I$(KRML_INCLUDE)/krml -I$(KRML_RUNTIME) -I$(EXTRACT_DIR) -I$(STUBS_DIR)

extract-loops: verify
	@echo "Extracting the verified TFTP driver loops to C ..."
	@EVERPARSE_HOME=$(EVERPARSE_HOME) bash extract_loops.sh

vloop-test: extract-loops
	@echo "Building the verified-loop transfer test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/vloop_test \
	  $(VERIFIED_DIR)/vloop_test.c $(VERIFIED_DIR)/pulse_array_shim.c \
	  $(EXTRACT_DIR)/TFTP_Verified.c $(EXTRACT_DIR)/Common_ProtocolImplementation.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified server loop  ->  verified client loop  (over a SOCK_DGRAM socketpair)"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/vloop_test $(VERIFIED_DIR)/dummy.txt

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "TFTP sample - Makefile targets:"
	@echo "  make verify        - Verify all TFTP modules (default)"
	@echo "  make check-admits  - List admits in spec/ and impl/"
	@echo "  make extract-krml  - Extract the codec leaf to .krml"
	@echo "  make extract-c     - Run KaRaMeL to generate C (into _extract/)"
	@echo "  make extract       - verify + extract-krml + extract-c"
	@echo "  make extract-loops - Extract the verified driver loops (_extract/TFTP_Verified.c)"
	@echo "  make vloop-test    - Build + run the verified server->client transfer test"
	@echo "  make clean         - Remove build artifacts"
	@echo "  (no 'gen' target: the TFTP wire format is hand-written, not QuackyDucky)"
