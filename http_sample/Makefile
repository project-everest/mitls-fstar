# ═══════════════════════════════════════════════════════════════════
# HTTP sample: Makefile (verify + KaRaMeL C extraction)
# ═══════════════════════════════════════════════════════════════════
# Verifies the IETF HTTP (RFC 1350) reliable-delivery specification and
# executable layer, and (in later phases) extracts the verified codec + driver
# loops to C for the interop wrappers.  Structure mirrors ../ymodem_sample, with
# ONE deliberate difference: there is NO QuackyDucky `gen` target, because the
# HTTP wire format exceeds the expressive power of EverParse/QuackyDucky (NUL-
# terminated variable-length strings and a datagram-length-implicit DATA payload)
# and is therefore written and proved BY HAND over FStar.Seq in spec/HTTP.Wire.fst.
#
#   * Specification layer (spec/):
#       - HTTP.Wire       : hand-written RFC 1350 wire format (the five packet
#         types RRQ/WRQ/DATA/ACK/ERROR as a tagged union `http_message`), the
#         Common.WireFormat.wire_format instance, and its round-trip law.  Note:
#         DATA is datagram-delimited (implicit payload length), so it is NOT a
#         strong (prefix) parser and the OPTIONAL Common.WireFormat stream laws
#         are deliberately not instantiated; the driver only needs per-datagram
#         wf_parse (one datagram per read).
#       - HTTP.Protocol   : (later) the stop-and-wait ARQ state machines +
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
	@echo "All HTTP modules verified"

check-admits:
	@echo "Checking for admits..."
	@grep -rn "admit *()" $(SPEC_DIR) $(IMPL_DIR) 2>/dev/null || echo "  none"

# ═══════════════════════════════════════════════════════════════════
# Extraction to C
# ═══════════════════════════════════════════════════════════════════
# The verified codec leaf `HTTP.Impl.Codec` is standalone (only Pulse/F* array
# primitives + the hand-written HTTP.Wire spec it proves against), so KaRaMeL
# bundles away the FStar/Pulse/Prims support and emits one C file with unprefixed
# function names — the ABI the interop wrappers (P5) link against.
IMPL_MODULES = HTTP.Impl.Codec.Chunked

KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(IMPL_MODULES)))

$(OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# ── Phase 1: F* → .krml ────────────────────────────────────────────
$(OUTPUT_DIR)/HTTP_Impl_Codec_Chunked.krml: verify | $(OUTPUT_DIR)
	@echo "Extracting HTTP.Impl.Codec.Chunked to .krml"
	@$(FSTAR) --codegen krml \
	  --extract_module HTTP.Impl.Codec.Chunked \
	  --odir $(OUTPUT_DIR) \
	  $(IMPL_DIR)/HTTP.Impl.Codec.Chunked.fst --krmloutput $@

extract-krml: $(KRML_FILES)
	@echo "All implementation modules extracted to .krml"

# ── Phase 2: .krml → C ─────────────────────────────────────────────
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "Running KaRaMeL to generate C code..."
	@$(KRML) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17 \
	  -bundle 'HTTP.Impl.Codec.Chunked=[rename=HTTP_Impl_Codec_Chunked]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,HTTP.Wire.Common,HTTP.Wire.Chunked' \
	  -no-prefix HTTP.Impl.Codec.Chunked \
	  $(KRML_FILES)
	@echo "C code generated in $(EXTRACT_DIR)/"
	@ls -lh $(EXTRACT_DIR)/HTTP_Impl_Codec_Chunked.c 2>/dev/null || true

extract: extract-c

# ═══════════════════════════════════════════════════════════════════
# Verified driver loop → C + end-to-end (verified-loop) test
# ═══════════════════════════════════════════════════════════════════
# Extract the VERIFIED HTTP chunked send loop (http_server_run in
# HTTP.Impl.Server.Loop) — which reuses the verified codec leaves
# (http_emit_chunk / http_emit_empty_chunk) and the verified Common.TCP
# interface — to one self-contained C bundle (_extract/HTTP_Verified.c), then
# link a socketpair test harness (verified sender -> plain-C chunked receiver)
# that transfers a file body and checks the reconstructed bytes.  The socketpair
# is SOCK_STREAM: HTTP runs over TCP and chunked framing is self-delimiting
# (each chunk carries its own hex4 length prefix), so no datagram boundaries are
# needed.  The verified loop uses only Common.TCP write/close, so no Pulse array
# shim is required (the codec copies via a verified index loop, not memcpy_l).
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
	@echo "Extracting the verified HTTP driver loop to C ..."
	@EVERPARSE_HOME=$(EVERPARSE_HOME) bash extract_loops.sh

vloop-test: extract-loops
	@echo "Building the verified-loop transfer test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/vloop_test \
	  $(VERIFIED_DIR)/vloop_test.c \
	  $(EXTRACT_DIR)/HTTP_Verified.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified server send loop  ->  Verified client receive loop  (over a SOCK_STREAM socketpair)"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/vloop_test $(VERIFIED_DIR)/dummy.txt

vloop-length-test: extract-loops
	@echo "Building the verified Content-Length transfer test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/vloop_length_test \
	  $(VERIFIED_DIR)/vloop_length_test.c \
	  $(EXTRACT_DIR)/HTTP_Verified.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified server send loop  ->  Verified client receive loop  (Content-Length body, SOCK_STREAM)"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/vloop_length_test $(VERIFIED_DIR)/dummy.txt

# Run both framings' verified<->verified interop tests.
vloop-tests: vloop-test vloop-length-test

head-emit-test: extract-loops
	@echo "Building the verified head-emitter self-test ..."
	$(CC) $(CFLAGS_VLOOP) -o $(EXTRACT_DIR)/head_emit_test \
	  $(VERIFIED_DIR)/head_emit_test.c \
	  $(EXTRACT_DIR)/HTTP_Verified.c \
	  $(STUBS_DIR)/common_tcp_karamel.c $(STUBS_DIR)/common_tcp_stubs.c
	@echo "─────────────────────────────────────────────────────────────────"
	@echo " Verified http_emit_response / http_emit_request  ->  byte-exact reference"
	@echo "─────────────────────────────────────────────────────────────────"
	@$(EXTRACT_DIR)/head_emit_test

# ── Clean ──────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f .depend
	@echo "Cleaned build artifacts"

help:
	@echo "HTTP sample - Makefile targets:"
	@echo "  make verify        - Verify all HTTP modules (default)"
	@echo "  make check-admits  - List admits in spec/ and impl/"
	@echo "  make extract-krml  - Extract the codec leaf to .krml"
	@echo "  make extract-c     - Run KaRaMeL to generate C (into _extract/)"
	@echo "  make extract       - verify + extract-krml + extract-c"
	@echo "  make extract-loops - Extract the verified driver loops (_extract/HTTP_Verified.c)"
	@echo "  make vloop-test    - Build + run the verified chunked server->client transfer test"
	@echo "  make vloop-length-test - Build + run the verified Content-Length transfer test"
	@echo "  make vloop-tests   - Run both framings' verified<->verified interop tests"
	@echo "  make head-emit-test - Build + run the verified head-emitter byte-exact self-test"
	@echo "  make clean         - Remove build artifacts"
	@echo "  (no 'gen' target: the HTTP wire format is hand-written, not QuackyDucky)"
