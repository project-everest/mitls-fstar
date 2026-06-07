# ═══════════════════════════════════════════════════════════════════
# Verified TLS 1.3 Client: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental builds

# ── Toolchain Configuration ────────────────────────────────────────
FSTAR_HOME ?= $(CURDIR)/tools/FStar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML_EXE   ?= $(KRML_HOME)/krml

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract
HACL_DIR    = third_party/hacl-star/dist/gcc-compatible
HACL_KI     = third_party/hacl-star/dist/karamel/include
HACL_KL     = third_party/hacl-star/dist/karamel/krmllib/dist/minimal

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include src/spec \
  --include src/impl

FSTAR_FLAGS = \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
  --ext optimize_let_vc \
  --ext fly_deps \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
SPEC_FILES = $(wildcard src/spec/*.fst src/spec/*.fsti)
IMPL_FILES = $(wildcard src/impl/*.fst src/impl/*.fsti)
ALL_FILES  = $(SPEC_FILES) $(IMPL_FILES)

# ── Dependency Analysis ────────────────────────────────────────────
.depend: $(ALL_FILES) | check-toolchain
	$(FSTAR) --dep full $(ALL_FILES) --output_deps_to $@

include .depend

# ── Generic Verification Rules ────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	$(FSTAR) $<

$(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR):
	mkdir -p $@

# ── Main Targets ───────────────────────────────────────────────────
.PHONY: all verify test clean check-toolchain check-deps admit-count check-admits

all: verify

verify: $(ALL_CHECKED_FILES)
	@echo "All F* modules verified"

admit-count:
	@matches=$$(grep -RIn --include='*.fst' --include='*.fsti' 'admit[[:space:]]*(' src calc_sample/spec calc_sample/impl || true); \
	if [ -n "$$matches" ]; then \
	  printf "%s\n" "$$matches"; \
	  count=$$(printf "%s\n" "$$matches" | wc -l); \
	  echo "$$count admit(s) found"; \
	else \
	  echo "0 admit(s) found"; \
	fi

check-admits:
	@matches=$$(grep -RIn --include='*.fst' --include='*.fsti' 'admit[[:space:]]*(' src calc_sample/spec calc_sample/impl || true); \
	if [ -n "$$matches" ]; then \
	  printf "%s\n" "$$matches"; \
	  count=$$(printf "%s\n" "$$matches" | wc -l); \
	  echo "$$count admit(s) found"; \
	  exit 1; \
	else \
	  echo "0 admit(s) found"; \
	fi

# ── Generic Extraction Rules ───────────────────────────────────────
# Extract individual module to .krml
$(OUTPUT_DIR)/%.krml: verify | $(OUTPUT_DIR)
	$(FSTAR) --codegen krml \
	  --extract_module $(subst _,.,$*) \
	  src/impl/$(subst _,.,$*).fst \
	  --krmloutput $@

# Note: .krml → .c extraction requires KaRaMeL bundling configuration
# See bundle-specific targets below

# ── Extraction Bundles ─────────────────────────────────────────────
# List of modules to extract (dotted names)
EXTRACT_MODULES = \
  $(BUNDLE_IMPL_MODULES) \
  TLS13.Extract.Smoke

# Convert module names to .krml filenames
KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(EXTRACT_MODULES)))

.PHONY: extract-krml extract-connection extract-smoke \
  extract-driver-krml extract-driver-bundle

extract-krml: $(KRML_FILES)

# ──────────────────────────────────────────────────────────────────────────────
# KaRaMeL Extraction - .krml to C
# ──────────────────────────────────────────────────────────────────────────────

EXTRACT_DIR = _extract

# ── Bundle extraction (single-file) using proper KaRaMeL bundling ──────

BUNDLE_DIR = $(EXTRACT_DIR)/bundle

# TLS13.Impl.Client is the public API module.
BUNDLE_API_MODULE = TLS13.Impl.Client

# Implementation modules to bundle as internal to the client.
BUNDLE_IMPL_MODULES = \
  TLS13.Impl.Client \
  TLS13.Impl.Client.Types \
  TLS13.Impl.ConnectionState.Bounds \
  TLS13.Impl.ConnectionState.Model \
  TLS13.Impl.ConnectionState.Tags \
  TLS13.Impl.ConnectionState.Repr \
  TLS13.Impl.ConnectionState.Queries \
  TLS13.Impl.ConnectionState.Fail \
  TLS13.Impl.ConnectionState.LocalHandshake \
  TLS13.Impl.ConnectionState.LocalAuth \
  TLS13.Impl.ConnectionState.LocalSend \
  TLS13.Impl.ConnectionState.LocalApp \
  TLS13.Impl.ConnectionState.Network \
  TLS13.Impl.Handle.Alert \
  TLS13.Impl.Handle.ApplicationData \
  TLS13.Impl.Handle.ChangeCipherSpec \
  TLS13.Impl.Handle.DecodeError \
  TLS13.Impl.Handle.Dispatch \
  TLS13.Impl.Handle.Handshake \
  TLS13.Impl.Handle.Local \
  TLS13.Impl.Messages \
  TLS13.KeySchedule \
  TLS13.Record

# Non-API modules (everything except TLS13.Impl.Client)
BUNDLE_INTERNAL_MODULES = \
  TLS13.Impl.Client.Types,TLS13.Impl.ConnectionState.Bounds,\
  TLS13.Impl.ConnectionState.Model,TLS13.Impl.ConnectionState.Tags,\
  TLS13.Impl.ConnectionState.Repr,TLS13.Impl.ConnectionState.Queries,\
  TLS13.Impl.ConnectionState.Fail,TLS13.Impl.ConnectionState.LocalHandshake,\
  TLS13.Impl.ConnectionState.LocalAuth,TLS13.Impl.ConnectionState.LocalSend,\
  TLS13.Impl.ConnectionState.LocalApp,TLS13.Impl.ConnectionState.Network,\
  TLS13.Impl.Handle.Alert,TLS13.Impl.Handle.ApplicationData,\
  TLS13.Impl.Handle.ChangeCipherSpec,TLS13.Impl.Handle.DecodeError,\
  TLS13.Impl.Handle.Dispatch,TLS13.Impl.Handle.Handshake,\
  TLS13.Impl.Handle.Local,TLS13.Impl.Messages,\
  TLS13.KeySchedule,TLS13.Record

# Interface-only modules (not extracted, only .fsti):
# TLS13.Crypto, TLS13.X509, TLS13.MachineTypes, TLS13.IO,
# TLS13.Impl.Parser, TLS13.Impl.Serializer

# Extract all impl modules to .krml
BUNDLE_KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(BUNDLE_IMPL_MODULES)))

DRIVER_BUNDLE_DIR = $(EXTRACT_DIR)/driver_bundle
DRIVER_KRML_FILES = \
  $(BUNDLE_KRML_FILES) \
  $(OUTPUT_DIR)/TLS13_IO.krml \
  $(OUTPUT_DIR)/TLS13_Impl_Client_Driver.krml \
  $(OUTPUT_DIR)/TLS13_OpenSSL.krml

# Extract FStar.Pervasives.Native for tuple support
$(OUTPUT_DIR)/FStar_Pervasives_Native.krml: verify | $(OUTPUT_DIR)
	$(FSTAR_EXE) --codegen krml --extract_module FStar.Pervasives.Native \
	  --odir $(OUTPUT_DIR) --cache_dir $(CACHE_DIR) \
	  --already_cached Prims,FStar \
	  FStar.Pervasives.Native.fst

# Pattern rule for extracting modules to .krml
# Note: Some modules are interface-only (.fsti) and don't need extraction
$(OUTPUT_DIR)/%.krml: verify | $(OUTPUT_DIR)
	@if [ -f "src/impl/$(subst _,.,$*).fst" ]; then \
	  $(FSTAR) --codegen krml --extract_module $(subst _,.,$*) src/impl/$(subst _,.,$*).fst; \
	elif [ -f "src/impl/$(subst _,.,$*).fsti" ]; then \
	  $(FSTAR) --codegen krml --extract_module $(subst _,.,$*) src/impl/$(subst _,.,$*).fsti --krmloutput $@; \
	elif [ -f "src/spec/$(subst _,.,$*).fst" ]; then \
	  $(FSTAR) --codegen krml --extract_module $(subst _,.,$*) src/spec/$(subst _,.,$*).fst; \
	else \
	  echo "Note: $(subst _,.,$*) is interface-only, skipping extraction"; \
	  touch $@; \
	fi

extract-krml-bundle: $(BUNDLE_KRML_FILES) $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

extract-driver-krml: $(DRIVER_KRML_FILES) $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

# Generate C for the new buffer/event-oriented client API.
extract-bundle: extract-krml-bundle | $(BUNDLE_DIR)
	@echo "Extracting TLS13 modules without bundling (consistent ghost handling)..."
	@rm -f $(BUNDLE_DIR)/*.c $(BUNDLE_DIR)/*.h $(BUNDLE_DIR)/internal/*.h
	$(KRML_EXE) \
	  -tmpdir $(BUNDLE_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17-6 \
	  -add-include '<stdbool.h>' \
	  -add-include '"../../c_stubs/tls13_connection_backend.h"' \
	  -add-include '"../../c_stubs/tls13_crypto_external.h"' \
	  -add-include '"../../c_stubs/tls13_spec_types.h"' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix TLS13.Impl.Client \
	  $(BUNDLE_KRML_FILES) \
	  _output/FStar_Pervasives_Native.krml
	@echo ""
	@echo "Extraction complete:"
	@ls -lh $(BUNDLE_DIR)/TLS13_*.c 2>/dev/null | awk '{print "  " $$9 " (" $$5 ")"}'
	@echo ""
	@echo "  Main API (TLS13_Impl_Client.h):"
	@ls -lh $(BUNDLE_DIR)/TLS13_*.c 2>/dev/null | awk '{print "    " $$9 " (" $$5 ")"}'
	@echo ""
	@echo "Public API (TLS13_Impl_Client.h):"
	@grep "^[a-zA-Z_].*client_" $(BUNDLE_DIR)/TLS13_Impl_Client.h || true

$(BUNDLE_DIR):
	mkdir -p $@

$(DRIVER_BUNDLE_DIR):
	mkdir -p $@

extract-driver-bundle: extract-driver-krml | $(DRIVER_BUNDLE_DIR)
	@echo "Extracting TLS13 client driver slice..."
	@rm -f $(DRIVER_BUNDLE_DIR)/*.c $(DRIVER_BUNDLE_DIR)/*.h $(DRIVER_BUNDLE_DIR)/internal/*.h
	$(KRML_EXE) \
	  -tmpdir $(DRIVER_BUNDLE_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-17-6 \
	  -add-include '<stdbool.h>' \
	  -add-include '"../../c_stubs/tls13_connection_backend.h"' \
	  -add-include '"../../c_stubs/tls13_crypto_external.h"' \
	  -add-include '"../../c_stubs/tls13_spec_types.h"' \
	  -add-include '"../../c_stubs/tls13_openssl_karamel.h"' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix TLS13.Impl.Client \
	  $(DRIVER_KRML_FILES) \
	  _output/FStar_Pervasives_Native.krml

# ── Smoke Test Extraction ───────────────────────────────────────────────

SMOKE_DIR = $(EXTRACT_DIR)/smoke
SMOKE_KRML = $(OUTPUT_DIR)/TLS13_Extract_Smoke.krml
SMOKE_C = $(SMOKE_DIR)/TLS13_Extract_Smoke.c
SMOKE_H = $(SMOKE_DIR)/TLS13_Extract_Smoke.h

$(SMOKE_DIR):
	mkdir -p $@

$(SMOKE_C) $(SMOKE_H): $(SMOKE_KRML) | $(SMOKE_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles \
	  -tmpdir $(SMOKE_DIR) $(SMOKE_KRML)

extract-smoke: $(SMOKE_C) $(SMOKE_H)

# ──────────────────────────────────────────────────────────────────────────────
# C Stubs and Dependencies
# ──────────────────────────────────────────────────────────────────────────────

HACL_WRAPPER_SOURCES = \
  c_stubs/tls13_hacl_stubs.c \
  $(HACL_DIR)/Hacl_Hash_SHA2.c \
  $(HACL_DIR)/Hacl_HMAC.c \
  $(HACL_DIR)/Hacl_HKDF.c \
  $(HACL_DIR)/Hacl_Curve25519_51.c \
  $(HACL_DIR)/Hacl_AEAD_Chacha20Poly1305.c \
  $(HACL_DIR)/Hacl_Chacha20.c \
  $(HACL_DIR)/Hacl_MAC_Poly1305.c \
  $(HACL_DIR)/Lib_RandomBuffer_System.c

CONNECTION_BACKEND_SOURCES = \
  c_stubs/tls13_connection_backend_openssl.c \
  c_stubs/tls13_io_stubs.c \
  c_stubs/tls13_openssl_stubs.c \
  $(HACL_WRAPPER_SOURCES)

# Common C flags for all test builds
CFLAGS_COMMON = -Wall -Wextra -Wno-deprecated-declarations \
  -ffunction-sections -fdata-sections \
  -I c_stubs \
  -I runtime \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/minimal \
  -I $(HACL_DIR) \
  -I $(HACL_DIR)/internal \
  -I $(HACL_KI) \
  -I $(HACL_KL)

LDFLAGS_COMMON = -Wl,--gc-sections

# ──────────────────────────────────────────────────────────────────────────────
# Testing
# ──────────────────────────────────────────────────────────────────────────────
.PHONY: test test-extract-smoke test-connection-bindings \
  test-extracted-client-driver-slice \
  test-extracted-client-openssl-echo \
  test-key-schedule-bindings test-record-bindings \
  test-hacl-stubs test-openssl-stubs test-io-stubs \
  test-openssl-echo check-c-stubs

test: verify check-c-stubs test-hacl-stubs test-openssl-stubs \
  test-io-stubs test-extract-smoke test-connection-bindings \
  test-extracted-client-driver-slice test-key-schedule-bindings \
  test-record-bindings

# ── C Stub Syntax Check ────────────────────────────────────────────
check-c-stubs:
	$(CC) -fsyntax-only -Wall -Wextra -Wno-deprecated-declarations \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal \
	  -I $(HACL_KI) -I $(HACL_KL) \
	  $(wildcard c_stubs/*.c)

# ── HACL* Wrapper Tests ────────────────────────────────────────────
test/test_hacl_stubs: test/unit/test_hacl_stubs.c $(HACL_WRAPPER_SOURCES) \
  c_stubs/tls13_hacl_stubs.h | check-deps
	$(CC) $(CFLAGS_COMMON) \
	  test/unit/test_hacl_stubs.c $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -o $@

test-hacl-stubs: test/test_hacl_stubs
	./test/test_hacl_stubs

# ── OpenSSL Wrapper Tests ──────────────────────────────────────────
test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der: \
  scripts/generate-test-certs.sh
	scripts/generate-test-certs.sh test/certs

test/test_openssl_stubs: c_stubs/tls13_openssl_stubs.c \
  c_stubs/tls13_openssl_stubs.h test/unit/test_openssl_stubs.c | check-deps
	$(CC) -Wall -Wextra -I c_stubs \
	  c_stubs/tls13_openssl_stubs.c test/unit/test_openssl_stubs.c \
	  -lssl -lcrypto -o $@

test-openssl-stubs: test/test_openssl_stubs test/certs/chain.pem \
  test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der
	./test/test_openssl_stubs test/certs/ca.pem test/certs/chain.pem \
	  test/certs/leaf.key test/certs/leaf.der

# ── I/O Stub Tests ─────────────────────────────────────────────────
test/test_io_stubs: c_stubs/tls13_io_stubs.c c_stubs/tls13_io_stubs.h \
  test/unit/test_io_stubs.c
	$(CC) -Wall -Wextra -I c_stubs \
	  c_stubs/tls13_io_stubs.c test/unit/test_io_stubs.c -o $@

test-io-stubs: test/test_io_stubs
	./test/test_io_stubs

# ── Extracted Code Tests ───────────────────────────────────────────
test/test_extract_smoke: test/unit/test_extract_smoke.c $(SMOKE_C) $(SMOKE_H)
	$(CC) -Wall -Wextra \
	  -I $(SMOKE_DIR) \
	  -I $(KRML_HOME)/include \
	  -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(SMOKE_C) test/unit/test_extract_smoke.c -o $@

test-extract-smoke: test/test_extract_smoke
	./test/test_extract_smoke

test/test_connection_bindings: test/unit/test_connection_bindings.c extract-bundle $(HACL_OBJECTS)
	$(CC) $(CFLAGS_COMMON) \
	  -I_extract/bundle -I_extract/bundle/internal \
	  _extract/bundle/*.c \
	  c_stubs/tls13_crypto_external.c \
	  c_stubs/tls13_pulse_shims.c \
	  test/unit/test_connection_bindings.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -o $@

test-connection-bindings: test/test_connection_bindings
	./test/test_connection_bindings

test/test_extracted_client_driver_slice: \
  test/unit/test_extracted_client_driver_slice.c extract-driver-bundle \
  c_stubs/tls13_io_karamel.c c_stubs/tls13_io_karamel.h \
  c_stubs/tls13_io_stubs.c c_stubs/tls13_io_stubs.h \
  c_stubs/tls13_openssl_karamel.c c_stubs/tls13_openssl_karamel.h \
  c_stubs/tls13_openssl_stubs.c c_stubs/tls13_openssl_stubs.h $(HACL_OBJECTS)
	$(CC) $(CFLAGS_COMMON) \
	  -I_extract/driver_bundle -I_extract/driver_bundle/internal \
	  _extract/driver_bundle/*.c \
	  c_stubs/tls13_crypto_external.c \
	  c_stubs/tls13_pulse_shims.c \
	  c_stubs/tls13_io_karamel.c \
	  c_stubs/tls13_io_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/unit/test_extracted_client_driver_slice.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -lssl -lcrypto -o $@

test-extracted-client-driver-slice: test/test_extracted_client_driver_slice
	./test/test_extracted_client_driver_slice

test/test_extracted_client_openssl_echo: \
  test/unit/test_extracted_client_openssl_echo.c extract-driver-bundle \
  runtime/tls13_client_driver.c runtime/tls13_client_driver.h \
  c_stubs/tls13_io_karamel.c c_stubs/tls13_io_karamel.h \
  c_stubs/tls13_io_stubs.c c_stubs/tls13_io_stubs.h \
  c_stubs/tls13_openssl_karamel.c c_stubs/tls13_openssl_karamel.h \
  c_stubs/tls13_openssl_stubs.c c_stubs/tls13_openssl_stubs.h $(HACL_OBJECTS)
	$(CC) $(CFLAGS_COMMON) \
	  -I_extract/driver_bundle -I_extract/driver_bundle/internal \
	  _extract/driver_bundle/*.c \
	  c_stubs/tls13_crypto_external.c \
	  c_stubs/tls13_pulse_shims.c \
	  runtime/tls13_client_driver.c \
	  c_stubs/tls13_io_karamel.c \
	  c_stubs/tls13_io_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/unit/test_extracted_client_openssl_echo.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -lssl -lcrypto -o $@

test-extracted-client-openssl-echo: test-openssl-echo

test/test_key_schedule_bindings: test/unit/test_key_schedule_bindings.c \
  $(OUTPUT_DIR)/TLS13_KeySchedule.krml \
  c_stubs/tls13_crypto_external.h \
  $(HACL_WRAPPER_SOURCES) | check-deps $(EXTRACT_DIR)
	@mkdir -p $(EXTRACT_DIR)/key-schedule
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_crypto_external.h"' \
	  -tmpdir $(EXTRACT_DIR)/key-schedule \
	  $(OUTPUT_DIR)/TLS13_KeySchedule.krml
	$(CC) $(CFLAGS_COMMON) \
	  -I $(EXTRACT_DIR)/key-schedule \
	  $(EXTRACT_DIR)/key-schedule/TLS13_KeySchedule.c \
	  test/unit/test_key_schedule_bindings.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -o $@

test-key-schedule-bindings: test/test_key_schedule_bindings
	./test/test_key_schedule_bindings

test/test_record_bindings: test/unit/test_record_bindings.c \
  $(OUTPUT_DIR)/TLS13_Record.krml \
  c_stubs/tls13_crypto_external.h \
  c_stubs/tls13_pulse_shims.c \
  $(HACL_WRAPPER_SOURCES) | check-deps $(EXTRACT_DIR)
	@mkdir -p $(EXTRACT_DIR)/record
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_crypto_external.h"' \
	  -tmpdir $(EXTRACT_DIR)/record \
	  $(OUTPUT_DIR)/TLS13_Record.krml
	$(CC) $(CFLAGS_COMMON) \
	  -I $(EXTRACT_DIR)/record \
	  $(EXTRACT_DIR)/record/TLS13_Record.c \
	  test/unit/test_record_bindings.c \
	  c_stubs/tls13_pulse_shims.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(LDFLAGS_COMMON) -o $@

test-record-bindings: test/test_record_bindings
	./test/test_record_bindings

# ── Unit Tests ─────────────────────────────────────────────────────
# These are low-level tests for individual modules (for development only)
test/openssl_echo_server: test/openssl_echo_server.c
	$(CC) -Wall -Wextra test/openssl_echo_server.c \
	  -lssl -lcrypto -o $@

test-client:
	@echo "OpenSSL interop is pending the new buffer/event network driver."

test-openssl-echo: test/openssl_echo_server test/test_extracted_client_openssl_echo \
  test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der
	@rm -f test/openssl_echo_server.port test/openssl_echo_server.log
	@set -e; \
	  ./test/openssl_echo_server 0 test/certs/chain.pem test/certs/leaf.key \
	    test/openssl_echo_server.port > test/openssl_echo_server.log 2>&1 & \
	  server_pid=$$!; \
	  trap 'kill '"$$server_pid"' 2>/dev/null || true; wait '"$$server_pid"' 2>/dev/null || true; rm -f test/openssl_echo_server.port' EXIT; \
	  for _i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50; do \
	    test -s test/openssl_echo_server.port && break; \
	    sleep 0.1; \
	  done; \
	  if ! test -s test/openssl_echo_server.port; then \
	    echo "OpenSSL echo server did not start"; \
	    cat test/openssl_echo_server.log; \
	    exit 1; \
	  fi; \
	  port=$$(cat test/openssl_echo_server.port); \
	  ./test/test_extracted_client_openssl_echo 127.0.0.1 $$port test/certs/ca.pem; \
	  wait $$server_pid

# ── Dependency Checks ──────────────────────────────────────────────
check-toolchain:
	@if ! command -v $(FSTAR_EXE) >/dev/null 2>&1; then \
	  echo "F* not found at $(FSTAR_EXE). Run ./setup.sh or override FSTAR_EXE."; \
	  exit 1; \
	fi

check-deps:
	@scripts/check-openssl.sh >/dev/null
	@test -d third_party/hacl-star/dist/gcc-compatible || \
	  { echo "Missing HACL* C snapshot; run scripts/fetch-hacl-star.sh"; exit 1; }
	@test -f third_party/rfc/rfc8446.txt || \
	  { echo "Missing RFC 8446 cache; run scripts/fetch-rfcs.sh"; exit 1; }
	@test -f third_party/rfc/rfc8448.txt || \
	  { echo "Missing RFC 8448 cache; run scripts/fetch-rfcs.sh"; exit 1; }

# ── Cleanup ────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR) .depend
	rm -f test/test_hacl_stubs test/test_openssl_stubs \
	  test/test_record_bindings test/test_io_stubs \
	  test/test_extract_smoke test/test_connection_bindings \
	  test/test_key_schedule_bindings \
	  test/test_extracted_client_openssl_echo \
	  test/openssl_echo_server test/openssl_echo_server.port \
	  test/openssl_echo_server.log
	find src test -name '*.checked' -delete

.PHONY: all verify test extract-krml extract-connection extract-smoke extract-bundle \
  test-extract-smoke test-connection-bindings test-key-schedule-bindings \
  test-record-bindings test-hacl-stubs test-openssl-stubs test-io-stubs \
  test-extracted-client-openssl-echo \
  test-client test-openssl-echo check-c-stubs check-toolchain check-deps clean
