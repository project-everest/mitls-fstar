FSTAR_HOME ?= $(CURDIR)/tools/FStar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML_EXE   ?= $(KRML_HOME)/krml

CACHE_DIR   = _cache
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract
HACL_DIR    = third_party/hacl-star/dist/gcc-compatible
HACL_KI     = third_party/hacl-star/dist/karamel/include
HACL_KL     = third_party/hacl-star/dist/karamel/krmllib/dist/minimal

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
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

SPEC_FILES = \
  src/spec/TLS13.Bytes.fst \
  src/spec/TLS13.Types.fst \
  src/spec/TLS13.Crypto.Spec.fsti \
  src/spec/TLS13.X509.Spec.fsti \
  src/spec/TLS13.Transcript.fst \
  src/spec/TLS13.Keys.fst \
  src/spec/TLS13.Record.Spec.fst \
  src/spec/TLS13.Handshake.Spec.fst \
  src/spec/TLS13.Wire.Spec.fsti \
  src/spec/TLS13.Wire.Spec.fst \
  src/spec/TLS13.StateMachine.fst \
  src/spec/TLS13.StateMachine.Lemmas.fst

IMPL_FILES = \
  src/impl/TLS13.MachineTypes.fsti \
  src/impl/TLS13.Extract.Smoke.fst \
  src/impl/TLS13.State.fst \
  src/impl/TLS13.Handshake.StateDriver.fst \
  src/impl/TLS13.Connection.StateDriver.fst \
  src/impl/TLS13.Crypto.fsti \
  src/impl/TLS13.KeySchedule.fsti \
  src/impl/TLS13.KeySchedule.fst \
  src/impl/TLS13.X509.fsti \
  src/impl/TLS13.Record.Framing.fsti \
  src/impl/TLS13.Record.Framing.fst \
  src/impl/TLS13.Record.fsti \
  src/impl/TLS13.Record.fst \
  src/impl/TLS13.Parse.fsti \
  src/impl/TLS13.Serialize.fsti \
  src/impl/TLS13.IO.fsti \
  src/impl/TLS13.Handshake.External.fsti \
  src/impl/TLS13.Handshake.fsti \
  src/impl/TLS13.Handshake.fst \
  src/impl/TLS13.Handshake.Driver.fst \
  src/impl/TLS13.Connection.External.fsti \
  src/impl/TLS13.Connection.fsti \
  src/impl/TLS13.Connection.fst \
  src/impl/TLS13.Connection.Driver.fst

ALL_FILES = $(SPEC_FILES) $(IMPL_FILES)

EXTRACT_SMOKE_DIR  = $(EXTRACT_DIR)/smoke
EXTRACT_SMOKE_KRML = $(EXTRACT_SMOKE_DIR)/out.krml
EXTRACT_SMOKE_C    = $(EXTRACT_SMOKE_DIR)/TLS13_Extract_Smoke.c
EXTRACT_SMOKE_H    = $(EXTRACT_SMOKE_DIR)/TLS13_Extract_Smoke.h
EXTRACT_CONNECTION_DRIVER_DIR  = $(EXTRACT_DIR)/connection-driver
EXTRACT_CONNECTION_DRIVER_KRML = $(EXTRACT_CONNECTION_DRIVER_DIR)/TLS13_Connection_Driver.krml
EXTRACT_CONNECTION_DRIVER_C    = $(EXTRACT_CONNECTION_DRIVER_DIR)/TLS13_Connection_Driver.c
EXTRACT_CONNECTION_DRIVER_H    = $(EXTRACT_CONNECTION_DRIVER_DIR)/TLS13_Connection_Driver.h
EXTRACT_CONNECTION_DIR  = $(EXTRACT_DIR)/connection
EXTRACT_CONNECTION_KRML = $(EXTRACT_CONNECTION_DIR)/TLS13_Connection.krml
EXTRACT_CONNECTION_C    = $(EXTRACT_CONNECTION_DIR)/TLS13_Connection.c
EXTRACT_CONNECTION_H    = $(EXTRACT_CONNECTION_DIR)/TLS13_Connection.h
EXTRACT_HANDSHAKE_DRIVER_DIR  = $(EXTRACT_DIR)/handshake-driver
EXTRACT_HANDSHAKE_DRIVER_KRML = $(EXTRACT_HANDSHAKE_DRIVER_DIR)/TLS13_Handshake_Driver.krml
EXTRACT_HANDSHAKE_DRIVER_C    = $(EXTRACT_HANDSHAKE_DRIVER_DIR)/TLS13_Handshake_Driver.c
EXTRACT_HANDSHAKE_DRIVER_H    = $(EXTRACT_HANDSHAKE_DRIVER_DIR)/TLS13_Handshake_Driver.h
EXTRACT_HANDSHAKE_DIR  = $(EXTRACT_DIR)/handshake
EXTRACT_HANDSHAKE_KRML = $(EXTRACT_HANDSHAKE_DIR)/TLS13_Handshake.krml
EXTRACT_HANDSHAKE_C    = $(EXTRACT_HANDSHAKE_DIR)/TLS13_Handshake.c
EXTRACT_HANDSHAKE_H    = $(EXTRACT_HANDSHAKE_DIR)/TLS13_Handshake.h
EXTRACT_KEY_SCHEDULE_DIR  = $(EXTRACT_DIR)/key-schedule
EXTRACT_KEY_SCHEDULE_KRML = $(EXTRACT_KEY_SCHEDULE_DIR)/TLS13_KeySchedule.krml
EXTRACT_KEY_SCHEDULE_C    = $(EXTRACT_KEY_SCHEDULE_DIR)/TLS13_KeySchedule.c
EXTRACT_KEY_SCHEDULE_H    = $(EXTRACT_KEY_SCHEDULE_DIR)/TLS13_KeySchedule.h
EXTRACT_RECORD_DIR  = $(EXTRACT_DIR)/record
EXTRACT_RECORD_KRML = $(EXTRACT_RECORD_DIR)/TLS13_Record.krml
EXTRACT_RECORD_C    = $(EXTRACT_RECORD_DIR)/TLS13_Record.c
EXTRACT_RECORD_H    = $(EXTRACT_RECORD_DIR)/TLS13_Record.h
EXTRACT_RECORD_FRAMING_DIR  = $(EXTRACT_DIR)/record-framing
EXTRACT_RECORD_FRAMING_KRML = $(EXTRACT_RECORD_FRAMING_DIR)/TLS13_Record_Framing.krml
EXTRACT_RECORD_FRAMING_C    = $(EXTRACT_RECORD_FRAMING_DIR)/TLS13_Record_Framing.c
EXTRACT_RECORD_FRAMING_H    = $(EXTRACT_RECORD_FRAMING_DIR)/TLS13_Record_Framing.h

.PHONY: all verify test extract-smoke extract-connection-driver-krml extract-connection-driver-c extract-connection-krml extract-connection-c extract-handshake-driver-krml extract-handshake-driver-c extract-handshake-krml extract-handshake-c extract-key-schedule-krml extract-key-schedule-c extract-record-krml extract-record-c extract-record-framing-krml extract-record-framing-c test-extract-smoke test-connection-driver-bindings test-connection-bindings test-handshake-driver-bindings test-handshake-bindings test-key-schedule-bindings test-record-bindings check-c-stubs test-hacl-stubs test-openssl-stubs test-wire-stubs test-record-stubs test-io-stubs test-openssl-echo check-toolchain check-deps clean

all: verify

test: verify check-c-stubs test-hacl-stubs test-openssl-stubs test-wire-stubs test-record-stubs test-io-stubs test-extract-smoke test-connection-driver-bindings test-connection-bindings test-handshake-driver-bindings test-handshake-bindings test-key-schedule-bindings test-record-bindings

check-toolchain:
	@if ! command -v $(FSTAR_EXE) >/dev/null 2>&1; then \
	  echo "F* not found at $(FSTAR_EXE). Run ./setup.sh or override FSTAR_EXE."; \
	  exit 1; \
	fi

check-deps:
	@scripts/check-openssl.sh >/dev/null
	@test -d third_party/hacl-star/dist/gcc-compatible || { echo "Missing HACL* C snapshot; run scripts/fetch-hacl-star.sh"; exit 1; }
	@test -f third_party/rfc/rfc8446.txt || { echo "Missing RFC 8446 cache; run scripts/fetch-rfcs.sh"; exit 1; }
	@test -f third_party/rfc/rfc8448.txt || { echo "Missing RFC 8448 cache; run scripts/fetch-rfcs.sh"; exit 1; }

$(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR):
	mkdir -p $@

$(EXTRACT_SMOKE_DIR):
	mkdir -p $@

$(EXTRACT_CONNECTION_DRIVER_DIR):
	mkdir -p $@

$(EXTRACT_CONNECTION_DIR):
	mkdir -p $@

$(EXTRACT_HANDSHAKE_DRIVER_DIR):
	mkdir -p $@

$(EXTRACT_HANDSHAKE_DIR):
	mkdir -p $@

$(EXTRACT_KEY_SCHEDULE_DIR):
	mkdir -p $@

$(EXTRACT_RECORD_DIR):
	mkdir -p $@

$(EXTRACT_RECORD_FRAMING_DIR):
	mkdir -p $@

verify: check-deps check-toolchain $(CACHE_DIR) $(OUTPUT_DIR)
	@set -e; for f in $(ALL_FILES); do \
	  echo "$(FSTAR) $$f"; \
	  $(FSTAR) $$f; \
	done
	@echo "All F* modules verified"

check-c-stubs:
	$(CC) -fsyntax-only -Wall -Wextra -Wno-deprecated-declarations \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  c_stubs/*.c

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

HACL_STUB_TEST_SOURCES = \
  test/test_hacl_stubs.c \
  $(HACL_WRAPPER_SOURCES)

CONNECTION_PROBE_SOURCES = \
  c_stubs/tls13_connection_probe.c \
  c_stubs/tls13_connection_probe.h \
  c_stubs/tls13_connection_external.h \
  c_stubs/tls13_wire_stubs.c \
  c_stubs/tls13_wire_stubs.h \
  c_stubs/tls13_io_stubs.c \
  c_stubs/tls13_io_stubs.h \
  c_stubs/tls13_openssl_stubs.c \
  c_stubs/tls13_openssl_stubs.h \
  $(HACL_WRAPPER_SOURCES)

test/test_hacl_stubs: $(HACL_STUB_TEST_SOURCES) c_stubs/tls13_hacl_stubs.h | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(HACL_STUB_TEST_SOURCES) -Wl,--gc-sections -o $@

test-hacl-stubs: test/test_hacl_stubs
	./test/test_hacl_stubs

test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der: scripts/generate-test-certs.sh
	scripts/generate-test-certs.sh test/certs

test/test_openssl_stubs: c_stubs/tls13_openssl_stubs.c c_stubs/tls13_openssl_stubs.h test/test_openssl_stubs.c | check-deps
	$(CC) -Wall -Wextra -I c_stubs \
	  c_stubs/tls13_openssl_stubs.c test/test_openssl_stubs.c \
	  -lssl -lcrypto -o $@

test/openssl_echo_server: test/openssl_echo_server.c | check-deps
	$(CC) -Wall -Wextra test/openssl_echo_server.c \
	  -lssl -lcrypto -o $@

test/test_clienthello_openssl_probe: $(CONNECTION_PROBE_SOURCES) test/test_clienthello_openssl_probe.c | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(HACL_WRAPPER_SOURCES) c_stubs/tls13_wire_stubs.c c_stubs/tls13_io_stubs.c c_stubs/tls13_openssl_stubs.c c_stubs/tls13_connection_probe.c test/test_clienthello_openssl_probe.c \
	  -Wl,--gc-sections -lssl -lcrypto -o $@

test-openssl-stubs: test/test_openssl_stubs test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der
	./test/test_openssl_stubs test/certs/ca.pem test/certs/chain.pem test/certs/leaf.key test/certs/leaf.der

test/test_extracted_connection_driver_openssl: $(CONNECTION_PROBE_SOURCES) test/test_extracted_connection_driver_openssl.c $(EXTRACT_CONNECTION_DRIVER_C) $(EXTRACT_CONNECTION_DRIVER_H) $(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_H) c_stubs/tls13_handshake_external.h | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -DTLS13_CONNECTION_PROBE_USE_EXTRACTED_HANDSHAKE \
	  -I $(EXTRACT_CONNECTION_DRIVER_DIR) -I $(EXTRACT_HANDSHAKE_DRIVER_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(EXTRACT_CONNECTION_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_C) $(HACL_WRAPPER_SOURCES) c_stubs/tls13_wire_stubs.c c_stubs/tls13_io_stubs.c c_stubs/tls13_openssl_stubs.c c_stubs/tls13_connection_probe.c test/test_extracted_connection_driver_openssl.c \
	  -Wl,--gc-sections -lssl -lcrypto -o $@

test/test_extracted_connection_wrapper_openssl: $(CONNECTION_PROBE_SOURCES) test/test_extracted_connection_wrapper_openssl.c $(EXTRACT_CONNECTION_C) $(EXTRACT_CONNECTION_H) $(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_H) $(EXTRACT_KEY_SCHEDULE_C) $(EXTRACT_KEY_SCHEDULE_H) $(EXTRACT_RECORD_C) $(EXTRACT_RECORD_H) $(EXTRACT_RECORD_FRAMING_C) $(EXTRACT_RECORD_FRAMING_H) c_stubs/tls13_connection_external_layer.h c_stubs/tls13_crypto_external.c c_stubs/tls13_pulse_shims.c | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -DTLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER \
	  -DTLS13_CONNECTION_PROBE_USE_EXTRACTED_HANDSHAKE \
	  -DTLS13_CONNECTION_PROBE_USE_EXTRACTED_KEY_SCHEDULE \
	  -I $(EXTRACT_CONNECTION_DIR) -I $(EXTRACT_HANDSHAKE_DRIVER_DIR) -I $(EXTRACT_KEY_SCHEDULE_DIR) -I $(EXTRACT_RECORD_DIR) -I $(EXTRACT_RECORD_FRAMING_DIR) \
	  -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(EXTRACT_CONNECTION_C) $(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_KEY_SCHEDULE_C) $(EXTRACT_RECORD_C) $(EXTRACT_RECORD_FRAMING_C) \
	  $(HACL_WRAPPER_SOURCES) c_stubs/tls13_crypto_external.c c_stubs/tls13_pulse_shims.c \
	  c_stubs/tls13_wire_stubs.c c_stubs/tls13_io_stubs.c c_stubs/tls13_openssl_stubs.c c_stubs/tls13_connection_probe.c \
	  test/test_extracted_connection_wrapper_openssl.c \
	  -Wl,--gc-sections -lssl -lcrypto -o $@

test-openssl-echo: test/openssl_echo_server test/test_clienthello_openssl_probe test/test_extracted_connection_driver_openssl test/test_extracted_connection_wrapper_openssl
	scripts/test-openssl-echo.sh

test/test_wire_stubs: c_stubs/tls13_wire_stubs.c c_stubs/tls13_wire_stubs.h test/test_wire_stubs.c
	$(CC) -Wall -Wextra -I c_stubs \
	  c_stubs/tls13_wire_stubs.c test/test_wire_stubs.c \
	  -o $@

test-wire-stubs: test/test_wire_stubs
	./test/test_wire_stubs

test/test_record_stubs: $(HACL_WRAPPER_SOURCES) c_stubs/tls13_hacl_stubs.h c_stubs/tls13_wire_stubs.c c_stubs/tls13_wire_stubs.h test/test_record_stubs.c | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(HACL_WRAPPER_SOURCES) c_stubs/tls13_wire_stubs.c test/test_record_stubs.c \
	  -Wl,--gc-sections -o $@

test-record-stubs: test/test_record_stubs
	./test/test_record_stubs

test/test_io_stubs: c_stubs/tls13_io_stubs.c c_stubs/tls13_io_stubs.h test/test_io_stubs.c
	$(CC) -Wall -Wextra -I c_stubs \
	  c_stubs/tls13_io_stubs.c test/test_io_stubs.c \
	  -o $@

test-io-stubs: test/test_io_stubs
	./test/test_io_stubs

$(EXTRACT_SMOKE_KRML): src/impl/TLS13.Extract.Smoke.fst | check-toolchain $(EXTRACT_SMOKE_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(EXTRACT_SMOKE_DIR) --odir $(EXTRACT_SMOKE_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  --include src/impl $<
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(EXTRACT_SMOKE_DIR) --odir $(EXTRACT_SMOKE_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  --include src/impl --codegen krml --extract 'TLS13.Extract.Smoke' --krmloutput $@ $<

$(EXTRACT_SMOKE_C) $(EXTRACT_SMOKE_H): $(EXTRACT_SMOKE_KRML) | $(EXTRACT_SMOKE_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -tmpdir $(EXTRACT_SMOKE_DIR) $(EXTRACT_SMOKE_KRML)

extract-smoke: $(EXTRACT_SMOKE_C) $(EXTRACT_SMOKE_H)

$(EXTRACT_CONNECTION_DRIVER_KRML): src/impl/TLS13.Connection.Driver.fst verify | $(EXTRACT_CONNECTION_DRIVER_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Connection.Driver \
	  --krmloutput $@ $<

extract-connection-driver-krml: $(EXTRACT_CONNECTION_DRIVER_KRML)

$(EXTRACT_CONNECTION_DRIVER_C) $(EXTRACT_CONNECTION_DRIVER_H): $(EXTRACT_CONNECTION_DRIVER_KRML) c_stubs/tls13_connection_external.h | $(EXTRACT_CONNECTION_DRIVER_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_connection_external.h"' \
	  -tmpdir $(EXTRACT_CONNECTION_DRIVER_DIR) $(EXTRACT_CONNECTION_DRIVER_KRML)

extract-connection-driver-c: $(EXTRACT_CONNECTION_DRIVER_C) $(EXTRACT_CONNECTION_DRIVER_H)

$(EXTRACT_CONNECTION_KRML): src/impl/TLS13.Connection.fst verify | $(EXTRACT_CONNECTION_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Connection \
	  --krmloutput $@ $<

extract-connection-krml: $(EXTRACT_CONNECTION_KRML)

$(EXTRACT_CONNECTION_C) $(EXTRACT_CONNECTION_H): $(EXTRACT_CONNECTION_KRML) c_stubs/tls13_connection_external_layer.h | $(EXTRACT_CONNECTION_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_connection_external_layer.h"' \
	  -tmpdir $(EXTRACT_CONNECTION_DIR) $(EXTRACT_CONNECTION_KRML)

extract-connection-c: $(EXTRACT_CONNECTION_C) $(EXTRACT_CONNECTION_H)

$(EXTRACT_HANDSHAKE_DRIVER_KRML): src/impl/TLS13.Handshake.Driver.fst verify | $(EXTRACT_HANDSHAKE_DRIVER_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Handshake.Driver \
	  --krmloutput $@ $<

extract-handshake-driver-krml: $(EXTRACT_HANDSHAKE_DRIVER_KRML)

$(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_H): $(EXTRACT_HANDSHAKE_DRIVER_KRML) c_stubs/tls13_handshake_external.h | $(EXTRACT_HANDSHAKE_DRIVER_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_handshake_external.h"' \
	  -tmpdir $(EXTRACT_HANDSHAKE_DRIVER_DIR) $(EXTRACT_HANDSHAKE_DRIVER_KRML)

extract-handshake-driver-c: $(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_H)

$(EXTRACT_HANDSHAKE_KRML): src/impl/TLS13.Handshake.fst verify | $(EXTRACT_HANDSHAKE_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Handshake \
	  --krmloutput $@ $<

extract-handshake-krml: $(EXTRACT_HANDSHAKE_KRML)

$(EXTRACT_HANDSHAKE_C) $(EXTRACT_HANDSHAKE_H): $(EXTRACT_HANDSHAKE_KRML) c_stubs/tls13_handshake_external_layer.h | $(EXTRACT_HANDSHAKE_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_handshake_external_layer.h"' \
	  -tmpdir $(EXTRACT_HANDSHAKE_DIR) $(EXTRACT_HANDSHAKE_KRML)

extract-handshake-c: $(EXTRACT_HANDSHAKE_C) $(EXTRACT_HANDSHAKE_H)

$(EXTRACT_KEY_SCHEDULE_KRML): src/impl/TLS13.KeySchedule.fst verify | $(EXTRACT_KEY_SCHEDULE_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.KeySchedule \
	  --krmloutput $@ $<

extract-key-schedule-krml: $(EXTRACT_KEY_SCHEDULE_KRML)

$(EXTRACT_KEY_SCHEDULE_C) $(EXTRACT_KEY_SCHEDULE_H): $(EXTRACT_KEY_SCHEDULE_KRML) c_stubs/tls13_crypto_external.h | $(EXTRACT_KEY_SCHEDULE_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_crypto_external.h"' \
	  -tmpdir $(EXTRACT_KEY_SCHEDULE_DIR) $(EXTRACT_KEY_SCHEDULE_KRML)

extract-key-schedule-c: $(EXTRACT_KEY_SCHEDULE_C) $(EXTRACT_KEY_SCHEDULE_H)

$(EXTRACT_RECORD_KRML): src/impl/TLS13.Record.fst verify | $(EXTRACT_RECORD_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Record \
	  --krmloutput $@ $<

extract-record-krml: $(EXTRACT_RECORD_KRML)

$(EXTRACT_RECORD_C) $(EXTRACT_RECORD_H): $(EXTRACT_RECORD_KRML) c_stubs/tls13_crypto_external.h | $(EXTRACT_RECORD_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_crypto_external.h"' \
	  -tmpdir $(EXTRACT_RECORD_DIR) $(EXTRACT_RECORD_KRML)

extract-record-c: $(EXTRACT_RECORD_C) $(EXTRACT_RECORD_H)

$(EXTRACT_RECORD_FRAMING_KRML): src/impl/TLS13.Record.Framing.fst verify | $(EXTRACT_RECORD_FRAMING_DIR)
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore -TLS13' \
	  $(INCLUDES) --codegen krml --extract_module TLS13.Record.Framing \
	  --krmloutput $@ $<

extract-record-framing-krml: $(EXTRACT_RECORD_FRAMING_KRML)

$(EXTRACT_RECORD_FRAMING_C) $(EXTRACT_RECORD_FRAMING_H): $(EXTRACT_RECORD_FRAMING_KRML) c_stubs/tls13_crypto_external.h | $(EXTRACT_RECORD_FRAMING_DIR)
	$(KRML_EXE) -skip-compilation -skip-makefiles -warn-error -2 \
	  -add-include '"tls13_crypto_external.h"' \
	  -tmpdir $(EXTRACT_RECORD_FRAMING_DIR) $(EXTRACT_RECORD_FRAMING_KRML)

extract-record-framing-c: $(EXTRACT_RECORD_FRAMING_C) $(EXTRACT_RECORD_FRAMING_H)

test/test_extract_smoke: test/test_extract_smoke.c $(EXTRACT_SMOKE_C) $(EXTRACT_SMOKE_H)
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_SMOKE_DIR) -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_SMOKE_C) test/test_extract_smoke.c \
	  -o $@

test-extract-smoke: test/test_extract_smoke
	./test/test_extract_smoke

test/test_connection_driver_bindings: test/test_connection_driver_bindings.c $(EXTRACT_CONNECTION_DRIVER_C) $(EXTRACT_CONNECTION_DRIVER_H) c_stubs/tls13_connection_external.h
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_CONNECTION_DRIVER_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_CONNECTION_DRIVER_C) test/test_connection_driver_bindings.c \
	  -o $@

test-connection-driver-bindings: test/test_connection_driver_bindings
	./test/test_connection_driver_bindings

test/test_connection_bindings: test/test_connection_bindings.c $(EXTRACT_CONNECTION_C) $(EXTRACT_CONNECTION_H) c_stubs/tls13_connection_external_layer.h
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_CONNECTION_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_CONNECTION_C) test/test_connection_bindings.c \
	  -o $@

test-connection-bindings: test/test_connection_bindings
	./test/test_connection_bindings

test/test_handshake_driver_bindings: test/test_handshake_driver_bindings.c $(EXTRACT_HANDSHAKE_DRIVER_C) $(EXTRACT_HANDSHAKE_DRIVER_H) c_stubs/tls13_handshake_external.h c_stubs/tls13_connection_external.h
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_HANDSHAKE_DRIVER_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_HANDSHAKE_DRIVER_C) test/test_handshake_driver_bindings.c \
	  -o $@

test-handshake-driver-bindings: test/test_handshake_driver_bindings
	./test/test_handshake_driver_bindings

test/test_handshake_bindings: test/test_handshake_bindings.c $(EXTRACT_HANDSHAKE_C) $(EXTRACT_HANDSHAKE_H) c_stubs/tls13_handshake_external_layer.h
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_HANDSHAKE_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_HANDSHAKE_C) test/test_handshake_bindings.c \
	  -o $@

test-handshake-bindings: test/test_handshake_bindings
	./test/test_handshake_bindings

test/test_key_schedule_bindings: test/test_key_schedule_bindings.c $(EXTRACT_KEY_SCHEDULE_C) $(EXTRACT_KEY_SCHEDULE_H) c_stubs/tls13_crypto_external.h $(HACL_WRAPPER_SOURCES) | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I $(EXTRACT_KEY_SCHEDULE_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(EXTRACT_KEY_SCHEDULE_C) test/test_key_schedule_bindings.c $(HACL_WRAPPER_SOURCES) \
	  -Wl,--gc-sections -o $@

test-key-schedule-bindings: test/test_key_schedule_bindings
	./test/test_key_schedule_bindings

test/test_record_bindings: test/test_record_bindings.c $(EXTRACT_RECORD_C) $(EXTRACT_RECORD_H) c_stubs/tls13_crypto_external.h c_stubs/tls13_pulse_shims.c $(HACL_WRAPPER_SOURCES) | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I $(EXTRACT_RECORD_DIR) -I c_stubs -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(EXTRACT_RECORD_C) test/test_record_bindings.c c_stubs/tls13_pulse_shims.c $(HACL_WRAPPER_SOURCES) \
	  -Wl,--gc-sections -o $@

test-record-bindings: test/test_record_bindings
	./test/test_record_bindings

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f test/test_hacl_stubs test/test_openssl_stubs test/test_wire_stubs test/test_record_stubs test/test_record_bindings test/test_io_stubs test/test_extract_smoke test/test_connection_driver_bindings test/test_connection_bindings test/test_handshake_driver_bindings test/test_handshake_bindings test/test_key_schedule_bindings test/test_clienthello_openssl_probe test/test_extracted_connection_driver_openssl test/test_extracted_connection_wrapper_openssl test/openssl_echo_server
	find src test -name '*.checked' -delete
