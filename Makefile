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
  src/spec/TLS13.StateMachine.fst \
  src/spec/TLS13.StateMachine.Lemmas.fst

IMPL_FILES = \
  src/impl/TLS13.LowTypes.fsti \
  src/impl/TLS13.Extract.Smoke.fst \
  src/impl/TLS13.State.fst \
  src/impl/TLS13.Handshake.StateDriver.fst \
  src/impl/TLS13.Connection.StateDriver.fst \
  src/impl/TLS13.Crypto.fsti \
  src/impl/TLS13.KeySchedule.fsti \
  src/impl/TLS13.X509.fsti \
  src/impl/TLS13.Record.fsti \
  src/impl/TLS13.Parse.fsti \
  src/impl/TLS13.Serialize.fsti \
  src/impl/TLS13.IO.fsti \
  src/impl/TLS13.Handshake.fsti \
  src/impl/TLS13.Handshake.Driver.fst \
  src/impl/TLS13.Connection.fsti \
  src/impl/TLS13.Connection.Driver.fst

ALL_FILES = $(SPEC_FILES) $(IMPL_FILES)

EXTRACT_SMOKE_DIR  = $(EXTRACT_DIR)/smoke
EXTRACT_SMOKE_KRML = $(EXTRACT_SMOKE_DIR)/out.krml
EXTRACT_SMOKE_C    = $(EXTRACT_SMOKE_DIR)/TLS13_Extract_Smoke.c
EXTRACT_SMOKE_H    = $(EXTRACT_SMOKE_DIR)/TLS13_Extract_Smoke.h
EXTRACT_CONNECTION_DRIVER_DIR  = $(EXTRACT_DIR)/connection-driver
EXTRACT_CONNECTION_DRIVER_KRML = $(EXTRACT_CONNECTION_DRIVER_DIR)/out.krml

.PHONY: all verify test extract-smoke extract-connection-driver-krml test-extract-smoke check-c-stubs test-hacl-stubs test-openssl-stubs test-wire-stubs test-record-stubs test-io-stubs test-openssl-echo check-toolchain check-deps clean

all: verify

test: verify check-c-stubs test-hacl-stubs test-openssl-stubs test-wire-stubs test-record-stubs test-io-stubs test-extract-smoke

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

test/test_clienthello_openssl_probe: $(HACL_WRAPPER_SOURCES) c_stubs/tls13_hacl_stubs.h c_stubs/tls13_wire_stubs.c c_stubs/tls13_wire_stubs.h c_stubs/tls13_io_stubs.c c_stubs/tls13_io_stubs.h c_stubs/tls13_openssl_stubs.c c_stubs/tls13_openssl_stubs.h test/test_clienthello_openssl_probe.c | check-deps
	$(CC) -Wall -Wextra -Wno-deprecated-declarations \
	  -ffunction-sections -fdata-sections \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal -I $(HACL_KI) -I $(HACL_KL) \
	  $(HACL_WRAPPER_SOURCES) c_stubs/tls13_wire_stubs.c c_stubs/tls13_io_stubs.c c_stubs/tls13_openssl_stubs.c test/test_clienthello_openssl_probe.c \
	  -Wl,--gc-sections -lssl -lcrypto -o $@

test-openssl-stubs: test/test_openssl_stubs test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der
	./test/test_openssl_stubs test/certs/ca.pem test/certs/chain.pem test/certs/leaf.key test/certs/leaf.der

test-openssl-echo: test/openssl_echo_server
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
	  $(INCLUDES) --codegen krml --extract 'TLS13.Connection.Driver' --krmloutput $@ $<

extract-connection-driver-krml: $(EXTRACT_CONNECTION_DRIVER_KRML)

test/test_extract_smoke: test/test_extract_smoke.c $(EXTRACT_SMOKE_C) $(EXTRACT_SMOKE_H)
	$(CC) -Wall -Wextra \
	  -I $(EXTRACT_SMOKE_DIR) -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(EXTRACT_SMOKE_C) test/test_extract_smoke.c \
	  -o $@

test-extract-smoke: test/test_extract_smoke
	./test/test_extract_smoke

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	rm -f test/test_hacl_stubs test/test_openssl_stubs test/test_wire_stubs test/test_record_stubs test/test_io_stubs test/test_extract_smoke test/test_clienthello_openssl_probe test/openssl_echo_server
	find src test -name '*.checked' -delete
