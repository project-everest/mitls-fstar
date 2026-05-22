FSTAR_HOME ?= $(CURDIR)/tools/FStar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML_EXE   ?= $(KRML_HOME)/krml

CACHE_DIR   = _cache
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract

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
  src/spec/TLS13.StateMachine.fst

IMPL_FILES = \
  src/impl/TLS13.LowTypes.fst

ALL_FILES = $(SPEC_FILES) $(IMPL_FILES)

.PHONY: all verify check-toolchain check-deps clean

all: verify

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

verify: check-deps check-toolchain $(CACHE_DIR) $(OUTPUT_DIR)
	@set -e; for f in $(ALL_FILES); do \
	  echo "$(FSTAR) $$f"; \
	  $(FSTAR) $$f; \
	done
	@echo "All F* modules verified"

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR)
	find src test -name '*.checked' -delete
