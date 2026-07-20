# ═══════════════════════════════════════════════════════════════════
# Verified TLS 1.3 Client: Makefile
# ═══════════════════════════════════════════════════════════════════
# Uses F* --dep full for proper incremental builds

.DEFAULT_GOAL := all

# ── Toolchain Configuration ────────────────────────────────────────
# The F*, KaRaMeL and QuackyDucky toolchain is provided by the EverParse build
# (see ./setup.sh, which clones+builds the fork via `make quackyducky`).  Point
# EVERPARSE_HOME at that checkout; everything else is derived from it.  Override
# FSTAR_EXE/KRML_EXE/QD_EXE directly to use a different toolchain.
EVERPARSE_HOME ?= $(CURDIR)/tools/everparse
FSTAR_HOME ?= $(EVERPARSE_HOME)/opt/FStar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(EVERPARSE_HOME)/opt/karamel
# Use the installed KaRaMeL binary (opt/FStar/karamel/out/bin/krml): unlike the
# in-tree `krml` symlink to _build/default/src/Karamel.exe, it self-locates its
# krmllib/share, so no extra symlinks are needed.
KRML_EXE   ?= $(KRML_HOME)/out/bin/krml

# QuackyDucky: compiler for the TLS wire format spec, plus the LowParse +
# LowParse.Pulse combinator libraries the generated modules depend on.
QD_EXE         ?= $(EVERPARSE_HOME)/bin/qd.exe
LOWPARSE_HOME  ?= $(EVERPARSE_HOME)/src/lowparse

# F* locates Z3 by looking for `z3-<version>` on PATH.  The EverParse toolchain
# ships the pinned Z3 binaries under opt/z3 (e.g. z3-4.13.3); make them visible
# to every F* invocation (this Makefile and the generated/ sub-make) instead of
# relying on the caller having sourced tools/everparse/env.sh.
Z3_DIR         ?= $(EVERPARSE_HOME)/opt/z3
export PATH := $(Z3_DIR):$(PATH)

GENERATED_DIR   = generated
QD_RFC          = tls.qd.rfc
FSTAR_PREFIX    = $(patsubst %/bin/fstar.exe,%,$(realpath $(FSTAR_EXE)))
FSTAR_SOURCE_ROOT ?= $(FSTAR_HOME)
FSTAR_ULIB      = $(FSTAR_SOURCE_ROOT)/ulib
FSTAR_PULSE_COMMON = $(FSTAR_SOURCE_ROOT)/pulse/lib/common
FSTAR_PULSE_LIB = $(FSTAR_SOURCE_ROOT)/pulse/lib/pulse/lib

# ── Directories ────────────────────────────────────────────────────
CACHE_DIR   = _cache
OUTPUT_DIR  = _output
EXTRACT_DIR = _extract
HACL_DIR    = third_party/hacl-star/dist/gcc-compatible
HACL_KI     = third_party/hacl-star/dist/karamel/include
HACL_KL     = third_party/hacl-star/dist/karamel/krmllib/dist/minimal
SPEC_DIRS   = $(sort $(shell find src/spec -type d -print))
SOURCE_DIRS = common $(SPEC_DIRS) src/impl $(GENERATED_DIR) \
  $(LOWPARSE_HOME) $(LOWPARSE_HOME)/pulse

# ── F* Flags ───────────────────────────────────────────────────────
INCLUDES = \
  --include common \
  $(addprefix --include ,$(SPEC_DIRS)) \
  --include src/impl \
  --include $(GENERATED_DIR) \
  --include $(LOWPARSE_HOME) \
  --include $(LOWPARSE_HOME)/pulse

FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,+Pulse.Lib.Array,+Pulse.Lib.Array.*'

EXTRACT_DEBUG ?= 0
ifeq ($(EXTRACT_DEBUG),1)
FSTAR_EXTRACT_DEBUG_FLAGS = --trace_error --profile '*' --profile_component FStarC.Extraction
KRML_DEBUG_FLAGS = -verbose -dbacktrace
else
FSTAR_EXTRACT_DEBUG_FLAGS =
KRML_DEBUG_FLAGS =
endif

FSTAR_FLAGS = \
  $(OTHERFLAGS) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
  --ext optimize_let_vc \
  --ext fly_deps \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

FSTAR_EXTRACT_FLAGS = \
  $(OTHERFLAGS) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
  $(INCLUDES)

FSTAR_EXTRACT = $(FSTAR_EXE) $(FSTAR_EXTRACT_FLAGS)

# ── Source Files ───────────────────────────────────────────────────
COMMON_FILES = $(wildcard common/*.fst common/*.fsti)
SPEC_FILES = $(sort $(shell find src/spec -type f \( -name '*.fst' -o -name '*.fsti' \) -print))
IMPL_FILES = $(wildcard src/impl/*.fst src/impl/*.fsti)
ALL_FILES  = $(COMMON_FILES) $(SPEC_FILES) $(IMPL_FILES)
ROOT_FILES = \
  src/impl/TLS13.System.Temporal.fst \
  src/impl/TLS13.Impl.Client.Driver.fst \
  src/impl/TLS13.Impl.Server.Driver.fst

# ── TLS wire parsers/serializers: QuackyDucky → F* → KaRaMeL pipeline ──────
# The TLS13.Wire.Generated.* modules are produced by QuackyDucky from $(QD_RFC),
# verified by F*, and (optionally) extracted to C by KaRaMeL.  Only the generated
# .fst/.fsti sources are committed; their .checked files are gitignored and
# produced locally, consumed by the main client build as already-cached; the
# rules below regenerate/verify/extract them via the EverParse harness
# (generated/generated.Makefile), driven by the same toolchain.
#
#   make regen-generated    QuackyDucky:  $(QD_RFC) -> generated/TLS13.Wire.Generated.*
#   make verify-generated    F* verify:    refresh generated/*.checked
#   make extract-generated   KaRaMeL:      generated/out/*.c (parsers + serializers)
#   make parsers             run all three in order

# Toolchain passed through to the generated/ EverParse harness sub-make.
GENERATED_MAKE_VARS = \
  EVERPARSE_HOME='$(realpath $(EVERPARSE_HOME))' \
  FSTAR_EXE='$(FSTAR_EXE)' \
  KRML_EXE='$(KRML_EXE)' \
  KRML_HOME='$(KRML_HOME)'

# Committed generated sources and a stamp marking that their (gitignored)
# .checked files have been produced.  The main build's `.depend` consumes the
# generated modules as already-cached (--already_cached +TLS13.Wire.Generated),
# so the .checked MUST exist before `.depend` is computed — see its order-only
# prerequisite below.  The stamp rebuilds whenever a generated source changes.
GENERATED_SRCS  = $(wildcard $(GENERATED_DIR)/TLS13.Wire.Generated.*.fst $(GENERATED_DIR)/TLS13.Wire.Generated.*.fsti)
GENERATED_STAMP = $(GENERATED_DIR)/.checked.stamp

.PHONY: regen-generated
regen-generated: | check-toolchain
	rm -f $(GENERATED_DIR)/TLS13.Wire.Generated.*.fst $(GENERATED_DIR)/TLS13.Wire.Generated.*.fsti
	$(QD_EXE) -pulse -prefix "TLS13.Wire.Generated." -odir $(GENERATED_DIR) $(QD_RFC)
	@echo "Regenerated TLS13.Wire.Generated.* — now run 'make verify-generated' to refresh .checked files."

# Verify the generated modules in isolation using the EverParse harness flags,
# producing their (gitignored) .checked files.  Driven through a stamp so the
# main build's `.depend` can depend on it (order-only) without re-running it on
# every invocation; the stamp rebuilds when a generated source changes.
#
# The verification artifacts under $(GENERATED_DIR)/cache (and the harness
# .depend) are deliberately left in place: extract-generated reuses them so the
# generated Wire modules are verified exactly once per `parsers` run instead of
# being re-verified during extraction.  The main build never reads
# $(GENERATED_DIR)/cache (its cache_dir is $(CACHE_DIR), and the Wire modules are
# consumed as already-cached from the $(GENERATED_DIR)/*.checked copies below), so
# these leftovers are inert for the rest of the build.
$(GENERATED_STAMP): $(GENERATED_SRCS) | check-toolchain
	$(MAKE) -C $(GENERATED_DIR) -f generated.Makefile depend verify $(GENERATED_MAKE_VARS)
	-cp $(GENERATED_DIR)/cache/TLS13.Wire.Generated.*.checked $(GENERATED_DIR)/ 2>/dev/null || true
	touch $@

# Force a re-verification of the generated modules (e.g. after regen-generated).
.PHONY: verify-generated
verify-generated: | check-toolchain
	rm -f $(GENERATED_STAMP)
	$(MAKE) $(GENERATED_STAMP)

# Extract the generated parsers and serializers to C (standalone library) via
# KaRaMeL.  Output lands in generated/out/*.c,*.h.  Consumers must call
# krmlinit_globals() at startup to initialise the enum lookup tables (the
# parsers/serializers library is what the verified drivers link against; the
# C driver wrappers wire krmlinit_globals.
#
# Depends on $(GENERATED_STAMP): verification happens there (once).  The `verify`
# goal below is then satisfied by the preserved $(GENERATED_DIR)/cache, so this
# stage only runs KaRaMeL extraction rather than re-verifying.
.PHONY: extract-generated
extract-generated: $(GENERATED_STAMP) | check-toolchain
	$(MAKE) -C $(GENERATED_DIR) -f generated.Makefile depend verify extract $(GENERATED_MAKE_VARS)
	@echo "Extracted TLS wire parsers/serializers to $(GENERATED_DIR)/out/"

# Full parsers/serializers pipeline from $(QD_RFC): generate, verify, extract.
# These stages share the generated/ directory (.depend, cache/, the .fst sources)
# and are inherently ordered, so they MUST run sequentially even under a parallel
# `make -jN`; run them via recursive $(MAKE) rather than as parallel prerequisites.
# extract-generated pulls in $(GENERATED_STAMP) (the single verification step), so
# verify-generated is not invoked separately here.
.PHONY: parsers
parsers:
	$(MAKE) regen-generated
	$(MAKE) extract-generated

# ── Portable generated-verification cache (for CI) ─────────────────
# The generated TLS13.Wire.Generated.* .checked files are a pure function of two
# inputs: the QuackyDucky-generated sources (themselves derived from $(QD_RFC))
# and the F*/LowParse/QuackyDucky toolchain (pinned by scripts/build-everparse.sh).
# So a CI cache keyed on the hash of just those two files can carry the whole
# generated-module verification result across runs.  These targets export/import
# that result as a single relocatable tarball — exactly the artifacts the
# $(GENERATED_STAMP) recipe produces (the sub-make cache/, the .checked copies the
# main build consumes as already-cached, the harness .depend, and the stamp).
GENERATED_CACHE_TARBALL ?= generated-checked.tar.gz

# Bundle the verification artifacts into $(GENERATED_CACHE_TARBALL).  Only files
# that exist are added, so a partial tree never aborts the tar.
.PHONY: save-generated-cache
save-generated-cache:
	@test -f $(GENERATED_STAMP) || { \
	  echo "No verified generated modules to save; run 'make generated-checked' first." >&2; \
	  exit 1; }
	@files='$(GENERATED_STAMP)'; \
	 for f in $(GENERATED_DIR)/.depend $(GENERATED_DIR)/cache \
	          $(GENERATED_DIR)/TLS13.Wire.Generated.*.checked; do \
	   [ -e "$$f" ] && files="$$files $$f"; \
	 done; \
	 tar czf $(GENERATED_CACHE_TARBALL) $$files; \
	 echo "Saved generated verification cache -> $(GENERATED_CACHE_TARBALL)"

# Unpack a previously saved tarball, then mark the restored .checked files and
# stamp newer than the (freshly checked-out) generated sources so Make treats
# $(GENERATED_STAMP) as up-to-date and skips re-running the verification.  A
# missing tarball is not an error — the build simply verifies from scratch.  F*
# still validates every .checked against its source hash when the main build
# consumes it, so a stale cache is safely re-verified rather than trusted.
.PHONY: restore-generated-cache
restore-generated-cache:
	@if [ ! -f $(GENERATED_CACHE_TARBALL) ]; then \
	  echo "No cache tarball at $(GENERATED_CACHE_TARBALL); nothing to restore (will verify from scratch)."; \
	  exit 0; \
	fi; \
	if tar xzf $(GENERATED_CACHE_TARBALL); then \
	  find $(GENERATED_DIR) \( -name '*.checked' -o -name '.checked.stamp' \) -exec touch {} + ; \
	  echo "Restored generated verification cache from $(GENERATED_CACHE_TARBALL) (stamp marked fresh)."; \
	else \
	  echo "WARNING: could not extract $(GENERATED_CACHE_TARBALL); verifying from scratch." >&2; \
	  rm -f $(GENERATED_STAMP); \
	fi

# ── Dependency Analysis ────────────────────────────────────────────
# The generated .checked files must exist before `.depend` is computed, because
# the dependency scan runs F* with --already_cached +TLS13.Wire.Generated.  The
# order-only $(GENERATED_STAMP) prerequisite produces them first (without forcing
# a needless `.depend` rebuild once present).
.depend: $(ALL_FILES) Makefile | check-toolchain $(GENERATED_STAMP)
	$(FSTAR) $(FSTAR_DEP_OPTIONS) --dep full $(ROOT_FILES) --output_deps_to $@

# Do NOT pull in .depend (and, through it, the order-only $(GENERATED_STAMP)
# prerequisite) for the generated-pipeline phony goals or clean.  `parsers` runs
# regen/verify/extract-generated as recursive $(MAKE) sub-builds; each such
# sub-invocation re-reads this Makefile and would re-evaluate $(GENERATED_STAMP),
# which is perpetually out of date during `parsers` (regen-generated rewrites the
# generated sources), so the generated Wire modules would be re-verified once per
# sub-make — racing under -jN.  These goals manage the generated .checked files
# explicitly via the stamp and never need the spec/impl dependency graph.
DEPEND_EXCLUDED_GOALS := clean regen-generated verify-generated extract-generated \
  parsers generated-checked save-generated-cache restore-generated-cache \
  $(GENERATED_STAMP)
ifeq (,$(filter $(DEPEND_EXCLUDED_GOALS),$(MAKECMDGOALS)))
include .depend
endif

# ── Generic Verification Rules ────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	$(FSTAR) $<

$(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR):
	mkdir -p $@

# ── Main Targets ───────────────────────────────────────────────────
.PHONY: all verify test clean check-toolchain check-deps admit-count check-admits generated-checked parsers extract-generated save-generated-cache restore-generated-cache benchmark benchmark-build benchmark-profile-build profile

all: verify

# Ensure the generated TLS13.Wire.Generated.* modules have up-to-date .checked
# files (consumed as already-cached by the main build) before verifying.  The
# .checked files are not committed; they are produced from the committed sources
# via $(GENERATED_STAMP).
generated-checked: $(GENERATED_STAMP)

verify: generated-checked $(ALL_CHECKED_FILES)
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

# ── Extraction Bundles ─────────────────────────────────────────────
# List of modules to extract (dotted names)
EXTRACT_MODULES = \
  $(BUNDLE_IMPL_MODULES)

# Convert module names to .krml filenames
KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(EXTRACT_MODULES)))

.PHONY: extract-krml extract-connection \
  extract-tls13-driver-krml extract-tls13-bundle

extract-krml: $(KRML_FILES)

# ──────────────────────────────────────────────────────────────────────────────
# KaRaMeL Extraction - .krml to C
# ──────────────────────────────────────────────────────────────────────────────

EXTRACT_DIR = _extract

# ── Bundle extraction (single-file) using proper KaRaMeL bundling ──────

BUNDLE_DIR = $(EXTRACT_DIR)/bundle

# TLS13.Impl.Client is the public API module.
BUNDLE_API_MODULE = TLS13.Impl.Client

SERIALIZER_MODULES = \
  TLS13.Impl.Serializer.Common \
  TLS13.Impl.Serializer.Handshake \
  TLS13.Impl.Serializer.Finished \
  TLS13.Impl.Serializer.EncryptedExtensions \
  TLS13.Impl.Serializer.ServerHello \
  TLS13.Impl.Serializer.Certificate \
  TLS13.Impl.Serializer.ProtectedRecord \
  TLS13.Impl.Serializer

SERIALIZER_INTERNAL_MODULES = \
  TLS13.Impl.Serializer.Common,TLS13.Impl.Serializer.Handshake,\
  TLS13.Impl.Serializer.Finished,\
  TLS13.Impl.Serializer.EncryptedExtensions,\
  TLS13.Impl.Serializer.ServerHello,\
  TLS13.Impl.Serializer.Certificate,TLS13.Impl.Serializer.ProtectedRecord,\
  TLS13.Impl.Serializer

PARSER_MODULES = \
  TLS13.Impl.Parser.PureExists \
  TLS13.Impl.Parser.DecoderWF \
  TLS13.Impl.Parser.CertChain \
  TLS13.Impl.Parser

PARSER_INTERNAL_MODULES = \
  TLS13.Impl.Parser.PureExists,TLS13.Impl.Parser.DecoderWF,\
  TLS13.Impl.Parser.CertChain,TLS13.Impl.Parser

PULSE_RUNTIME_MODULES = \
  Pulse.Lib.ArrayPtr \
  Pulse.Lib.Array.Core \
  Pulse.Lib.Array \
  Pulse.Lib.Slice \
  Pulse.Lib.Vec

# Implementation modules to bundle as internal to the client.
BUNDLE_IMPL_MODULES = \
  TLS13.Impl.Client \
  TLS13.Impl.Endpoint.Types \
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
  $(SERIALIZER_MODULES) \
  $(PARSER_MODULES) \
  TLS13.Impl.Messages \
  TLS13.KeySchedule \
  TLS13.Record

# Non-API modules (everything except TLS13.Impl.Client)
BUNDLE_INTERNAL_MODULES = \
  TLS13.Impl.Endpoint.Types,TLS13.Impl.Client.Types,\
  TLS13.Impl.ConnectionState.Bounds,\
  TLS13.Impl.ConnectionState.Model,TLS13.Impl.ConnectionState.Tags,\
  TLS13.Impl.ConnectionState.Repr,TLS13.Impl.ConnectionState.Queries,\
  TLS13.Impl.ConnectionState.Fail,TLS13.Impl.ConnectionState.LocalHandshake,\
  TLS13.Impl.ConnectionState.LocalAuth,TLS13.Impl.ConnectionState.LocalSend,\
  TLS13.Impl.ConnectionState.LocalApp,TLS13.Impl.ConnectionState.Network,\
  TLS13.Impl.Handle.Alert,TLS13.Impl.Handle.ApplicationData,\
  TLS13.Impl.Handle.ChangeCipherSpec,TLS13.Impl.Handle.DecodeError,\
  TLS13.Impl.Handle.Dispatch,TLS13.Impl.Handle.Handshake,\
  TLS13.Impl.Handle.Local,$(SERIALIZER_INTERNAL_MODULES),$(PARSER_INTERNAL_MODULES),\
  TLS13.Impl.Messages,\
  TLS13.KeySchedule,TLS13.Record

# Interface-only external modules (not implemented in F*):
# TLS13.Crypto, TLS13.OpenSSL, Common.TCP

FULL_KRML_FILES = $(filter-out $(OUTPUT_DIR)/prims.krml $(OUTPUT_DIR)/Prims.krml,$(ALL_KRML_FILES))

# Extract the full dependency closure so calls through .fsti interfaces (notably
# TLS13.Impl.Parser) resolve to their verified implementations.
BUNDLE_KRML_FILES = $(filter-out \
  $(OUTPUT_DIR)/TLS13_Impl_Client_Driver.krml \
  $(OUTPUT_DIR)/TLS13_OpenSSL.krml \
  $(OUTPUT_DIR)/Common_TCP.krml,$(FULL_KRML_FILES))

TLS13_BUNDLE_DIR = $(EXTRACT_DIR)/tls13_bundle
TLS13_BUNDLE_STAMP = $(TLS13_BUNDLE_DIR)/.generated
TLS13_BUNDLE_OBJ_DIR = $(TLS13_BUNDLE_DIR)/obj
TLS13_BUNDLE_OBJS_STAMP = $(TLS13_BUNDLE_OBJ_DIR)/.built
TLS13_BUNDLE_INCLUDES = -I$(TLS13_BUNDLE_DIR) -I$(TLS13_BUNDLE_DIR)/internal
TLS13_DRIVER_KRML_STAMP = $(OUTPUT_DIR)/.tls13_driver_krml.stamp
CLIENT_DRIVER_IMPL_MODULES = \
  TLS13.Impl.Endpoint.Types \
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
  TLS13.Record \
  TLS13.Impl.Client \
  TLS13.Impl.Client.Driver.State \
  TLS13.Impl.Client.Driver.New \
  TLS13.Impl.Client.Driver.Core \
  TLS13.Impl.Client.Driver.Cleanup \
  TLS13.Impl.Client.Driver.Connect \
  TLS13.Impl.Client.Driver.Send \
  TLS13.Impl.Client.Driver.Receive \
  TLS13.Impl.Client.Driver.Close
CLIENT_DRIVER_KRML_FILES = \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(PULSE_RUNTIME_MODULES))) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(CLIENT_DRIVER_IMPL_MODULES))) \
  $(OUTPUT_DIR)/TLS13_Client_Driver_Bundle.krml \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(PARSER_MODULES))) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(SERIALIZER_MODULES)))
DRIVER_EXTRACT_SELECTOR = \
  *,-FStar.Tactics,-FStar.Reflection,-Pulse,+Pulse.Lib.Pervasives,\
  +Pulse.Lib.Slice,+Pulse.Lib.Array,+Pulse.Lib.Array.*,\
  -Common.StateMachine,-Common.WireFormat,-Common.WireFormatStateMachine,\
  -Common.ProtocolImplementation,-Common.ProtocolEndpoint,\
  -TLS13.Impl.ConnectionStateQuery,-TLS13.Impl.CanonicalTypes,\
  -TLS13.Spec.Endpoint.Wire,-TLS13.Impl.Client.CanonicalProtocol,\
  -TLS13.Impl.Client.CanonicalQueries,-TLS13.Impl.Client.Endpoint,\
  -TLS13.Impl.Driver.Pairing,-TLS13.Impl.Serializer,-TLS13.Impl.Serializer.*,\
  -TLS13.Impl.Parser,-TLS13.Impl.Parser.*
SERVER_DRIVER_EXTRACT_SELECTOR = \
  *,-FStar.Tactics,-FStar.Reflection,-Pulse,+Pulse.Lib.Pervasives,\
  +Pulse.Lib.Slice,+Pulse.Lib.Array,+Pulse.Lib.Array.*,\
  -Common.StateMachine,-Common.WireFormat,-Common.WireFormatStateMachine,\
  -Common.ProtocolImplementation,-Common.ProtocolEndpoint,\
  -TLS13.Impl.ConnectionStateQuery,-TLS13.Impl.CanonicalTypes,\
  -TLS13.Spec.Endpoint.Wire,-TLS13.Impl.Server.CanonicalProtocol,\
  -TLS13.Impl.Server.CanonicalQueries,-TLS13.Impl.Server.Endpoint,\
  -TLS13.Impl.Serializer,-TLS13.Impl.Serializer.*,\
  -TLS13.Impl.Parser,-TLS13.Impl.Parser.*

SERVER_DRIVER_MODULES = \
  TLS13.Impl.Endpoint.Types \
  TLS13.Impl.ConnectionState.Bounds \
  TLS13.Impl.ConnectionState.Model \
  TLS13.Impl.ConnectionState.Tags \
  TLS13.Impl.ConnectionState.Repr \
  TLS13.Impl.ConnectionState.Queries \
  TLS13.Impl.ConnectionState.Fail \
  TLS13.Impl.ConnectionState.Network \
  TLS13.Impl.ConnectionState.LocalHandshake \
  TLS13.Impl.ConnectionState.LocalAuth \
  TLS13.Impl.ConnectionState.LocalSend \
  TLS13.Impl.ConnectionState.LocalApp \
  TLS13.Impl.Messages \
  TLS13.KeySchedule \
  TLS13.Record \
  TLS13.Impl.Server.Types \
  TLS13.Impl.Server.Setup \
  TLS13.Impl.Server.Schedule \
  TLS13.Impl.Server.Keys \
  TLS13.Impl.Server.Network \
  TLS13.Impl.Server.Material \
  TLS13.Impl.Server.Send \
  TLS13.Impl.Server.Auth \
  TLS13.Impl.Server.App \
  TLS13.Impl.Server \
  Common.TCP \
  TLS13.OpenSSL \
  TLS13.Impl.Server.Driver.State \
  TLS13.Impl.Server.Driver.Transport \
  TLS13.Impl.Server.Driver.Network \
  TLS13.Impl.Server.Driver.Local \
  TLS13.Impl.Server.Driver.Handshake \
  TLS13.Impl.Server.Driver
SERVER_DRIVER_KRML_FILES = \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(PULSE_RUNTIME_MODULES))) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(SERVER_DRIVER_MODULES))) \
  $(OUTPUT_DIR)/TLS13_Server_Driver_Bundle.krml \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(PARSER_MODULES))) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(SERIALIZER_MODULES)))
GENERATED_RUNTIME_MODULES = TLS13.Wire.Generated.ChangeCipherSpec
TLS13_BUNDLE_KRML_FILES = \
  $(CLIENT_DRIVER_KRML_FILES) \
  $(filter-out $(CLIENT_DRIVER_KRML_FILES),$(SERVER_DRIVER_KRML_FILES)) \
  $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(GENERATED_RUNTIME_MODULES))) \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

# Extract FStar.Pervasives.Native for tuple support
$(OUTPUT_DIR)/FStar_Pervasives_Native.krml: verify | $(OUTPUT_DIR)
	@start=$$(date +%s); \
	printf '[extract] F* start target=%s module=%s src=%s at %s\n' \
	  "$@" "FStar.Pervasives.Native" "FStar.Pervasives.Native.fst" "$$(date -Is)"; \
	$(FSTAR_EXE) $(FSTAR_EXTRACT_DEBUG_FLAGS) \
	  --codegen krml --extract_module FStar.Pervasives.Native \
	  --odir $(OUTPUT_DIR) --cache_dir $(CACHE_DIR) \
	  --already_cached Prims,FStar \
	  FStar.Pervasives.Native.fst; \
	status=$$?; end=$$(date +%s); \
	printf '[extract] F* end target=%s module=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "FStar.Pervasives.Native" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status

$(filter-out $(OUTPUT_DIR)/FStar_SizeT.krml,$(ALL_KRML_FILES)): | $(OUTPUT_DIR)/FStar_SizeT.krml

$(OUTPUT_DIR)/FStar_SizeT.krml: $(FSTAR_ULIB)/FStar.SizeT.fst | $(OUTPUT_DIR)
	@# Extract the *stock* standard-library FStar.SizeT to .krml, reusing the F*
	@# install's already-cached FStar.SizeT.checked (--already_cached 'Prims,FStar'
	@# keeps FStar.SizeT cached, so F* loads it rather than re-checking and never
	@# rewrites the install's ulib.checked/FStar.SizeT.*.checked).  No stub, no
	@# clobber/restore: the extracted client code calls no FStar.SizeT function
	@# (v/uint_to_t stay noextract_to "krml"; all SizeT arithmetic/casts are KaRaMeL
	@# builtins), so the stock module — where v/uint_to_t emit no C — works as-is.
	@start=$$(date +%s); \
	printf '[extract] F* start target=%s module=%s src=%s at %s\n' \
	  "$@" "FStar.SizeT" "$(FSTAR_ULIB)/FStar.SizeT.fst" "$$(date -Is)"; \
	$(FSTAR_EXE) $(FSTAR_EXTRACT_DEBUG_FLAGS) \
	  --odir $(OUTPUT_DIR) --already_cached 'Prims,FStar' \
	  --codegen krml --extract_module FStar.SizeT \
	  $(FSTAR_ULIB)/FStar.SizeT.fst --krmloutput $@; \
	status=$$?; end=$$(date +%s); \
	printf '[extract] F* end target=%s module=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "FStar.SizeT" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status

$(OUTPUT_DIR)/TLS13_Client_Driver_Bundle.krml: verify src/impl/TLS13.Impl.Client.Driver.fst Makefile | $(OUTPUT_DIR)
	@start=$$(date +%s); \
	printf '[extract] F* start target=%s module=%s src=%s at %s\n' \
	  "$@" "TLS13.Impl.Client.Driver bundle" "src/impl/TLS13.Impl.Client.Driver.fst" "$$(date -Is)"; \
	$(FSTAR_EXTRACT) $(FSTAR_EXTRACT_DEBUG_FLAGS) \
	  --codegen krml --extract '$(DRIVER_EXTRACT_SELECTOR)' \
	  src/impl/TLS13.Impl.Client.Driver.fst --krmloutput $@; \
	status=$$?; end=$$(date +%s); \
	printf '[extract] F* end target=%s module=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "TLS13.Impl.Client.Driver bundle" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status

$(OUTPUT_DIR)/TLS13_Server_Driver_Bundle.krml: verify src/impl/TLS13.Impl.Server.Driver.fst Makefile | $(OUTPUT_DIR)
	@start=$$(date +%s); \
	printf '[extract] F* start target=%s module=%s src=%s at %s\n' \
	  "$@" "TLS13.Impl.Server.Driver bundle" "src/impl/TLS13.Impl.Server.Driver.fst" "$$(date -Is)"; \
	$(FSTAR_EXTRACT) $(FSTAR_EXTRACT_DEBUG_FLAGS) \
	  --codegen krml --extract '$(SERVER_DRIVER_EXTRACT_SELECTOR)' \
	  src/impl/TLS13.Impl.Server.Driver.fst --krmloutput $@; \
	status=$$?; end=$$(date +%s); \
	printf '[extract] F* end target=%s module=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "TLS13.Impl.Server.Driver bundle" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status

$(OUTPUT_DIR)/%.krml: verify | $(OUTPUT_DIR)
	@target_base=$$(basename "$@" .krml); \
	module=; src=; \
	for ext in fst fsti; do \
	  for dir in $(SOURCE_DIRS) \
	      $(FSTAR_ULIB) $(FSTAR_PULSE_COMMON) $(FSTAR_PULSE_LIB); do \
	    test -d "$$dir" || continue; \
	    for candidate in "$$dir"/*.$$ext; do \
	      test -f "$$candidate" || continue; \
	      candidate_module=$$(basename "$$candidate" .$$ext); \
	      candidate_base=$$(printf '%s' "$$candidate_module" | tr . _); \
	      if test "$$candidate_base" = "$$target_base"; then \
	        module=$$candidate_module; src=$$candidate; break 3; \
	      fi; \
	    done; \
	  done; \
	done; \
	if test -z "$$module" || test -z "$$src"; then \
	  echo "Could not locate F* source for $@"; \
	  exit 1; \
	fi; \
	start=$$(date +%s); \
	printf '[extract] F* start target=%s module=%s src=%s at %s\n' \
	  "$@" "$$module" "$$src" "$$(date -Is)"; \
	$(FSTAR) $(FSTAR_EXTRACT_DEBUG_FLAGS) \
	  --codegen krml --extract_module "$$module" "$$src" --krmloutput "$@"; \
	status=$$?; end=$$(date +%s); \
	printf '[extract] F* end target=%s module=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "$$module" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status

extract-krml-bundle: $(BUNDLE_KRML_FILES)

extract-tls13-driver-krml: $(TLS13_DRIVER_KRML_STAMP)

$(TLS13_DRIVER_KRML_STAMP): $(ALL_FILES) $(GENERATED_SRCS) $(GENERATED_STAMP) Makefile | verify $(OUTPUT_DIR)
	$(MAKE) $(TLS13_BUNDLE_KRML_FILES)
	@touch $@

$(BUNDLE_DIR):
	mkdir -p $@

$(TLS13_BUNDLE_DIR):
	mkdir -p $@ $@/internal

extract-tls13-bundle: $(TLS13_BUNDLE_STAMP)

$(TLS13_BUNDLE_STAMP): $(TLS13_DRIVER_KRML_STAMP) Makefile | $(TLS13_BUNDLE_DIR)
	@echo "Extracting TLS13 client/server driver bundle..."
	@rm -f $(TLS13_BUNDLE_DIR)/*.c $(TLS13_BUNDLE_DIR)/*.h $(TLS13_BUNDLE_DIR)/internal/*.h
	@rm -rf $(TLS13_BUNDLE_OBJ_DIR)
	@mkdir -p $(TLS13_BUNDLE_DIR)/internal
	@start=$$(date +%s); \
	printf '[extract] KaRaMeL start target=%s at %s\n' "$@" "$$(date -Is)"; \
	$(KRML_EXE) $(KRML_DEBUG_FLAGS) \
	  -tmpdir $(TLS13_BUNDLE_DIR) \
	  -skip-compilation \
	  -static-header TLS13.Impl.Serializer \
	  -add-include '<stdbool.h>' \
	  -add-include '"krml/internal/compat.h"' \
	  -add-include '"../../c_stubs/common_tcp_karamel.h"' \
	  -add-include '"../../c_stubs/tls13_bytes_karamel.h"' \
	  -add-include '"../../c_stubs/tls13_openssl_karamel.h"' \
	  -drop 'FStar.Tactics.*' -drop FStar.Tactics -drop 'FStar.Reflection.*' \
	  -library TLS13.Crypto -library Common.TCP \
	  -library TLS13.OpenSSL \
	  -bundle 'TLS13.Bytes,TLS13.Types,TLS13.Keys,TLS13.Crypto.Spec,TLS13.X509.Spec,TLS13.Record.Spec,TLS13.Handshake.Spec,TLS13.Wire.Spec,TLS13.Wire.Spec.*' \
	  -bundle 'TLS13.ConnectionLog,TLS13.Spec.StateMachine,TLS13.Spec.StateMachine.*,TLS13.Spec.Endpoint.*,TLS13.Transcript' \
	  -bundle 'TLS13.Wire.Generated.*' \
	  -bundle 'LowParse.*' \
	  -bundle 'FStar.*,PulseCore.*,Prims' \
	  -warn-error -2-9-17-6 \
	  $(TLS13_BUNDLE_KRML_FILES); \
	status=$$?; end=$$(date +%s); \
	printf '[extract] KaRaMeL end target=%s status=%s elapsed=%ss at %s\n' \
	  "$@" "$$status" "$$((end-start))" "$$(date -Is)"; \
	exit $$status
	@touch $@

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

ECHO_STUB_SOURCES = \
  c_stubs/common_tcp_karamel.c \
  c_stubs/common_tcp_stubs.c \
  c_stubs/tls13_crypto_external.c \
  c_stubs/tls13_openssl_karamel.c \
  c_stubs/tls13_openssl_stubs.c \
  c_stubs/tls13_hacl_stubs.c

ECHO_STUB_HEADERS = \
  c_stubs/common_tcp_karamel.h \
  c_stubs/common_tcp_stubs.h \
  c_stubs/tls13_bytes_karamel.h \
  c_stubs/tls13_crypto_external.h \
  c_stubs/tls13_hacl_stubs.h \
  c_stubs/tls13_openssl_karamel.h \
  c_stubs/tls13_openssl_stubs.h

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

# Benchmark builds keep symbols and frame pointers for profiling while using
# production optimization. Override these variables to compare compiler flags.
BENCHMARK_CFLAGS ?= -O3 -DNDEBUG -g -fno-omit-frame-pointer
BENCHMARK_PROFILE_CFLAGS ?= -O2 -DNDEBUG -g -pg -fno-omit-frame-pointer
BENCHMARK_OBJ_DIR = $(TLS13_BUNDLE_DIR)/benchmark_obj
BENCHMARK_PROFILE_OBJ_DIR = $(TLS13_BUNDLE_DIR)/benchmark_profile_obj
BENCHMARK_BUILD_ID := $(shell printf '%s' '$(CC) $(CFLAGS_COMMON) $(BENCHMARK_CFLAGS) $(TLS13_BUNDLE_INCLUDES) $(LDFLAGS_COMMON)' | cksum | cut -d' ' -f1)
BENCHMARK_PROFILE_BUILD_ID := $(shell printf '%s' '$(CC) $(CFLAGS_COMMON) $(BENCHMARK_PROFILE_CFLAGS) $(TLS13_BUNDLE_INCLUDES) $(LDFLAGS_COMMON)' | cksum | cut -d' ' -f1)
BENCHMARK_OBJ_STAMP = $(BENCHMARK_OBJ_DIR)/.built-$(BENCHMARK_BUILD_ID)
BENCHMARK_PROFILE_OBJ_STAMP = $(BENCHMARK_PROFILE_OBJ_DIR)/.built-$(BENCHMARK_PROFILE_BUILD_ID)
BENCHMARK_BINARY = test/perf/tls13_bench
BENCHMARK_PROFILE_BINARY = test/perf/tls13_bench-gprof

$(BENCHMARK_OBJ_STAMP): $(TLS13_BUNDLE_STAMP) $(ECHO_STUB_HEADERS) Makefile
	@rm -rf $(BENCHMARK_OBJ_DIR)
	@mkdir -p $(BENCHMARK_OBJ_DIR)
	@set -e; for src in $(TLS13_BUNDLE_DIR)/*.c; do \
	  obj="$(BENCHMARK_OBJ_DIR)/$$(basename "$$src" .c).o"; \
	  $(CC) $(CFLAGS_COMMON) $(BENCHMARK_CFLAGS) $(TLS13_BUNDLE_INCLUDES) \
	    -c "$$src" -o "$$obj"; \
	done
	@touch $@

$(BENCHMARK_PROFILE_OBJ_STAMP): $(TLS13_BUNDLE_STAMP) $(ECHO_STUB_HEADERS) Makefile
	@rm -rf $(BENCHMARK_PROFILE_OBJ_DIR)
	@mkdir -p $(BENCHMARK_PROFILE_OBJ_DIR)
	@set -e; for src in $(TLS13_BUNDLE_DIR)/*.c; do \
	  obj="$(BENCHMARK_PROFILE_OBJ_DIR)/$$(basename "$$src" .c).o"; \
	  $(CC) $(CFLAGS_COMMON) $(BENCHMARK_PROFILE_CFLAGS) $(TLS13_BUNDLE_INCLUDES) \
	    -c "$$src" -o "$$obj"; \
	done
	@touch $@

define link_benchmark
	$(CC) $(CFLAGS_COMMON) $(1) \
	  $(TLS13_BUNDLE_INCLUDES) \
	  $(2)/*.o \
	  c_stubs/tls13_crypto_external.c \
	  runtime/tls13_client_driver.c \
	  runtime/tls13_server_driver.c \
	  c_stubs/common_tcp_karamel.c \
	  c_stubs/common_tcp_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/perf/tls13_bench.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(KRML_HOME)/krmllib/c/fstar_uint32.c \
	  $(LDFLAGS_COMMON) $(1) -lssl -lcrypto -o $(3)
endef

$(BENCHMARK_BINARY): test/perf/tls13_bench.c $(BENCHMARK_OBJ_STAMP) \
  runtime/tls13_client_driver.c runtime/tls13_client_driver.h \
  runtime/tls13_server_driver.c runtime/tls13_server_driver.h \
  $(ECHO_STUB_SOURCES) $(ECHO_STUB_HEADERS) $(HACL_WRAPPER_SOURCES) | check-deps
	$(call link_benchmark,$(BENCHMARK_CFLAGS),$(BENCHMARK_OBJ_DIR),$@)

$(BENCHMARK_PROFILE_BINARY): test/perf/tls13_bench.c \
  $(BENCHMARK_PROFILE_OBJ_STAMP) \
  runtime/tls13_client_driver.c runtime/tls13_client_driver.h \
  runtime/tls13_server_driver.c runtime/tls13_server_driver.h \
  $(ECHO_STUB_SOURCES) $(ECHO_STUB_HEADERS) $(HACL_WRAPPER_SOURCES) | check-deps
	$(call link_benchmark,$(BENCHMARK_PROFILE_CFLAGS),$(BENCHMARK_PROFILE_OBJ_DIR),$@)

benchmark-build: $(BENCHMARK_BINARY) test/certs/ca.pem test/certs/chain.pem \
  test/certs/leaf.der test/certs/leaf.key

benchmark-profile-build: $(BENCHMARK_PROFILE_BINARY) test/certs/ca.pem \
  test/certs/chain.pem test/certs/leaf.der test/certs/leaf.key

benchmark: benchmark-build
	scripts/benchmark-tls13.sh

profile: benchmark-profile-build
	scripts/profile-tls13.sh

$(TLS13_BUNDLE_OBJS_STAMP): $(TLS13_BUNDLE_STAMP) $(ECHO_STUB_HEADERS) Makefile | check-deps
	@rm -rf $(TLS13_BUNDLE_OBJ_DIR)
	@mkdir -p $(TLS13_BUNDLE_OBJ_DIR)
	@set -e; for src in $(TLS13_BUNDLE_DIR)/*.c; do \
	  obj="$(TLS13_BUNDLE_OBJ_DIR)/$$(basename "$$src" .c).o"; \
	  $(CC) $(CFLAGS_COMMON) $(TLS13_BUNDLE_INCLUDES) \
	    -c "$$src" -o "$$obj"; \
	done
	@touch $@

# ──────────────────────────────────────────────────────────────────────────────
# Testing
# ──────────────────────────────────────────────────────────────────────────────
.PHONY: test test-extracted-client-openssl-echo test-openssl-echo \
  test-openssl-sclient check-c-stubs

test: verify check-c-stubs test-openssl-echo test-openssl-sclient

# ── Echo C Stub Syntax Check ───────────────────────────────────────
check-c-stubs: | check-deps
	$(CC) -fsyntax-only -Wall -Wextra -Wno-deprecated-declarations \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal \
	  -I $(HACL_KI) -I $(HACL_KL) \
	  -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(ECHO_STUB_SOURCES)

# ── OpenSSL Echo Test ──────────────────────────────────────────────
TEST_CERT_STAMP = test/certs/.generated

$(TEST_CERT_STAMP): scripts/generate-test-certs.sh
	scripts/generate-test-certs.sh test/certs
	touch $@

test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der: $(TEST_CERT_STAMP)
	@test -f $@

test/test_extracted_client_openssl_echo: \
  test/unit/test_extracted_client_openssl_echo.c $(TLS13_BUNDLE_OBJS_STAMP) \
  runtime/tls13_client_driver.c runtime/tls13_client_driver.h \
  $(ECHO_STUB_SOURCES) $(ECHO_STUB_HEADERS) $(HACL_WRAPPER_SOURCES) | check-deps
	$(CC) $(CFLAGS_COMMON) \
	  $(TLS13_BUNDLE_INCLUDES) \
	  $(TLS13_BUNDLE_OBJ_DIR)/*.o \
	  c_stubs/tls13_crypto_external.c \
	  runtime/tls13_client_driver.c \
	  c_stubs/common_tcp_karamel.c \
	  c_stubs/common_tcp_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/unit/test_extracted_client_openssl_echo.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(KRML_HOME)/krmllib/c/fstar_uint32.c \
	  $(LDFLAGS_COMMON) -lssl -lcrypto -o $@

test-extracted-client-openssl-echo: test-openssl-echo

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

# ── Extracted Server / OpenSSL Client Test ─────────────────────────
test/test_extracted_server_openssl_client: \
  test/unit/test_extracted_server_openssl_client.c $(TLS13_BUNDLE_OBJS_STAMP) \
  runtime/tls13_server_driver.c runtime/tls13_server_driver.h \
  $(ECHO_STUB_SOURCES) $(ECHO_STUB_HEADERS) $(HACL_WRAPPER_SOURCES) | check-deps
	$(CC) $(CFLAGS_COMMON) \
	  $(TLS13_BUNDLE_INCLUDES) \
	  $(TLS13_BUNDLE_OBJ_DIR)/*.o \
	  c_stubs/tls13_crypto_external.c \
	  runtime/tls13_server_driver.c \
	  c_stubs/common_tcp_karamel.c \
	  c_stubs/common_tcp_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/unit/test_extracted_server_openssl_client.c \
	  $(HACL_WRAPPER_SOURCES) \
	  $(KRML_HOME)/krmllib/c/fstar_uint32.c \
	  $(LDFLAGS_COMMON) -lssl -lcrypto -o $@

test-openssl-sclient: test/test_extracted_server_openssl_client \
  test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der
	./test/test_extracted_server_openssl_client

# ── Dependency Checks ──────────────────────────────────────────────
check-toolchain:
	@if [ ! -x "$(FSTAR_EXE)" ] && ! command -v "$(FSTAR_EXE)" >/dev/null 2>&1; then \
	  echo "F* not found at $(FSTAR_EXE)."; \
	  echo "Build the EverParse toolchain with ./setup.sh (or set EVERPARSE_HOME / FSTAR_EXE)."; \
	  exit 1; \
	fi
	@if [ ! -x "$(KRML_EXE)" ] && ! command -v "$(KRML_EXE)" >/dev/null 2>&1; then \
	  echo "KaRaMeL not found at $(KRML_EXE).  Build EverParse with ./setup.sh (or set KRML_EXE)."; \
	  exit 1; \
	fi
	@if [ ! -x "$(QD_EXE)" ] && ! command -v "$(QD_EXE)" >/dev/null 2>&1; then \
	  echo "QuackyDucky not found at $(QD_EXE).  Build EverParse with ./setup.sh (or set QD_EXE)."; \
	  exit 1; \
	fi

check-deps:
	@scripts/check-openssl.sh >/dev/null
	@test -d third_party/hacl-star/dist/gcc-compatible || \
	  { echo "Missing HACL* C snapshot; run scripts/fetch-hacl-star.sh"; exit 1; }

# ── Cleanup ────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR) .depend \
	  test/openssl_echo_server test/test_extracted_client_openssl_echo \
	  test/test_extracted_server_openssl_client \
	  $(BENCHMARK_BINARY) $(BENCHMARK_PROFILE_BINARY) \
	  test/openssl_echo_server.port \
	  test/openssl_echo_server.log \
	  $(TEST_CERT_STAMP)
	find src test -name '*.checked' -delete

.PHONY: all verify test extract-krml extract-connection \
  extract-tls13-driver-krml extract-tls13-bundle \
  test-extracted-client-openssl-echo \
  test-client test-openssl-echo test-openssl-sclient \
  check-c-stubs check-toolchain check-deps benchmark benchmark-build \
  benchmark-profile-build profile clean
