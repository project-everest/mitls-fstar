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
KRML_HOME  ?= $(FSTAR_HOME)/karamel
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
FSTAR_ULIB      = $(FSTAR_PREFIX)/lib/fstar/ulib
FSTAR_PULSE_COMMON = $(FSTAR_PREFIX)/lib/fstar/pulse/common
FSTAR_PULSE_LIB = $(FSTAR_PREFIX)/lib/fstar/pulse/pulse/lib

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
  --include src/impl \
  --include $(GENERATED_DIR) \
  --include $(LOWPARSE_HOME) \
  --include $(LOWPARSE_HOME)/pulse

FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,+Pulse.Lib.Array,+Pulse.Lib.Array.*'

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

# ── Source Files ───────────────────────────────────────────────────
SPEC_FILES = $(wildcard src/spec/*.fst src/spec/*.fsti)
IMPL_FILES = $(wildcard src/impl/*.fst src/impl/*.fsti)
ALL_FILES  = $(SPEC_FILES) $(IMPL_FILES)

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
# parsers/serializers library is what the verified client links against; the
# client driver wires krmlinit_globals — see extract-driver-bundle).
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

# ── Dependency Analysis ────────────────────────────────────────────
# The generated .checked files must exist before `.depend` is computed, because
# the dependency scan runs F* with --already_cached +TLS13.Wire.Generated.  The
# order-only $(GENERATED_STAMP) prerequisite produces them first (without forcing
# a needless `.depend` rebuild once present).
.depend: $(ALL_FILES) Makefile | check-toolchain $(GENERATED_STAMP)
	$(FSTAR) $(FSTAR_DEP_OPTIONS) --dep full $(ALL_FILES) --output_deps_to $@

# Do NOT pull in .depend (and, through it, the order-only $(GENERATED_STAMP)
# prerequisite) for the generated-pipeline phony goals or clean.  `parsers` runs
# regen/verify/extract-generated as recursive $(MAKE) sub-builds; each such
# sub-invocation re-reads this Makefile and would re-evaluate $(GENERATED_STAMP),
# which is perpetually out of date during `parsers` (regen-generated rewrites the
# generated sources), so the generated Wire modules would be re-verified once per
# sub-make — racing under -jN.  These goals manage the generated .checked files
# explicitly via the stamp and never need the spec/impl dependency graph.
DEPEND_EXCLUDED_GOALS := clean regen-generated verify-generated extract-generated \
  parsers generated-checked $(GENERATED_STAMP)
ifeq (,$(filter $(DEPEND_EXCLUDED_GOALS),$(MAKECMDGOALS)))
include .depend
endif

# ── Generic Verification Rules ────────────────────────────────────
$(CACHE_DIR)/%.checked: | $(CACHE_DIR)
	$(FSTAR) $<

$(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR):
	mkdir -p $@

# ── Main Targets ───────────────────────────────────────────────────
.PHONY: all verify test clean check-toolchain check-deps admit-count check-admits generated-checked parsers extract-generated

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
  TLS13.Impl.Serializer \
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
  TLS13.Impl.Handle.Local,TLS13.Impl.Serializer,TLS13.Impl.Messages,\
  TLS13.KeySchedule,TLS13.Record

# Interface-only external modules (not implemented in F*):
# TLS13.Crypto, TLS13.X509, TLS13.MachineTypes, TLS13.IO

FULL_KRML_FILES = $(filter-out $(OUTPUT_DIR)/prims.krml $(OUTPUT_DIR)/Prims.krml,$(ALL_KRML_FILES))
KRML_STUB_DIR = $(OUTPUT_DIR)/krml_stubs
KRML_STUB_CACHE = $(OUTPUT_DIR)/krml_stub_cache

# Extract the full dependency closure so calls through .fsti interfaces (notably
# TLS13.Impl.Parser) resolve to their verified implementations.
BUNDLE_KRML_FILES = $(filter-out \
  $(OUTPUT_DIR)/TLS13_Impl_Client_Driver.krml \
  $(OUTPUT_DIR)/TLS13_OpenSSL.krml \
  $(OUTPUT_DIR)/TLS13_IO.krml,$(FULL_KRML_FILES))

DRIVER_BUNDLE_DIR = $(EXTRACT_DIR)/driver_bundle
DRIVER_KRML_FILES = $(filter-out \
  $(OUTPUT_DIR)/TLS13_Extract_Smoke.krml \
  $(OUTPUT_DIR)/FStar_Errors_Msg.krml \
  $(OUTPUT_DIR)/FStar_Tactics_%.krml \
  $(OUTPUT_DIR)/FStar_Reflection_%.krml \
  $(OUTPUT_DIR)/FStar_Syntax_Syntax.krml \
  $(OUTPUT_DIR)/FStar_TypeChecker_%.krml \
  $(OUTPUT_DIR)/FStar_VConfig.krml \
  $(OUTPUT_DIR)/TLS13_X509.krml \
  $(OUTPUT_DIR)/TLS13_MachineTypes.krml,$(FULL_KRML_FILES))

# Extract each dependency-discovered module to its own .krml.  Use the checked
# source prerequisite from .depend instead of deriving module names from the
# target; generated modules legitimately contain underscores in their names.
$(filter-out $(OUTPUT_DIR)/FStar_SizeT.krml $(OUTPUT_DIR)/TLS13_Impl_Messages.krml,$(ALL_KRML_FILES)): %.krml: | $(OUTPUT_DIR)
	@checked="$(firstword $(filter %.checked,$^))"; \
	  src_full="$${checked%.checked}"; \
	  src="$$(basename "$$src_full")"; \
	  src_arg="$$src"; \
	  if [ -f "$$src_full" ]; then src_arg="$$src_full"; \
	  else \
	    for d in src/spec src/impl $(GENERATED_DIR); do \
	      if [ -f "$$d/$$src" ]; then src_arg="$$d/$$src"; break; fi; \
	    done; \
	  fi; \
	  mod="$${src%.fst}"; mod="$${mod%.fsti}"; \
	  if [ -f "generated/krml/$(notdir $@)" ]; then \
	    cp "generated/krml/$(notdir $@)" "$@"; \
	  elif echo "$$checked" | grep -q '/everparse/src/lowparse/'; then \
	    cache="$$(dirname "$$checked")"; \
	    $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache" --odir $(OUTPUT_DIR) \
	      --warn_error -321 --report_assumes warn \
	      --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	      --ext optimize_let_vc --ext fly_deps $(INCLUDES) "$$src_arg" \
	      --codegen krml --extract_module "$$mod" --krmloutput "$@"; \
	  elif echo "$$checked" | grep -q '/lib/fstar/ulib.checked/'; then \
	    cache="$$(dirname "$$checked")"; \
	    $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache" --odir $(OUTPUT_DIR) \
	      --warn_error -321 --report_assumes warn \
	      --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	      --ext optimize_let_vc --ext fly_deps $(INCLUDES) "$$src" \
	      --codegen krml --extract_module "$$mod" --krmloutput "$@"; \
	  else \
	    case "$$mod" in \
	      Pulse.*|Pulse) cache="$(FSTAR_PREFIX)/lib/fstar/pulse/pulse.checked" ;; \
	      PulseCore.*) cache="$(FSTAR_PREFIX)/lib/fstar/pulse/common.checked" ;; \
	      *) cache="$(CACHE_DIR)" ;; \
	    esac; \
	    if [ "$$cache" = "$(CACHE_DIR)" ]; then \
	    iface="$${src_arg%.fst}.fsti"; \
	    if [ "$$iface" != "$$src_arg" ] && [ -f "$$iface" ]; then \
	      $(FSTAR) "$$iface" || exit $$?; \
	    fi; \
	    $(FSTAR) "$$src_arg" && \
	    $(FSTAR) "$$src_arg" --codegen krml --extract_module "$$mod" --krmloutput "$@"; \
	    else \
	    src_path="$$src_arg"; \
	    if [ -f "$(FSTAR_PREFIX)/lib/fstar/pulse/pulse/lib/$$src" ]; then \
	      src_path="$(FSTAR_PREFIX)/lib/fstar/pulse/pulse/lib/$$src"; \
	    elif [ -f "$(FSTAR_PREFIX)/lib/fstar/pulse/common/$$src" ]; then \
	      src_path="$(FSTAR_PREFIX)/lib/fstar/pulse/common/$$src"; \
	    fi; \
	    iface="$${src%.fst}.fsti"; \
	    iface_path=""; \
	    if [ -f "$(FSTAR_PREFIX)/lib/fstar/pulse/pulse/lib/$$iface" ]; then \
	      iface_path="$(FSTAR_PREFIX)/lib/fstar/pulse/pulse/lib/$$iface"; \
	    elif [ -f "$(FSTAR_PREFIX)/lib/fstar/pulse/common/$$iface" ]; then \
	      iface_path="$(FSTAR_PREFIX)/lib/fstar/pulse/common/$$iface"; \
	    fi; \
	    if [ "$$iface" != "$$src" ] && \
	       [ -n "$$iface_path" ]; then \
	      $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache" --odir $(OUTPUT_DIR) \
	        --warn_error -321 --report_assumes warn \
	        --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	        --ext optimize_let_vc --ext fly_deps $(INCLUDES) "$$iface_path" || exit $$?; \
	    fi; \
	    $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache" --odir $(OUTPUT_DIR) \
	      --warn_error -321 --report_assumes warn \
	      --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	      --ext optimize_let_vc --ext fly_deps $(INCLUDES) "$$src_path" && \
	    $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache" --odir $(OUTPUT_DIR) \
	      --warn_error -321 --report_assumes warn \
	      --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	      --ext optimize_let_vc --ext fly_deps $(INCLUDES) "$$src_path" \
	      --codegen krml --extract_module "$$mod" --krmloutput "$@"; \
	    fi; \
	  fi
	touch -c $@

$(filter-out $(OUTPUT_DIR)/FStar_SizeT.krml,$(ALL_KRML_FILES)): | $(OUTPUT_DIR)/FStar_SizeT.krml

$(KRML_STUB_DIR) $(KRML_STUB_CACHE):
	mkdir -p $@

$(KRML_STUB_DIR)/TLS13.Impl.Messages.fst: src/impl/TLS13.Impl.Messages.fst | $(KRML_STUB_DIR)
	@awk ' \
	  /^[[:space:]]*noextract[[:space:]]*$$/ { pending = 1; next } \
	  pending && /^[[:space:]]*let max_(server_name_len|alpn_len|cipher_suites|signature_schemes|certificate_chain_bytes|certificate_chain_entries|signature_len|record_fragment_len)[[:space:]]*:/ { pending = 0; print; next } \
	  pending { print "noextract"; pending = 0 } \
	  { print } \
	  END { if (pending) print "noextract" }' $< > $@

$(OUTPUT_DIR)/FStar_SizeT.krml: $(FSTAR_ULIB)/FStar.SizeT.fst | $(OUTPUT_DIR)
	@# Extract the *stock* standard-library FStar.SizeT to .krml, reusing the F*
	@# install's already-cached FStar.SizeT.checked (--already_cached 'Prims,FStar'
	@# keeps FStar.SizeT cached, so F* loads it rather than re-checking and never
	@# rewrites the install's ulib.checked/FStar.SizeT.*.checked).  No stub, no
	@# clobber/restore: the extracted client code calls no FStar.SizeT function
	@# (v/uint_to_t stay noextract_to "krml"; all SizeT arithmetic/casts are KaRaMeL
	@# builtins), so the stock module — where v/uint_to_t emit no C — works as-is.
	$(FSTAR_EXE) --odir $(OUTPUT_DIR) --already_cached 'Prims,FStar' \
	  --codegen krml --extract_module FStar.SizeT \
	  $(FSTAR_ULIB)/FStar.SizeT.fst --krmloutput $@

$(OUTPUT_DIR)/TLS13_Impl_Messages.krml: \
  $(KRML_STUB_DIR)/TLS13.Impl.Messages.fst | $(OUTPUT_DIR) $(KRML_STUB_CACHE)
	-cp $(CACHE_DIR)/*.checked $(KRML_STUB_CACHE)/ 2>/dev/null || true
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(KRML_STUB_CACHE) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	  --ext optimize_let_vc --ext fly_deps $(INCLUDES) $<
	$(FSTAR_EXE) --cache_checked_modules --cache_dir $(KRML_STUB_CACHE) --odir $(OUTPUT_DIR) \
	  --warn_error -321 --report_assumes warn \
	  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
	  --ext optimize_let_vc --ext fly_deps $(INCLUDES) \
	  --codegen krml --extract_module TLS13.Impl.Messages $< --krmloutput $@

extract-krml-bundle: $(BUNDLE_KRML_FILES)

extract-driver-krml: $(DRIVER_KRML_FILES)

# The supported extracted artifact is the OpenSSL echo client driver. The older
# all-client bundle sent a much larger dependency closure through KaRaMeL, where
# reachability happens only after several expensive whole-AST passes.
extract-bundle: extract-driver-bundle
	@echo "Extracted OpenSSL echo driver bundle to $(DRIVER_BUNDLE_DIR)"

$(BUNDLE_DIR):
	mkdir -p $@

$(DRIVER_BUNDLE_DIR):
	mkdir -p $@

define POSTPROCESS_DRIVER_BUNDLE_PY
from pathlib import Path
import os
import re

root = Path(os.environ["DRIVER_BUNDLE_DIR"])

for path in list(root.glob("*.c")) + list((root / "internal").glob("*.h")):
    text = path.read_text()

    if path.name == "TLS13_Wire_Generated.c":
        fp_re = re.compile(
            r'(static\s+[A-Za-z_][\w\s\*]*?\n\(\*([A-Za-z_]\w*)\)\([^;]*?\)\s*=\s*)([A-Za-z_]\w+)(;)',
            re.S,
        )
        inits = {m.group(2): m.group(3) for m in fp_re.finditer(text)}

        def resolve(name):
            seen = set()
            while name in inits and name not in seen:
                seen.add(name)
                name = inits[name]
            return name

        text = fp_re.sub(lambda m: m.group(1) + resolve(m.group(3)) + m.group(4), text)

    # The [krml_checked_int_t] (F* [nat]) runtime primitives
    # (Prims.op_*, FStar.UInt8.v/uint_to_t) are provided by the hand-written
    # c_stubs/tls13_prims_runtime.c, which is always compiled and linked.  They
    # used to be injected here into the KaRaMeL-generated
    # FStar_Pulse_PulseCore_Prims.c, but that file is no longer emitted now that
    # the client uses the stock FStar.SizeT (it calls no FStar.SizeT function),
    # so a generated host file can no longer be relied upon.


    if path.name == "TLS13_Transcript.c":
        text = text.replace(
            "Prims_list__uint8_t *TLS13_Transcript_empty = TLS13_Bytes_empty;",
            "Prims_list__uint8_t *TLS13_Transcript_empty;",
        )

    if path.name == "TLS13_ConnectionLog.c":
        text = text.replace(
            "TLS13_ConnectionLog_raw_io_log\n"
            "TLS13_ConnectionLog_empty_raw_io_log =\n"
            "  { .raw_sent = TLS13_Bytes_empty, .raw_received = TLS13_Bytes_empty };",
            "TLS13_ConnectionLog_raw_io_log\n"
            "TLS13_ConnectionLog_empty_raw_io_log;",
        )

    if path.name == "TLS13_Spec_ConnectionState.c":
        text = re.sub(
            r'TLS13_Spec_ConnectionState_handshake_buffer_state\n'
            r'TLS13_Spec_ConnectionState_empty_handshake_buffer_state =\n'
            r'  \{\n'
            r'    \.hb_client_hello_bytes = TLS13_Bytes_empty, \.hb_server_hello_bytes = TLS13_Bytes_empty,\n'
            r'    \.hb_encrypted_server_handshake_bytes = TLS13_Bytes_empty,\n'
            r'    \.hb_encrypted_server_handshake_parsed = 0,\n'
            r'    \.hb_certificate_leaf_der = \{ \.tag = FStar_Pervasives_Native_None \},\n'
            r'    \.hb_certificate_verify_input = \{ \.tag = FStar_Pervasives_Native_None \}\n'
            r'  \};',
            "TLS13_Spec_ConnectionState_handshake_buffer_state\n"
            "TLS13_Spec_ConnectionState_empty_handshake_buffer_state;",
            text,
        )

    path.write_text(text)

krmlinit = root / "krmlinit.c"
if krmlinit.exists():
    text = krmlinit.read_text()
    marker = "  TLS13_Bytes_empty = FStar_Seq_Base_create__uint8_t(0, TLS13_Bytes_zero);\n"
    text = text.replace(
        "  TLS13_Keys_empty_hash = TLS13_Crypto_Spec_sha256(TLS13_Bytes_empty);\n",
        "  TLS13_Keys_empty_hash = TLS13_Bytes_zeros(32);\n",
    )
    init_block = """  TLS13_Transcript_empty = TLS13_Bytes_empty;
  TLS13_ConnectionLog_empty_raw_io_log =
    ((TLS13_ConnectionLog_raw_io_log){ .raw_sent = TLS13_Bytes_empty, .raw_received = TLS13_Bytes_empty });
  TLS13_Spec_ConnectionState_empty_handshake_buffer_state =
    ((TLS13_Spec_ConnectionState_handshake_buffer_state){
      .hb_client_hello_bytes = TLS13_Bytes_empty,
      .hb_server_hello_bytes = TLS13_Bytes_empty,
      .hb_encrypted_server_handshake_bytes = TLS13_Bytes_empty,
      .hb_encrypted_server_handshake_parsed = 0,
      .hb_certificate_leaf_der = { .tag = FStar_Pervasives_Native_None },
      .hb_certificate_verify_input = { .tag = FStar_Pervasives_Native_None }
    });
"""
    if init_block not in text:
        text = text.replace(marker, marker + init_block)
    krmlinit.write_text(text)
endef
export POSTPROCESS_DRIVER_BUNDLE_PY

extract-driver-bundle: extract-driver-krml | $(DRIVER_BUNDLE_DIR)
	@echo "Extracting TLS13 client driver slice..."
	@rm -f $(DRIVER_BUNDLE_DIR)/*.c $(DRIVER_BUNDLE_DIR)/*.h $(DRIVER_BUNDLE_DIR)/internal/*.h
	$(KRML_EXE) \
	  -tmpdir $(DRIVER_BUNDLE_DIR) \
	  -skip-compilation \
	  -add-include '<stdbool.h>' \
	  -add-include '"krml/internal/compat.h"' \
	  -add-include '"../../c_stubs/tls13_crypto_external.h"' \
	  -add-include '"../../c_stubs/tls13_spec_types.h"' \
	  -add-include '"../../c_stubs/tls13_io_karamel.h"' \
	  -add-include '"../../c_stubs/tls13_openssl_karamel.h"' \
	  -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	  -library TLS13.Crypto -library TLS13.X509 -library TLS13.IO \
	  -library TLS13.OpenSSL \
	  -bundle 'TLS13.Crypto.Spec,TLS13.X509.Spec,TLS13.Record.Spec,TLS13.Handshake.Spec,TLS13.Wire.Spec,TLS13.Wire.Spec.*' \
	  -bundle 'TLS13.Wire.Generated.*' \
	  -bundle 'LowParse.\*' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -warn-error '@2-26' \
	  -warn-error '+9' \
	  -no-prefix TLS13.Impl.Client \
	  $(DRIVER_KRML_FILES)
	DRIVER_BUNDLE_DIR="$(DRIVER_BUNDLE_DIR)" python3 -c "$$POSTPROCESS_DRIVER_BUNDLE_PY"

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

ECHO_STUB_SOURCES = \
  c_stubs/tls13_crypto_external.c \
  c_stubs/tls13_pulse_shims.c \
  c_stubs/tls13_prims_runtime.c \
  c_stubs/tls13_io_karamel.c \
  c_stubs/tls13_io_stubs.c \
  c_stubs/tls13_openssl_karamel.c \
  c_stubs/tls13_openssl_stubs.c \
  c_stubs/tls13_hacl_stubs.c

ECHO_STUB_HEADERS = \
  c_stubs/tls13_crypto_external.h \
  c_stubs/tls13_hacl_stubs.h \
  c_stubs/tls13_io_karamel.h \
  c_stubs/tls13_io_stubs.h \
  c_stubs/tls13_openssl_karamel.h \
  c_stubs/tls13_openssl_stubs.h \
  c_stubs/tls13_spec_types.h

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
.PHONY: test test-extracted-client-openssl-echo test-openssl-echo check-c-stubs

test: verify check-c-stubs test-openssl-echo

# ── Echo C Stub Syntax Check ───────────────────────────────────────
check-c-stubs: | check-deps
	$(CC) -fsyntax-only -Wall -Wextra -Wno-deprecated-declarations \
	  -I c_stubs -I $(HACL_DIR) -I $(HACL_DIR)/internal \
	  -I $(HACL_KI) -I $(HACL_KL) \
	  -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	  $(ECHO_STUB_SOURCES)

# ── OpenSSL Echo Test ──────────────────────────────────────────────
test/certs/chain.pem test/certs/ca.pem test/certs/leaf.key test/certs/leaf.der: \
  scripts/generate-test-certs.sh
	scripts/generate-test-certs.sh test/certs

test/test_extracted_client_openssl_echo: \
  test/unit/test_extracted_client_openssl_echo.c extract-driver-bundle \
  runtime/tls13_client_driver.c runtime/tls13_client_driver.h \
  $(ECHO_STUB_SOURCES) $(ECHO_STUB_HEADERS) $(HACL_WRAPPER_SOURCES) | check-deps
	$(CC) $(CFLAGS_COMMON) \
	  -I_extract/driver_bundle -I_extract/driver_bundle/internal \
	  _extract/driver_bundle/*.c \
	  c_stubs/tls13_crypto_external.c \
	  c_stubs/tls13_pulse_shims.c \
	  c_stubs/tls13_prims_runtime.c \
	  runtime/tls13_client_driver.c \
	  c_stubs/tls13_io_karamel.c \
	  c_stubs/tls13_io_stubs.c \
	  c_stubs/tls13_openssl_karamel.c \
	  c_stubs/tls13_openssl_stubs.c \
	  test/unit/test_extracted_client_openssl_echo.c \
	  $(HACL_WRAPPER_SOURCES) \
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
	@test -f third_party/rfc/rfc8446.txt || \
	  { echo "Missing RFC 8446 cache; run scripts/fetch-rfcs.sh"; exit 1; }
	@test -f third_party/rfc/rfc8448.txt || \
	  { echo "Missing RFC 8448 cache; run scripts/fetch-rfcs.sh"; exit 1; }

# ── Cleanup ────────────────────────────────────────────────────────
clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR) $(EXTRACT_DIR) .depend
	rm -f test/test_extracted_client_openssl_echo \
	  test/openssl_echo_server test/openssl_echo_server.port \
	  test/openssl_echo_server.log
	find src test -name '*.checked' -delete

.PHONY: all verify test extract-krml extract-connection extract-smoke extract-bundle \
  test-extracted-client-openssl-echo \
  test-client test-openssl-echo check-c-stubs check-toolchain check-deps clean
