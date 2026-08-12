#!/bin/bash
# Incremental single-file F* check using the Makefile flags.
#
# Usage:  scripts/fcheck.sh <file.fst|.fsti> [extra fstar flags...]
#
# Environment:
#   Z3_VERSION  solver to use (default 4.15.3, matching the root Makefile)
#   CACHE_DIR   .checked directory (default _cache).  Point this at a scratch
#               directory when probing a change you do not want to keep, so a
#               speculative result never lands in the real cache.
#
# See deviteration.md for how to use this for fast proof iteration.
set -e
cd "$(dirname "$0")/.."
export FSTAR_EXE=${FSTAR_EXE:-$(realpath tools/everparse/opt/FStar/bin/fstar.exe)}
# F* finds Z3 (z3-<version>) on PATH; the toolchain ships it under opt/z3.
export PATH="$(realpath tools/everparse/opt/z3):$PATH"
LP=$(realpath tools/everparse/src/lowparse)
exec "$FSTAR_EXE" \
  --z3version "${Z3_VERSION:-4.15.3}" \
  --cache_checked_modules --cache_dir "${CACHE_DIR:-_cache}" --odir _output \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
  --ext optimize_let_vc --ext fly_deps \
  --include common \
  --include src/spec --include src/spec/assumptions --include src/spec/common \
  --include src/spec/core --include src/spec/properties \
  --include src/impl --include src/impl/extern --include generated \
  --include "$LP" --include "$LP/pulse" \
  "$@"
