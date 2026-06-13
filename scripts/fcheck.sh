#!/bin/bash
# Incremental single-file F* check using the Makefile flags.
set -e
cd "$(dirname "$0")/.."
export FSTAR_EXE=${FSTAR_EXE:-$(realpath tools/everparse/opt/FStar/bin/fstar.exe)}
# F* finds Z3 (z3-<version>) on PATH; the toolchain ships it under opt/z3.
export PATH="$(realpath tools/everparse/opt/z3):$PATH"
LP=$(realpath tools/everparse/src/lowparse)
exec "$FSTAR_EXE" \
  --cache_checked_modules --cache_dir _cache --odir _output \
  --warn_error -321 --report_assumes warn \
  --already_cached 'Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse -TLS13 +TLS13.Wire.Generated' \
  --ext optimize_let_vc --ext fly_deps \
  --include src/spec --include src/impl --include generated \
  --include "$LP" --include "$LP/pulse" \
  "$@"
