#!/usr/bin/env bash
# Clone and build EverParse (QuackyDucky + LowParse + the F*/KaRaMeL toolchain it
# vendors under opt/FStar) from the fork/branch used by this project.
#
# `make quackyducky` in the EverParse tree builds everything we need:
#   - the F* binary           at opt/FStar/out/bin/fstar.exe (symlinked opt/FStar/bin/fstar.exe)
#   - the KaRaMeL binary       at opt/FStar/karamel/out/bin/krml
#   - the QuackyDucky compiler at bin/qd.exe
#   - the verified LowParse + LowParse.Pulse .checked libraries under src/lowparse
#
# The agentic-tls Makefile consumes this toolchain via EVERPARSE_HOME (no separate
# F* install is required).
set -euo pipefail

EVERPARSE_REPO="${EVERPARSE_REPO:-https://github.com/project-everest/everparse}"
EVERPARSE_BRANCH="${EVERPARSE_BRANCH:-fstar2}"
# Pinned EverParse commit this project is verified against.  The branch above is
# only used as a fetch hint; the build always checks out this exact commit so the
# toolchain is reproducible regardless of where the branch tip has moved.
EVERPARSE_COMMIT="${EVERPARSE_COMMIT:-6f1f390e0c8c376ce45facdb75c9af4e5aa3f11d}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Default location: tools/everparse inside the agentic-tls checkout (matches the
# Makefile's EVERPARSE_HOME default of $(CURDIR)/tools/everparse, and the
# tools/FStar convention used previously).  Override with EVERPARSE_HOME.
EVERPARSE_HOME="${EVERPARSE_HOME:-$repo_root/tools/everparse}"
jobs="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

fstar_exe="$EVERPARSE_HOME/opt/FStar/out/bin/fstar.exe"
krml_exe="$EVERPARSE_HOME/opt/karamel/out/bin/krml"
qd_exe="$EVERPARSE_HOME/bin/qd.exe"

for cmd in git make opam; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing prerequisite: $cmd" >&2
    exit 1
  fi
done

if [ -x "$fstar_exe" ] && [ -x "$krml_exe" ] && [ -x "$qd_exe" ]; then
  echo "EverParse toolchain already built in $EVERPARSE_HOME"
  exit 0
fi

if [ ! -d "$EVERPARSE_HOME/.git" ]; then
  echo "Cloning EverParse ($EVERPARSE_REPO @ $EVERPARSE_BRANCH) into $EVERPARSE_HOME ..."
  mkdir -p "$(dirname "$EVERPARSE_HOME")"
  git clone --branch "$EVERPARSE_BRANCH" "$EVERPARSE_REPO" "$EVERPARSE_HOME"
else
  echo "Updating existing EverParse checkout in $EVERPARSE_HOME ..."
  git -C "$EVERPARSE_HOME" fetch origin "$EVERPARSE_BRANCH"
fi

echo "Checking out pinned EverParse commit $EVERPARSE_COMMIT ..."
git -C "$EVERPARSE_HOME" checkout --quiet "$EVERPARSE_COMMIT"

echo "Building EverParse (make quackyducky -j$jobs) — this also builds F* and KaRaMeL ..."
make -C "$EVERPARSE_HOME" -j"$jobs" quackyducky

for f in "$fstar_exe" "$krml_exe" "$qd_exe"; do
  if [ ! -x "$f" ]; then
    echo "EverParse build did not produce $f" >&2
    exit 1
  fi
done

echo "EverParse toolchain ready in $EVERPARSE_HOME"
echo "  F*:          $fstar_exe"
echo "  KaRaMeL:     $krml_exe"
echo "  QuackyDucky: $qd_exe"
