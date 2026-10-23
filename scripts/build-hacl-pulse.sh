#!/usr/bin/env bash
# Clone hacl-pulse (https://github.com/FStarLang/hacl-pulse) at the pinned
# commit and build its C distribution, dist/Hacl.c and dist/Hacl.h, with the F*
# from the EverParse toolchain (scripts/build-everparse.sh must run first).
#
# hacl-pulse does not commit dist/: `make extract` verifies the library and
# extracts it with Custard.  The agentic-tls Makefile compiles dist/Hacl.c
# together with c/Hacl_Random.c (the platform entropy shim) and never re-runs
# hacl-pulse's own make.  TLS13.Crypto calls hacl-pulse from Pulse, so the
# Makefile also needs the checked files in obj/cache and the Custard unit
# interface obj/build/Hacl.cui that extraction links against: keep them.
set -euo pipefail

HACL_PULSE_REPO="${HACL_PULSE_REPO:-https://github.com/FStarLang/hacl-pulse}"
# Pinned hacl-pulse commit.  The build always checks out this exact commit.
HACL_PULSE_COMMIT="${HACL_PULSE_COMMIT:-4a1b5b7cb4e7d02c0feb1463ea8644efa5b592b0}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HACL_PULSE_HOME="${HACL_PULSE_HOME:-$repo_root/tools/hacl-pulse}"
EVERPARSE_HOME="${EVERPARSE_HOME:-$repo_root/tools/everparse}"
FSTAR_EXE="${FSTAR_EXE:-$EVERPARSE_HOME/opt/FStar/bin/fstar.exe}"
jobs="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

dist="$HACL_PULSE_HOME/dist"
stamp="$dist/.commit"

if [ -f "$dist/Hacl.c" ] && [ -f "$dist/Hacl.h" ] && [ -f "$stamp" ] &&
   [ "$(cat "$stamp")" = "$HACL_PULSE_COMMIT" ]; then
  echo "hacl-pulse dist already built at $HACL_PULSE_COMMIT in $dist"
  exit 0
fi

if [ ! -x "$FSTAR_EXE" ]; then
  echo "No F* at $FSTAR_EXE; run scripts/build-everparse.sh first" >&2
  exit 1
fi

if [ ! -d "$HACL_PULSE_HOME/.git" ]; then
  echo "Cloning hacl-pulse ($HACL_PULSE_REPO) into $HACL_PULSE_HOME ..."
  mkdir -p "$(dirname "$HACL_PULSE_HOME")"
  git clone "$HACL_PULSE_REPO" "$HACL_PULSE_HOME"
else
  echo "Updating existing hacl-pulse checkout in $HACL_PULSE_HOME ..."
  git -C "$HACL_PULSE_HOME" remote set-url origin "$HACL_PULSE_REPO"
  git -C "$HACL_PULSE_HOME" fetch origin
fi

echo "Checking out pinned hacl-pulse commit $HACL_PULSE_COMMIT ..."
git -C "$HACL_PULSE_HOME" checkout --quiet "$HACL_PULSE_COMMIT"
rm -f "$stamp"

echo "Verifying and extracting hacl-pulse (make extract -j$jobs) ..."
make -C "$HACL_PULSE_HOME" -j"$jobs" extract FSTAR_EXE="$FSTAR_EXE"

for f in "$dist/Hacl.c" "$dist/Hacl.h" "$HACL_PULSE_HOME/c/Hacl_Random.c" \
         "$HACL_PULSE_HOME/obj/build/Hacl.cui"; do
  if [ ! -f "$f" ]; then
    echo "hacl-pulse build did not produce $f" >&2
    exit 1
  fi
done
echo "$HACL_PULSE_COMMIT" > "$stamp"

echo "hacl-pulse C distribution ready in $dist"
