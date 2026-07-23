#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")" && pwd)"

usage() {
  cat <<'USAGE'
Usage:
  ./setup.sh [--everparse-home DIR] [--jobs N]

Builds the EverParse toolchain (QuackyDucky + LowParse + the F*/KaRaMeL binaries
it vendors) from the fork/branch used by this project, installs the required Z3
versions, then fetches the DY* and HACL* snapshots and checks OpenSSL.  The
Makefile consumes this toolchain via EVERPARSE_HOME; no separate F* installation
is required.

Environment overrides:
  EVERPARSE_HOME    where to clone/build EverParse (default: tools/everparse)
  EVERPARSE_REPO    git URL     (default: https://github.com/project-everest/everparse)
  EVERPARSE_BRANCH  git branch  (default: fstar2)
  EVERPARSE_COMMIT  pinned commit to build (default: recorded in scripts/build-everparse.sh)
  Z3_DIR            solver installation directory (default: tools/everparse/opt/z3)
  JOBS              parallelism for the EverParse build (default: nproc)
USAGE
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --everparse-home)
      [ "$#" -ge 2 ] || { echo "--everparse-home requires an argument" >&2; exit 1; }
      export EVERPARSE_HOME="$2"; shift 2 ;;
    --jobs)
      [ "$#" -ge 2 ] || { echo "--jobs requires an argument" >&2; exit 1; }
      export JOBS="$2"; shift 2 ;;
    -h|--help)
      usage; exit 0 ;;
    *)
      echo "unknown argument: $1" >&2; usage >&2; exit 1 ;;
  esac
done

for cmd in bash curl git make opam unzip; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing prerequisite: $cmd" >&2
    exit 1
  fi
done

# 1. Build EverParse (F*, KaRaMeL, QuackyDucky, LowParse) from the fork.
"$repo_root/scripts/build-everparse.sh"

# 2. Install the solver versions used by TLS and DY*.
"$repo_root/scripts/install-z3.sh"

# 3. Project dependencies.
"$repo_root/scripts/fetch-dy-star.sh"
"$repo_root/scripts/fetch-hacl-star.sh"
"$repo_root/scripts/check-openssl.sh"

echo "Setup complete.  Run 'make verify' to check the F* development."
