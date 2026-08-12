#!/usr/bin/env bash
# Install the Z3 version this project verifies against into $EVERPARSE_HOME/opt/z3.
#
# F* locates its solver by looking for a binary named `z3-<version>` on PATH, and
# the Makefiles put $(EVERPARSE_HOME)/opt/z3 on PATH and pass
# `--z3version $(Z3_VERSION)`.  The EverParse toolchain build drops the version it
# pins (4.13.3) into that same directory; this script adds ours alongside it, so
# both remain available and `make verify Z3_VERSION=4.13.3` still works.
#
# Why 4.15.3: Z3 4.13.3 hits an internal assertion failure in the LP arithmetic
# solver (`../src/math/lp/lar_solver.cpp:1066`, "m_columns_with_changed_bounds
# .empty()") on some of this project's arithmetic-heavy system-level queries.
# The solver aborts mid-answer and F* then fails to parse its output.  4.15.3
# fixes it.
set -euo pipefail

# Single source of truth, shared with the Makefiles and the CI dev-container
# cache key.
z3_version_file="$(dirname "$0")/z3-version.txt"
if [ -z "${Z3_VERSION:-}" ]; then
  if [ ! -r "$z3_version_file" ]; then
    echo "Cannot read the pinned Z3 version from $z3_version_file" >&2
    exit 1
  fi
  Z3_VERSION="$(tr -d '[:space:]' < "$z3_version_file")"
fi
if [ -z "$Z3_VERSION" ]; then
  echo "Pinned Z3 version is empty ($z3_version_file)" >&2
  exit 1
fi
# Which prebuilt release archive to fetch.  Z3 publishes per-glibc builds; this
# one matches the devcontainer base image.
Z3_ARCHIVE="${Z3_ARCHIVE:-z3-${Z3_VERSION}-x64-glibc-2.39.zip}"
Z3_URL="${Z3_URL:-https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${Z3_ARCHIVE}}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
EVERPARSE_HOME="${EVERPARSE_HOME:-$repo_root/tools/everparse}"
z3_dir="${Z3_DIR:-$EVERPARSE_HOME/opt/z3}"
target="$z3_dir/z3-$Z3_VERSION"

# Already provisioned in the directory consumed by the Makefiles?
if [ -x "$target" ]; then
  echo "Z3 $Z3_VERSION already installed at $target"
  exit 0
fi

for cmd in curl unzip; do
  command -v "$cmd" >/dev/null 2>&1 || { echo "missing prerequisite: $cmd" >&2; exit 1; }
done

mkdir -p "$z3_dir"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "Downloading Z3 $Z3_VERSION from $Z3_URL ..."
curl -fsSL "$Z3_URL" -o "$tmp/z3.zip"
unzip -q "$tmp/z3.zip" -d "$tmp"

src="$(find "$tmp" -type f -name z3 -perm -u+x -print -quit)"
[ -n "$src" ] || { echo "no z3 binary found in $Z3_ARCHIVE" >&2; exit 1; }

install -m 0755 "$src" "$target"
"$target" --version

echo "Z3 $Z3_VERSION installed at $target"
