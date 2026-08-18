#!/usr/bin/env bash
# Discard the .checked caches when the F* build that produced them has changed.
#
# A .checked file is specific to the F* build that wrote it.  F* validates a
# cached module against its source hash, but NOT against the version of F* that
# produced it, and loading a .checked written by a different build does not fail
# cleanly: it can segfault the typechecker deep inside FStarC.Syntax.Subst, with
# nothing in the output pointing at the cache.  The cache trees are gitignored
# build products that survive `git pull` and a toolchain rebuild, so a bump of
# the pinned EverParse/F* commit leaves them behind by default.
#
# The Makefile runs this at parse time -- before `.depend` is read -- because
# removing the generated .checked files partway through a build would pull rules
# out from under a dependency graph make has already computed.
set -euo pipefail

fstar_exe="${1:?usage: invalidate-stale-cache.sh FSTAR_EXE STAMP [PATH ...]}"
stamp="${2:?missing stamp path}"
shift 2

# Nothing to do before the toolchain exists; `make check-toolchain` reports that
# case with a usable message, and this script must stay silent so it does not
# corrupt the $(shell ...) expansion that calls it.
command -v "$fstar_exe" >/dev/null 2>&1 || [ -x "$fstar_exe" ] || exit 0

version="$("$fstar_exe" --version 2>/dev/null | tr '\n' ' ')"
[ -n "$version" ] || exit 0

if [ -f "$stamp" ] && [ "$(cat "$stamp")" = "$version" ]; then
  exit 0
fi

if [ -f "$stamp" ]; then
  echo "F* version changed; discarding .checked caches built by the previous toolchain" >&2
fi

for path in "$@"; do
  rm -rf "$path"
done

printf '%s' "$version" > "$stamp"
