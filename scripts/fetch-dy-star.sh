#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dy_path="third_party/dolev-yao-star-extrinsic"
expected_commit="b599e1fdca22a7fd97634320a7f882794fcbc28a"

cd "$repo_root"

if [ ! -f .gitmodules ] ||
   ! git config --file .gitmodules --get-regexp \
     '^submodule\.third_party/dolev-yao-star-extrinsic\.' >/dev/null; then
  echo "DY* submodule is not configured at $dy_path" >&2
  exit 1
fi

git submodule update --init "$dy_path"

actual_commit="$(git -C "$dy_path" rev-parse HEAD)"
if [ "$actual_commit" != "$expected_commit" ]; then
  echo "DY* is at $actual_commit; expected $expected_commit" >&2
  exit 1
fi

if [ ! -f "$dy_path/src/core/DY.Core.fst" ]; then
  echo "DY* checkout does not contain the core modules" >&2
  exit 1
fi

echo "DY* core is available at $expected_commit"
