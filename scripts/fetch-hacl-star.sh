#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$repo_root"

if [ ! -f .gitmodules ] || ! git config --file .gitmodules --get-regexp '^submodule\.third_party/hacl-star\.' >/dev/null; then
  echo "HACL* submodule is not configured; run: git submodule add https://github.com/hacl-star/hacl-star.git third_party/hacl-star" >&2
  exit 1
fi

git submodule update --init --depth 1 third_party/hacl-star
git -C third_party/hacl-star rev-parse HEAD

if [ ! -d third_party/hacl-star/dist/gcc-compatible ]; then
  echo "HACL* checkout does not contain dist/gcc-compatible" >&2
  exit 1
fi

echo "HACL* C snapshot is available at third_party/hacl-star/dist/gcc-compatible"
