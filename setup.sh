#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")" && pwd)"
fstar_dir="$repo_root/tools/FStar"
source_flag="--nightly"
version="2026-06-09"

usage() {
  cat <<'EOF'
Usage:
  ./setup.sh [--nightly] [--version VERSION]

Installs a repository-local F* binary toolchain into tools/FStar using the
official installer with --no-link. The Makefile uses only this local toolchain
unless FSTAR_EXE/KRML_EXE are explicitly overridden.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --nightly)
      source_flag="--nightly"
      version=""
      shift
      ;;
    --version)
      if [ "$#" -lt 2 ]; then
        echo "--version requires an argument" >&2
        exit 1
      fi
      source_flag=""
      version="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

for cmd in bash curl; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing prerequisite: $cmd" >&2
    exit 1
  fi
done

if [ ! -x "$fstar_dir/bin/fstar.exe" ]; then
  args=(--dest "$fstar_dir" --no-link)
  if [ -n "$source_flag" ]; then
    args=("$source_flag" "${args[@]}")
  fi
  if [ -n "$version" ]; then
    args=(--version "$version" "${args[@]}")
  fi

  curl --fail --location --show-error --silent https://aka.ms/install-fstar \
    | bash -s -- "${args[@]}"
fi

if [ ! -x "$fstar_dir/bin/fstar.exe" ]; then
  echo "F* installation failed: $fstar_dir/bin/fstar.exe not found" >&2
  exit 1
fi

compat="$fstar_dir/karamel"
if [ ! -x "$compat/krml" ]; then
  rm -rf "$compat"
  mkdir -p "$compat"
  ln -s ../bin/krml "$compat/krml"
  ln -s ../include/krml "$compat/include"
  ln -s ../lib/krml "$compat/krmllib"
fi

"$repo_root/scripts/fetch-hacl-star.sh"
"$repo_root/scripts/fetch-rfcs.sh"
"$repo_root/scripts/check-openssl.sh"

"$fstar_dir/bin/fstar.exe" --version
echo "Local F* toolchain is ready in tools/FStar"

