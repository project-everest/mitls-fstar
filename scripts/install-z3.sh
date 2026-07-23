#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
everparse_home="${EVERPARSE_HOME:-$repo_root/tools/everparse}"
fstar_home="${FSTAR_HOME:-$everparse_home/opt/FStar}"
z3_dir="${Z3_DIR:-$everparse_home/opt/z3}"
installer="$fstar_home/.scripts/get_fstar_z3.sh"

if [ ! -f "$installer" ]; then
  echo "F* Z3 installer not found at $installer; build the toolchain first." >&2
  exit 1
fi

bash "$installer" "$z3_dir"

for version in 4.13.3 4.15.3; do
  solver="$z3_dir/z3-$version"
  if [ ! -x "$solver" ]; then
    echo "Z3 $version was not installed at $solver" >&2
    exit 1
  fi
  "$solver" -version
done
