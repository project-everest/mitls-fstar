#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dest_dir="${1:-"$repo_root/third_party/rfc"}"

mkdir -p "$dest_dir"

fetch_rfc() {
  local number="$1"
  local url="https://www.rfc-editor.org/rfc/rfc${number}.txt"
  local dest="$dest_dir/rfc${number}.txt"
  local tmp
  tmp="$(mktemp "$dest.XXXXXX")"

  curl --fail --location --show-error --silent "$url" --output "$tmp"
  mv "$tmp" "$dest"
  echo "fetched $dest"
}

fetch_rfc 8446
fetch_rfc 8448

