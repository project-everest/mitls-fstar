#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "This bundle requires Linux x86_64." >&2
  exit 1
fi

declare -a binaries=(
  "$ROOT/chromium/chrome"
  "$ROOT/chromium/chrome_crashpad_handler"
  "$ROOT/server/openssl_http_server"
)

shopt -s nullglob
for library in "$ROOT"/chromium/*.so; do
  binaries+=("$library")
done

missing=0
for binary in "${binaries[@]}"; do
  if [[ ! -x "$binary" && "$binary" != *.so ]]; then
    echo "Missing executable: $binary" >&2
    missing=1
    continue
  fi
  dependencies="$(ldd "$binary" 2>&1)" || {
    echo "Unable to inspect dynamic dependencies for $binary:" >&2
    echo "$dependencies" >&2
    missing=1
    continue
  }
  if grep -q "not found" <<<"$dependencies"; then
    echo "Missing dynamic dependencies for $binary:" >&2
    grep "not found" <<<"$dependencies" >&2
    missing=1
  fi
done

if (( missing != 0 )); then
  echo "Install the missing compatible system libraries before running the demo." >&2
  exit 1
fi
