#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
URL="${1:?usage: launch-chrome.sh URL [CHROMIUM_ARGUMENT ...]}"
shift

"$ROOT/check-deps.sh"

PROFILE="${MITLS_CHROME_PROFILE:-${XDG_CACHE_HOME:-$HOME/.cache}/mitls-chromium-demo-profile}"
mkdir -p "$PROFILE"

exec "$ROOT/chromium/chrome" \
  --use-verified-mitls \
  --no-sandbox \
  --disable-field-trial-config \
  --disable-features=EncryptedClientHello,AddTLSServerHandshakePadding,TLSTrustAnchorIDs \
  --ignore-certificate-errors \
  --disable-background-networking \
  --disable-component-update \
  --disable-default-apps \
  --disable-sync \
  --disable-quic \
  --no-proxy-server \
  --no-default-browser-check \
  --no-first-run \
  --lang=en-US \
  --enable-logging=stderr \
  --log-level=0 \
  --user-data-dir="$PROFILE" \
  "$@" \
  "$URL"
