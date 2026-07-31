#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODE="local"
if [[ "${1:-}" == "--public" ]]; then
  MODE="public"
  shift
fi
URL="${1:?usage: launch-chrome.sh [--public] URL [CHROMIUM_ARGUMENT ...]}"
shift

"$ROOT/check-deps.sh"

PROFILE="${MITLS_CHROME_PROFILE:-${XDG_CACHE_HOME:-$HOME/.cache}/mitls-chromium-demo-profile}"
mkdir -p "$PROFILE"

declare -a mode_arguments
if [[ "$MODE" == "public" ]]; then
  mode_arguments=()
else
  case "$URL" in
    https://localhost|https://localhost/*|https://localhost:*) ;;
    *)
      echo "Non-local URLs require --public so certificate errors are enforced." >&2
      exit 2
      ;;
  esac
  mode_arguments=(
    --ignore-certificate-errors
    '--host-resolver-rules=MAP * ~NOTFOUND, EXCLUDE localhost'
  )
fi

exec "$ROOT/chromium/chrome" \
  --use-verified-mitls \
  --no-sandbox \
  --disable-gpu \
  --disable-field-trial-config \
  --disable-features=EncryptedClientHello,AddTLSServerHandshakePadding,TLSTrustAnchorIDs,Prewarm \
  --disable-background-networking \
  --disable-client-side-phishing-detection \
  --disable-component-extensions-with-background-pages \
  --disable-component-update \
  --disable-default-apps \
  --disable-domain-reliability \
  --disable-sync \
  --disable-quic \
  --no-proxy-server \
  --no-service-autorun \
  --no-default-browser-check \
  --no-first-run \
  --password-store=basic \
  --lang=en-US \
  --enable-logging=stderr \
  --log-level=0 \
  --user-data-dir="$PROFILE" \
  "${mode_arguments[@]}" \
  "$@" \
  "$URL"
