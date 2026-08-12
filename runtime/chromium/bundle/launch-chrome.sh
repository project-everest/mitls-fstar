#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODE="local"
while [[ "${1:-}" == --* ]]; do
  case "$1" in
    --public)
      MODE="public"
      shift
      ;;
    --trace)
      export ATLAS_TRACE_FILE="${2:?--trace requires an output file}"
      shift 2
      ;;
    *)
      break
      ;;
  esac
done
URL="${1:?usage: launch-chrome.sh [--public] [--trace FILE] URL [CHROMIUM_ARGUMENT ...]}"
shift

"$ROOT/check-deps.sh"

PROFILE="${ATLAS_CHROME_PROFILE:-${XDG_CACHE_HOME:-$HOME/.cache}/atlas-chromium-demo-profile}"
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
  --use-atlas \
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
