#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODE="visible"
if [[ "${1:-}" == "--headless" ]]; then
  MODE="headless"
  shift
fi
if (( $# != 0 )); then
  echo "usage: run-demo.sh [--headless]" >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/mitls-chromium-demo.XXXXXX")"
SERVER_PID=""
cleanup() {
  if [[ -n "$SERVER_PID" ]]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  if [[ "${MITLS_DEMO_KEEP_ARTIFACTS:-0}" == "1" ]]; then
    echo "Demo artifacts retained in $WORK" >&2
  else
    rm -rf "$WORK"
  fi
}
trap cleanup EXIT

"$ROOT/start-server.sh" "$WORK/server.port" >"$WORK/server.log" 2>&1 &
SERVER_PID=$!

for _ in {1..100}; do
  if [[ -s "$WORK/server.port" ]]; then
    break
  fi
  if ! kill -0 "$SERVER_PID" 2>/dev/null; then
    echo "The HTTPS demo server exited before publishing its port." >&2
    cat "$WORK/server.log" >&2
    exit 1
  fi
  sleep 0.1
done
if [[ ! -s "$WORK/server.port" ]]; then
  echo "Timed out waiting for the HTTPS demo server." >&2
  exit 1
fi

URL="https://localhost:$(cat "$WORK/server.port")/"
export MITLS_CHROME_PROFILE="$WORK/chromium-profile"

if [[ "$MODE" == "headless" ]]; then
  if ! "$ROOT/launch-chrome.sh" "$URL" \
      --headless \
      --disable-gpu \
      --dump-dom \
      >"$WORK/page.dom" 2>"$WORK/chromium.log"; then
    echo "Chromium failed while loading the HTTPS demo page." >&2
    cat "$WORK/chromium.log" >&2
    exit 1
  fi
else
  echo "Opening $URL with the verified miTLS Chromium build."
  "$ROOT/launch-chrome.sh" "$URL" \
    2> >(tee "$WORK/chromium.log" >&2)
fi

if [[ "$MODE" == "headless" ]] &&
   ! grep -q "verified chromium demo" "$WORK/page.dom"; then
  echo "Chromium did not render the expected HTTPS page." >&2
  cat "$WORK/chromium.log" >&2
  exit 1
fi
if ! grep -q "Verified miTLS provider selected" "$WORK/chromium.log"; then
  echo "Chromium did not report selection of the verified miTLS provider." >&2
  cat "$WORK/chromium.log" >&2
  exit 1
fi

if [[ "$MODE" == "headless" ]]; then
  echo "Verified miTLS Chromium rendered the bundled HTTPS page successfully."
fi
