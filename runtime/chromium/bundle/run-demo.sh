#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODE="visible"
TRACE_FILE=""
while (( $# > 0 )); do
  case "$1" in
    --headless)
      MODE="headless"
      shift
      ;;
    --trace)
      TRACE_FILE="${2:?--trace requires an output file}"
      shift 2
      ;;
    *)
      break
      ;;
  esac
done
if (( $# != 0 )); then
  echo "usage: run-demo.sh [--headless] [--trace FILE]" >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/atlas-chromium-demo.XXXXXX")"
SERVER_PID=""
cleanup() {
  status=$?
  trap - EXIT
  if [[ -n "$SERVER_PID" ]]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  if [[ "${ATLAS_DEMO_KEEP_ARTIFACTS:-0}" == "1" || "$status" != "0" ]]; then
    echo "Demo artifacts retained in $WORK" >&2
  else
    rm -rf "$WORK"
  fi
  exit "$status"
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

PORT="$(cat "$WORK/server.port")"
URL="https://localhost:$PORT/"
export ATLAS_CHROME_PROFILE="$WORK/chromium-profile"
if [[ -n "$TRACE_FILE" ]]; then
  export ATLAS_TRACE_FILE="$TRACE_FILE"
fi
NET_LOG_ARGUMENT="--log-net-log=$WORK/netlog.json"

if [[ "$MODE" == "headless" ]]; then
  if ! "$ROOT/launch-chrome.sh" "$URL" \
      --headless \
      --dump-dom \
      "$NET_LOG_ARGUMENT" \
      >"$WORK/page.dom" 2>"$WORK/chromium.log"; then
    echo "Chromium failed while loading the HTTPS demo page." >&2
    cat "$WORK/chromium.log" >&2
    exit 1
  fi
else
  echo "Opening $URL with the verified ATLAS Chromium build."
  "$ROOT/launch-chrome.sh" "$URL" \
    "$NET_LOG_ARGUMENT" \
    2> >(tee "$WORK/chromium.log" >&2)
fi

for _ in {1..50}; do
  if ! kill -0 "$SERVER_PID" 2>/dev/null; then
    break
  fi
  sleep 0.1
done
if kill -0 "$SERVER_PID" 2>/dev/null; then
  kill "$SERVER_PID" 2>/dev/null || true
  wait "$SERVER_PID" 2>/dev/null || true
  SERVER_PID=""
  echo "The HTTPS server did not receive a complete browser request." >&2
  exit 1
fi
if ! wait "$SERVER_PID"; then
  SERVER_PID=""
  echo "The HTTPS server did not complete the browser request." >&2
  cat "$WORK/server.log" >&2
  exit 1
fi
SERVER_PID=""

if [[ "$MODE" == "headless" ]] &&
   ! grep -q "verified chromium demo" "$WORK/page.dom"; then
  echo "Chromium did not render the expected HTTPS page." >&2
  cat "$WORK/chromium.log" >&2
  exit 1
fi
if ! grep -q "ATLAS provider selected" "$WORK/chromium.log"; then
  echo "Chromium did not report selection of the ATLAS provider." >&2
  cat "$WORK/chromium.log" >&2
  exit 1
fi
if [[ "$MODE" == "headless" ]] &&
   grep "ATLAS provider selected for" "$WORK/chromium.log" |
     grep -Fv "for localhost:$PORT" >/dev/null; then
  echo "Chromium selected the TLS provider for a non-localhost connection." >&2
  cat "$WORK/chromium.log" >&2
  exit 1
fi

if [[ "$MODE" == "headless" ]]; then
  echo "ATLAS Chromium rendered the bundled HTTPS page successfully."
else
  echo "ATLAS Chromium completed the bundled HTTPS request successfully."
fi
if [[ -n "$TRACE_FILE" && -s "$TRACE_FILE" ]]; then
  "$ROOT/analyze-atlas-trace.py" "$TRACE_FILE"
fi
