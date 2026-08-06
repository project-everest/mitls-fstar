#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PORT_FILE="${1:?usage: start-server.sh PORT_FILE}"

exec "$ROOT/server/openssl_http_server" \
  0 "$ROOT/server/chain.pem" "$ROOT/server/leaf.key" "$PORT_FILE"
