#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

scripts/generate-test-certs.sh test/certs >/dev/null
make test/openssl_echo_server >/dev/null

port="$(python3 - <<'PY'
import socket
s = socket.socket()
s.bind(("127.0.0.1", 0))
print(s.getsockname()[1])
s.close()
PY
)"

log="test/openssl_echo_server.log"
rm -f "$log"
test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
server_pid=$!
trap 'kill "$server_pid" 2>/dev/null || true; wait "$server_pid" 2>/dev/null || true' EXIT

for _ in $(seq 1 50); do
  if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
    break
  fi
  sleep 0.1
done

msg="agentic tls echo smoke"
out="$(printf '%s' "$msg" | openssl s_client \
  -quiet \
  -connect "127.0.0.1:$port" \
  -servername localhost \
  -CAfile test/certs/ca.pem \
  -tls1_3 \
  -ciphersuites TLS_CHACHA20_POLY1305_SHA256 \
  2>>"$log")"

wait "$server_pid"
trap - EXIT

if [ "$out" != "$msg" ]; then
  echo "echo mismatch" >&2
  echo "expected: $msg" >&2
  echo "actual:   $out" >&2
  echo "server log:" >&2
  cat "$log" >&2
  exit 1
fi

echo "OpenSSL TLS echo smoke passed"

