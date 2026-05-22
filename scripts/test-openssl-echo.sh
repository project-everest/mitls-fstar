#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

scripts/generate-test-certs.sh test/certs >/dev/null
make test/openssl_echo_server >/dev/null

tmp_dir="$(mktemp -d test/openssl-echo.XXXXXX)"
server_pid=""
cleanup() {
  if [ -n "$server_pid" ]; then
    kill "$server_pid" 2>/dev/null || true
    wait "$server_pid" 2>/dev/null || true
  fi
  rm -rf "$tmp_dir"
}
trap cleanup EXIT

pick_port() {
  python3 - <<'PY'
import socket
s = socket.socket()
s.bind(("127.0.0.1", 0))
print(s.getsockname()[1])
s.close()
PY
}

run_case() {
  local name="$1"
  local payload="$2"
  local port log output
  port="$(pick_port)"
  log="$tmp_dir/$name.log"
  output="$tmp_dir/$name.out"

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  openssl s_client \
    -quiet \
    -connect "127.0.0.1:$port" \
    -servername localhost \
    -CAfile test/certs/ca.pem \
    -tls1_3 \
    -ciphersuites TLS_CHACHA20_POLY1305_SHA256 \
    <"$payload" >"$output" 2>>"$log"

  wait "$server_pid"
  server_pid=""

  if ! cmp -s "$payload" "$output"; then
    echo "echo mismatch for $name" >&2
    echo "server log:" >&2
    cat "$log" >&2
    exit 1
  fi
}

short_payload="$tmp_dir/short.in"
large_payload="$tmp_dir/large.in"
printf 'agentic tls echo smoke' >"$short_payload"
python3 - "$large_payload" <<'PY'
import sys
path = sys.argv[1]
pattern = b"agentic tls multi-record echo line\n"
with open(path, "wb") as f:
    while f.tell() < 40000:
        f.write(pattern)
PY

run_case short "$short_payload"
run_case large "$large_payload"

echo "OpenSSL TLS echo smoke passed"
