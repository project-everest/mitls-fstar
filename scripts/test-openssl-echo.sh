#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

scripts/generate-test-certs.sh test/certs >/dev/null
make test/openssl_echo_server >/dev/null
make test/test_clienthello_openssl_probe >/dev/null
make test/test_extracted_connection_driver_openssl >/dev/null
make test/test_extracted_connection_wrapper_openssl >/dev/null

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

run_probe() {
  local port log
  port="$(pick_port)"
  log="$tmp_dir/clienthello-probe.log"

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if ! test/test_clienthello_openssl_probe 127.0.0.1 "$port" test/certs/ca.pem >>"$log" 2>&1; then
    echo "ClientHello/OpenSSL handshake probe failed" >&2
    echo "server/probe log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
}

run_probe_rejects_wrong_ca() {
  local port log wrong_certs
  port="$(pick_port)"
  log="$tmp_dir/clienthello-probe-wrong-ca.log"
  wrong_certs="$tmp_dir/wrong-certs"
  scripts/generate-test-certs.sh "$wrong_certs" >/dev/null

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if test/test_clienthello_openssl_probe 127.0.0.1 "$port" "$wrong_certs/ca.pem" >>"$log" 2>&1; then
    echo "ClientHello/OpenSSL probe unexpectedly accepted wrong CA" >&2
    echo "server/probe log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
}

run_extracted_driver() {
  local port log
  port="$(pick_port)"
  log="$tmp_dir/extracted-driver.log"

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if ! test/test_extracted_connection_driver_openssl 127.0.0.1 "$port" test/certs/ca.pem >>"$log" 2>&1; then
    echo "extracted connection driver OpenSSL echo failed" >&2
    echo "server/driver log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
}

run_extracted_driver_rejects_wrong_ca() {
  local port log wrong_certs
  port="$(pick_port)"
  log="$tmp_dir/extracted-driver-wrong-ca.log"
  wrong_certs="$tmp_dir/extracted-driver-wrong-certs"
  scripts/generate-test-certs.sh "$wrong_certs" >/dev/null

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if test/test_extracted_connection_driver_openssl 127.0.0.1 "$port" "$wrong_certs/ca.pem" >>"$log" 2>&1; then
    echo "extracted connection driver unexpectedly accepted wrong CA" >&2
    echo "server/driver log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
}

run_extracted_wrapper() {
  local port log
  port="$(pick_port)"
  log="$tmp_dir/extracted-wrapper.log"

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if ! test/test_extracted_connection_wrapper_openssl 127.0.0.1 "$port" test/certs/ca.pem >>"$log" 2>&1; then
    echo "extracted connection wrapper OpenSSL echo failed" >&2
    echo "server/wrapper log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
}

run_extracted_wrapper_rejects_wrong_ca() {
  local port log wrong_certs
  port="$(pick_port)"
  log="$tmp_dir/extracted-wrapper-wrong-ca.log"
  wrong_certs="$tmp_dir/extracted-wrapper-wrong-certs"
  scripts/generate-test-certs.sh "$wrong_certs" >/dev/null

  test/openssl_echo_server "$port" test/certs/leaf.pem test/certs/leaf.key >"$log" 2>&1 &
  server_pid=$!

  for _ in $(seq 1 50); do
    if grep -q "^[0-9][0-9]*$" "$log" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  if test/test_extracted_connection_wrapper_openssl 127.0.0.1 "$port" "$wrong_certs/ca.pem" >>"$log" 2>&1; then
    echo "extracted connection wrapper unexpectedly accepted wrong CA" >&2
    echo "server/wrapper log:" >&2
    cat "$log" >&2
    exit 1
  fi

  kill "$server_pid" 2>/dev/null || true
  wait "$server_pid" 2>/dev/null || true
  server_pid=""
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

run_probe
run_probe_rejects_wrong_ca
run_extracted_driver
run_extracted_driver_rejects_wrong_ca
run_extracted_wrapper
run_extracted_wrapper_rejects_wrong_ca
run_case short "$short_payload"
run_case large "$large_payload"

echo "OpenSSL TLS echo smoke passed"
