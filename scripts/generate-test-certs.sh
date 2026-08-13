#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dest_dir="${1:-"$repo_root/test/certs"}"

mkdir -p "$dest_dir"

openssl req -x509 -newkey rsa:2048 -nodes -days 30 \
  -subj "/CN=agentic-tls test CA" \
  -keyout "$dest_dir/ca.key" \
  -out "$dest_dir/ca.pem" \
  >/dev/null 2>&1

cat > "$dest_dir/leaf.ext" <<'EOF'
basicConstraints = CA:FALSE
keyUsage = digitalSignature, keyEncipherment
extendedKeyUsage = serverAuth
subjectAltName = DNS:localhost,IP:127.0.0.1
EOF

openssl req -newkey rsa:2048 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/leaf.key" \
  -out "$dest_dir/leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/leaf.csr" \
  -CA "$dest_dir/ca.pem" \
  -CAkey "$dest_dir/ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/leaf.pem" \
  >/dev/null 2>&1

openssl x509 -in "$dest_dir/leaf.pem" -outform DER -out "$dest_dir/leaf.der" >/dev/null 2>&1

cat "$dest_dir/leaf.pem" > "$dest_dir/chain.pem"

# Parity gap G5: an ECDSA P-256 leaf, issued by the same test CA, so the
# verified server can be exercised with a non-RSA credential.
openssl req -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -subj "/CN=localhost" \
  -keyout "$dest_dir/ec-leaf.key" \
  -out "$dest_dir/ec-leaf.csr" \
  >/dev/null 2>&1

openssl x509 -req -days 30 \
  -in "$dest_dir/ec-leaf.csr" \
  -CA "$dest_dir/ca.pem" \
  -CAkey "$dest_dir/ca.key" \
  -CAcreateserial \
  -extfile "$dest_dir/leaf.ext" \
  -out "$dest_dir/ec-leaf.pem" \
  >/dev/null 2>&1

openssl x509 -in "$dest_dir/ec-leaf.pem" -outform DER \
  -out "$dest_dir/ec-leaf.der" >/dev/null 2>&1

cat "$dest_dir/ec-leaf.pem" > "$dest_dir/ec-chain.pem"

echo "Generated test certificates in $dest_dir"
