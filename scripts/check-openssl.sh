#!/usr/bin/env bash
set -euo pipefail

if ! command -v openssl >/dev/null 2>&1; then
  echo "openssl executable not found" >&2
  exit 1
fi

openssl version

if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists openssl; then
  pkg-config --modversion openssl
  cflags="$(pkg-config --cflags openssl)"
  libs="$(pkg-config --libs openssl)"
  echo "$cflags $libs"
else
  cflags=""
  libs="-lssl -lcrypto"
fi

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

cat > "$tmp_dir/check_openssl.c" <<'C'
#include <openssl/ssl.h>
#include <openssl/x509.h>

#if OPENSSL_VERSION_MAJOR < 3
#error "OpenSSL 3.x or newer is required"
#endif

int main(void) {
  SSL_library_init();
  return X509_V_OK == 0 ? 0 : 0;
}
C

cc $cflags "$tmp_dir/check_openssl.c" -o "$tmp_dir/check_openssl" $libs
echo "OpenSSL 3.x headers and libraries are available"
