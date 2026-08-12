#!/usr/bin/env bash
# Reference oracle for the interop sweep.
#
#   usage: test/interop/oracle.sh [catalog.tsv] [out.tsv] [parallelism]
#
# Reports what an *unverified* TLS 1.3 client (OpenSSL) constrained to exactly
# ATLAS's offer -- X25519, {TLS_CHACHA20_POLY1305_SHA256, TLS_AES_128_GCM_SHA256}, and
# {rsa_pss_rsae_sha256, ecdsa_secp256r1_sha256} -- achieves against each host,
# with hostname verification enabled.
#
# This is the honest upper bound for the ATLAS sweep: a host that OpenSSL
# cannot reach under this offer is not an ATLAS defect, it needs a larger
# cipher/group/signature offer.  Keep the flags below in sync with
# `default_connection_config` in TLS13.Impl.ConnectionState.Repr.fsti.
set -u

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
CAT="${1:-$REPO/test/interop/top100.tsv}"
OUT="${2:-$REPO/test/interop/oracle.tsv}"
PAR="${3:-16}"

run_one() {
  local rank="$1" host="$2" connect_host="$3"
  local out rc detail
  out=$(timeout 25 openssl s_client -connect "$connect_host:443" \
          -servername "$connect_host" -tls1_3 -groups X25519 \
          -ciphersuites TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256 \
          -sigalgs rsa_pss_rsae_sha256:ecdsa_secp256r1_sha256 \
          -verify_hostname "$connect_host" -verify_return_error \
          </dev/null 2>&1)
  rc=$?
  if [ $rc -ne 0 ]; then
    detail=$(printf '%s' "$out" | grep -oE "(hostname mismatch|no peer certificate available|unable to get local issuer certificate|certificate has expired|self.signed certificate[a-z ]*|write:errno=[0-9]+|alert [a-z ]+|sslv3 alert [a-z ]+|handshake failure|Connection refused|no protocols available)" | head -1)
    [ -z "$detail" ] && detail="handshake failed"
    printf '%s\t%s\t%s\tFAIL\t%s\n' "$rank" "$host" "$connect_host" "$detail"
    return
  fi
  printf '%s\t%s\t%s\tOK\t-\n' "$rank" "$host" "$connect_host"
}
export -f run_one

grep -v '^#' "$CAT" | tr -d '\r' | \
  xargs -P "$PAR" -L1 bash -c 'run_one "$@"' _ > "$OUT"
sort -n -k1,1 -o "$OUT" "$OUT"
echo "wrote $OUT"
cut -f4 "$OUT" | sort | uniq -c | sort -rn
