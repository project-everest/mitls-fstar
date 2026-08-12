#!/usr/bin/env bash
# Run the ATLAS interop harness against every host in a catalog.
#
#   usage: test/interop/sweep.sh [catalog.tsv] [out.tsv] [parallelism]
#
# Requires `make interop-client` to have built test/test_interop_client, and
# outbound network access on port 443.  Per-host trust anchors are extracted
# on demand into test/interop/roots/ by host_root.py, because ATLAS's trust
# store is capped at Bounds.max_trust_anchors_len (65535 bytes), well below
# the ~182 KB system bundle.
set -u

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
CAT="${1:-$REPO/test/interop/top100.tsv}"
OUT="${2:-$REPO/test/interop/sweep.tsv}"
PAR="${3:-12}"

export HARNESS="$REPO/test/test_interop_client"
export ROOTS="$REPO/test/interop/roots"
export HOST_ROOT="$REPO/test/interop/host_root.py"

if [ ! -x "$HARNESS" ]; then
  echo "missing $HARNESS -- run 'make interop-client' first" >&2
  exit 1
fi
mkdir -p "$ROOTS"

run_one() {
  local rank="$1" host="$2" connect_host="$3"
  local ca="$ROOTS/$connect_host.pem"
  if [ ! -s "$ca" ]; then
    python3 "$HOST_ROOT" "$connect_host" "$ca" >/dev/null 2>&1
  fi
  if [ ! -s "$ca" ]; then
    printf '%s\t%s\t%s\tNOANCHOR\tno system root anchors this host under the ATLAS offer\n' \
      "$rank" "$host" "$connect_host"
    return
  fi
  local line
  line=$(timeout 30 "$HARNESS" "$connect_host" "$ca" 443 2>/dev/null \
           | grep '^RESULT' | head -1)
  if [ -z "$line" ]; then
    printf '%s\t%s\t%s\tCRASH\tno RESULT line\n' "$rank" "$host" "$connect_host"
    return
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$rank" "$host" "$connect_host" \
    "$(printf '%s' "$line" | cut -f3)" "$(printf '%s' "$line" | cut -f4)"
}
export -f run_one

grep -v '^#' "$CAT" | tr -d '\r' | \
  xargs -P "$PAR" -L1 bash -c 'run_one "$@"' _ > "$OUT"
sort -n -k1,1 -o "$OUT" "$OUT"
echo "wrote $OUT"
cut -f4 "$OUT" | sort | uniq -c | sort -rn
