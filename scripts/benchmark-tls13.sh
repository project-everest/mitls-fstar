#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
output_dir="${1:-benchmark-results/$timestamp}"
iterations="${HANDSHAKES:-50}"
warmup="${WARMUP_HANDSHAKES:-5}"
transfer_bytes="${TRANSFER_BYTES:-67108864}"
repetitions="${REPETITIONS:-3}"
sizes="${MESSAGE_SIZES:-64 1024 16384}"
memory_handshakes="${MEMORY_HANDSHAKE_COUNTS:-10 100 500}"
binary="test/perf/tls13_bench"

mkdir -p "$output_dir"
make -j"$(nproc)" --no-print-directory benchmark-build

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "git_commit=$(git rev-parse HEAD)"
  echo "git_dirty=$(test -n "$(git status --short)" && echo yes || echo no)"
  echo "compiler=$(${CC:-cc} --version | head -1)"
  echo "openssl=$(openssl version)"
  echo "kernel=$(uname -srmo)"
  echo "benchmark_cflags=${BENCHMARK_CFLAGS:--O3 -DNDEBUG -g -fno-omit-frame-pointer}"
  echo "hacl_simd256=${HACL_SIMD256:-auto-runtime-dispatch}"
  lscpu | grep -E '^(Architecture|CPU\(s\)|Model name|Thread|Core|Socket|CPU max MHz|L1d cache|L1i cache|L2 cache|L3 cache):'
  size "$binary"
} >"$output_dir/system.txt"

results="$output_dir/results.csv"
: >"$results"
first=1
run_case() {
  local trial="$1"
  local name="$2"
  shift 2
  local temporary
  temporary="$(mktemp "$output_dir/.result.XXXXXX")"
  "$binary" --case "$name" --trial "$trial" "$@" >"$temporary"
  if [ "$first" -eq 1 ]; then
    cat "$temporary" >>"$results"
    first=0
  else
    tail -n +2 "$temporary" >>"$results"
  fi
  rm -f "$temporary"
}

handshake_cases=(
  verified-client-handshake
  openssl-client-handshake
  verified-server-handshake
  openssl-server-handshake
)
transfer_cases=(
  verified-client-send
  verified-client-receive
  verified-server-send
  verified-server-receive
  openssl-client-send
  openssl-client-receive
  openssl-server-send
  openssl-server-receive
)

for trial in $(seq 1 "$repetitions"); do
  for name in "${handshake_cases[@]}"; do
    echo "benchmark: trial=$trial case=$name" >&2
    run_case "$trial" "$name" --iterations "$iterations" --warmup "$warmup"
  done
  for size in $sizes; do
    for name in "${transfer_cases[@]}"; do
      echo "benchmark: trial=$trial case=$name size=$size" >&2
      run_case "$trial" "$name" --bytes "$transfer_bytes" --size "$size"
    done
  done
done

memory_results="$output_dir/memory.csv"
: >"$memory_results"
memory_first=1
for name in "${handshake_cases[@]}"; do
  for count in $memory_handshakes; do
    echo "memory: case=$name handshakes=$count" >&2
    temporary="$(mktemp "$output_dir/.memory.XXXXXX")"
    "$binary" --case "$name" --iterations "$count" --warmup 2 >"$temporary"
    if [ "$memory_first" -eq 1 ]; then
      cat "$temporary" >>"$memory_results"
      memory_first=0
    else
      tail -n +2 "$temporary" >>"$memory_results"
    fi
    rm -f "$temporary"
  done
done

python3 test/perf/report.py \
  "$results" "$output_dir/system.txt" "$output_dir/report.md" "$memory_results"
echo "$output_dir/report.md"
