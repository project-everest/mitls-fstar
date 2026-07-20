#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
output_dir="${1:-benchmark-results/profile-$timestamp}"
handshakes="${PROFILE_HANDSHAKES:-200}"
transfer_bytes="${PROFILE_BYTES:-268435456}"
message_size="${PROFILE_MESSAGE_SIZE:-16384}"
binary="test/perf/tls13_bench-gprof"

mkdir -p "$output_dir"
make -j"$(nproc)" --no-print-directory benchmark-profile-build

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "git_commit=$(git rev-parse HEAD)"
  echo "git_dirty=$(test -n "$(git status --short)" && echo yes || echo no)"
  echo "compiler=$(${CC:-cc} --version | head -1)"
  echo "profile_cflags=${BENCHMARK_PROFILE_CFLAGS:--O2 -DNDEBUG -g -pg -fno-omit-frame-pointer}"
  echo "handshakes=$handshakes"
  echo "transfer_bytes=$transfer_bytes"
  echo "message_size=$message_size"
} >"$output_dir/metadata.txt"

cases=(
  verified-client-handshake
  openssl-client-handshake
  verified-server-handshake
  openssl-server-handshake
  verified-client-send
  verified-client-receive
  verified-server-send
  verified-server-receive
)

for name in "${cases[@]}"; do
  echo "profile: $name" >&2
  prefix="$output_dir/$name.gmon.$BASHPID"
  if [[ "$name" == *-handshake ]]; then
    GMON_OUT_PREFIX="$prefix" "$binary" \
      --case "$name" --iterations "$handshakes" --warmup 10 \
      >"$output_dir/$name.csv"
  else
    GMON_OUT_PREFIX="$prefix" "$binary" \
      --case "$name" --bytes "$transfer_bytes" --size "$message_size" \
      >"$output_dir/$name.csv"
  fi
  gmon_file="$(find "$output_dir" -maxdepth 1 -name "$(basename "$prefix").*" -type f | head -1)"
  if [ -z "$gmon_file" ]; then
    echo "gprof output was not produced for $name" >&2
    exit 1
  fi
  gprof -b "$binary" "$gmon_file" >"$output_dir/$name.gprof.txt"
done

for name in verified-client-handshake verified-server-handshake \
            verified-client-send verified-client-receive \
            verified-server-send verified-server-receive; do
  echo "syscalls: $name" >&2
  for attempt in 1 2 3; do
    if [[ "$name" == *-handshake ]]; then
      GMON_OUT_PREFIX="$output_dir/$name.strace.gmon" \
      strace -c -o "$output_dir/$name.strace.txt" "$binary" \
        --case "$name" --iterations 20 --warmup 2 >/dev/null && break
    else
      GMON_OUT_PREFIX="$output_dir/$name.strace.gmon" \
      strace -c -o "$output_dir/$name.strace.txt" "$binary" \
        --case "$name" --bytes 16777216 --size "$message_size" >/dev/null && break
    fi
    if [ "$attempt" -eq 3 ]; then
      echo "strace case failed after $attempt attempts: $name" >&2
      exit 1
    fi
    sleep 1
  done
done

perf_probe="$output_dir/perf-probe.txt"
rm -f "$output_dir/perf-unavailable.txt" \
  "$output_dir/verified-client-handshake.perf-stat.txt" "$perf_probe"
if perf stat -e task-clock -o "$perf_probe" true >/dev/null 2>&1; then
  rm -f "$perf_probe"
  perf stat --no-inherit -d \
    -o "$output_dir/verified-client-handshake.perf-stat.txt" \
    "$binary" --case verified-client-handshake \
    --iterations "$handshakes" --warmup 10 >/dev/null
else
  {
    echo "perf events unavailable."
    if [ -r /proc/sys/kernel/perf_event_paranoid ]; then
      echo "perf_event_paranoid=$(cat /proc/sys/kernel/perf_event_paranoid)"
    fi
    cat "$perf_probe"
  } >"$output_dir/perf-unavailable.txt"
  rm -f "$perf_probe"
fi

python3 test/perf/profile_report.py "$output_dir"
echo "$output_dir/report.md"
