# TLS 1.3 performance benchmarks

The native harness compares the extracted verified client and server against an
OpenSSL/OpenSSL baseline. All cases use TLS 1.3,
`TLS_CHACHA20_POLY1305_SHA256`, X25519, RSA-PSS/SHA-256 authentication, the
same generated certificate, disabled session resumption, and loopback TCP.

On x86 builds where the compiler accepts AVX2, the harness links HACL*'s
verified SIMD256 ChaCha20-Poly1305 implementation and selects it at runtime on
AVX2-capable CPUs. Other CPUs use the scalar HACL* implementation. Set
`HACL_SIMD256=0` when invoking Make to build only the scalar fallback.

```sh
make -j"$(nproc)" benchmark-build
test/perf/tls13_bench --case verified-client-handshake \
  --iterations 100 --warmup 10

# Full repeated suite; writes CSV, host metadata, and Markdown.
make -j"$(nproc)" benchmark

# Override duration and result location.
HANDSHAKES=200 TRANSFER_BYTES=$((256 * 1024 * 1024)) REPETITIONS=5 \
  scripts/benchmark-tls13.sh benchmark-results/long-run
```

The full suite measures:

- end-to-end handshakes/second, p50/p95/p99 handshake latency, CPU time,
  scheduler activity, faults, and peak RSS for each verified role and its
  OpenSSL baseline;
- RSS scaling after 10, 100, and 500 sequential handshakes to expose
  connection-lifecycle retention;
- send and receive application-data throughput at 64-byte, 1-KiB, and 16-KiB
  record sizes, including records/second and CPU cost per record. A process-local
  synchronization channel excludes peer startup from transfer timing, and every
  received plaintext byte is checked against the expected payload.

Handshake throughput includes connection setup and teardown through each public
API. OpenSSL reuses `SSL_CTX`, as a conventional production implementation
does. The current verified server API creates a listener and parses its
certificate and private key for every accepted connection, so this benchmark
intentionally exposes that lifecycle cost.

## Profiling

```sh
make -j"$(nproc)" profile
# or:
PROFILE_HANDSHAKES=500 PROFILE_BYTES=$((512 * 1024 * 1024)) \
  scripts/profile-tls13.sh benchmark-results/profile
```

Profiling rebuilds all extracted and wrapper code with `-pg -g`, writes a
per-case gprof call-graph/flat profile, a Markdown bottleneck report, and
syscall summaries with `strace -c`. It also records `perf stat -d` counters
when the host permits unprivileged perf events. The measured endpoint remains
in the parent process; the forked OpenSSL peer exits with `_exit`, so its
samples do not contaminate the gprof data.

Run on an otherwise idle, fixed-frequency host for stable numbers. Pin the
process to a pair of physical cores with `taskset` when comparing commits. For
production capacity planning, add concurrency scaling, session resumption and
0-RTT, AES-GCM on AES-capable hosts, multiple certificate/key types, network
RTT/loss, key updates, allocation counts, and sustained multi-connection RSS.
