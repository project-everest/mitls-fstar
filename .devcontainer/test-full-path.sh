#!/usr/bin/env bash
# Exercise the full agentic-tls pipeline end to end, the way the dev container is
# meant to be validated:
#
#   1. QuackyDucky generation     - regenerate generated/TLS13.Wire.Generated.*
#   2. generated verification     - F* verify of the generated parsers/serializers
#   3. generated extraction       - KaRaMeL extract parsers/serializers to C
#   4. agentic-tls verification   - F* verify of the spec + impl development
#   5. extraction + interop test  - extract the client driver and run the OpenSSL
#                                   echo round-trip
#
# Assumes ./setup.sh has already built the toolchain into tools/everparse and
# fetched dependencies (the dev container's onCreateCommand does this).
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

jobs="${JOBS:-$(nproc 2>/dev/null || echo 4)}"

echo "==> [1-3] QuackyDucky generation + verification + extraction (make parsers)"
make -j"$jobs" parsers

echo "==> [4] agentic-tls verification (make verify)"
make -j"$jobs" verify

echo "==> [5] extraction + OpenSSL interop (make test-openssl-echo)"
make test-openssl-echo

echo "==> full pipeline succeeded"
