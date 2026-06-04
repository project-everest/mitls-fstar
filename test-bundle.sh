#!/bin/bash
set -euo pipefail

# Historical helper retained for people who remember ./test-bundle.sh.
# The active extraction path is the Makefile bundle for TLS13.Impl.Client.

make extract-bundle

echo ""
echo "=== Generated bundle files ==="
ls -lh _extract/bundle/TLS13_*.c _extract/bundle/TLS13_*.h 2>/dev/null || true

echo ""
echo "=== Public client API in TLS13_Impl_Client.h ==="
grep "^[a-zA-Z_].*client_" _extract/bundle/TLS13_Impl_Client.h || true
