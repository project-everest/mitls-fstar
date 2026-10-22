#!/bin/bash
set -euo pipefail

# Historical helper retained for people who remember ./test-bundle.sh.
# The active extraction path is the unified client/server TLS13 unit, extracted
# directly to C by Custard.

make extract-tls13-bundle

echo ""
echo "=== Generated bundle files ==="
ls -lh _extract/tls13_c/TLS13.c _extract/tls13_c/TLS13.h 2>/dev/null || true

echo ""
echo "=== Public client driver API ==="
grep " TLS13_Impl_Client_Driver_\\(new_client\\|connect\\|send\\|receive\\|close\\)(" \
  _extract/tls13_c/TLS13.h || true

echo ""
echo "=== Public server driver API ==="
grep " TLS13_Impl_Server_Driver_\\(new_server\\|accept\\|send\\|receive\\|close\\)(" \
  _extract/tls13_c/TLS13.h || true
