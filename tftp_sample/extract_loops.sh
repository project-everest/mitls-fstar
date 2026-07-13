#!/usr/bin/env bash
# Extract the verified TFTP driver loops (+ their deps) to a single C bundle,
# mirroring ymodem_sample/extract_loops.sh.  The verified Pulse loops
# tftp_client_run / tftp_server_run (and the leaves they reuse: the codec, the
# CanonicalProtocol process_network/process_local, the handle allocators) lower
# to first-order Low* C in _extract/TFTP_Verified.c — the runnable verified
# orchestration the vloop_test harness links against.
set -e
EP=${EVERPARSE_HOME:-/workspaces/agentic-tls/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/src/lowparse
KRML=$EP/opt/FStar/karamel/out/bin/krml
export PATH=$EP/opt/z3:$PATH
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include $LP/pulse --include spec --include impl"

MODS="TFTP.Impl.Codec TFTP.Impl.Client.CanonicalProtocol TFTP.Impl.Client.Loop TFTP.Impl.Server.Plan TFTP.Impl.Server.CanonicalProtocol TFTP.Impl.Server.Loop Common.ProtocolImplementation"

for M in $MODS; do
  KM=_output/$(echo "$M" | tr . _).krml
  case "$M" in
    Common.ProtocolImplementation) SRC=../common/Common.ProtocolImplementation.fst ;;
    *) SRC=impl/$M.fst ;;
  esac
  $FS $F --codegen krml --extract_module "$M" --odir _output "$SRC" --krmloutput "$KM" >/dev/null 2>&1
done

KRMLS=""
for M in $MODS; do KRMLS="$KRMLS _output/$(echo "$M" | tr . _).krml"; done

rm -rf _extract
mkdir -p _extract
$KRML -tmpdir _extract -skip-compilation -warn-error -2-9-17 \
  -bundle 'TFTP.Impl.Client.Loop+TFTP.Impl.Client.CanonicalProtocol+TFTP.Impl.Server.Loop+TFTP.Impl.Server.CanonicalProtocol+TFTP.Impl.Codec=[rename=TFTP_Verified]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,LowParse.*,Common.StateMachine,Common.WireFormat,Common.WireFormatStateMachine,Common.FileTransfer,Common.TCP.History,Common.ProtocolEndpoint,Common.ProtocolDriver' \
  -no-prefix TFTP.Impl.Client.Loop \
  -no-prefix TFTP.Impl.Client.CanonicalProtocol \
  -no-prefix TFTP.Impl.Server.Loop \
  -no-prefix TFTP.Impl.Server.CanonicalProtocol \
  -no-prefix TFTP.Impl.Codec \
  $KRMLS
echo "=== generated ==="
ls -1 _extract/*.c _extract/*.h 2>/dev/null
