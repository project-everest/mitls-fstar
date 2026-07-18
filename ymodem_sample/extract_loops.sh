#!/usr/bin/env bash
# Extract the verified YMODEM driver loops (+ their deps) to a single C bundle.
set -e
EP=${EVERPARSE_HOME:-/home/taramana/agentic-tls/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/src/lowparse
KRML=$EP/opt/karamel/out/bin/krml
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include $LP/pulse --include spec --include impl"

MODS="YModem.Impl.Codec YModem.Impl.Client.CanonicalProtocol YModem.Impl.Client.Loop YModem.Impl.Server.Plan YModem.Impl.Server.CanonicalProtocol YModem.Impl.Server.Loop Common.ProtocolImplementation"

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
  -bundle 'YModem.Impl.Client.Loop+YModem.Impl.Client.CanonicalProtocol+YModem.Impl.Server.Loop+YModem.Impl.Server.CanonicalProtocol+YModem.Impl.Codec=[rename=YModem_Verified]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,LowParse.*,Common.StateMachine,Common.WireFormat,Common.WireFormatStateMachine,Common.FileTransfer,Common.TCP.History,Common.ProtocolEndpoint,Common.ProtocolDriver' \
  -no-prefix YModem.Impl.Client.Loop \
  -no-prefix YModem.Impl.Client.CanonicalProtocol \
  -no-prefix YModem.Impl.Server.Loop \
  -no-prefix YModem.Impl.Server.CanonicalProtocol \
  -no-prefix YModem.Impl.Codec \
  $KRMLS
echo "=== generated ==="
ls -1 _extract/*.c _extract/*.h 2>/dev/null
