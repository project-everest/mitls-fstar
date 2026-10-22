#!/usr/bin/env bash
# Extract the verified YMODEM driver loops (+ their deps) to a single C bundle.
set -e
EP=${EVERPARSE_HOME:-/home/taramana/agentic-tls/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/lib/everparse/lowparse
KRML=$EP/opt/karamel/out/bin/krml
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include spec --include impl"

MODS="YModem.Impl.Codec YModem.Impl.Client.CanonicalProtocol YModem.Impl.Client.Loop YModem.Impl.Server.Plan YModem.Impl.Server.CanonicalProtocol YModem.Impl.Server.Loop"

# Custard (F*'s whole-program extractor) extracts, from the checked files, the
# functions the C drivers in verified/ and interop/ call and everything they
# reach, into one .krml with one karamel file per F* module (--custard_split).
# Extraction is by reachability, so these roots are the whole C surface.  Custard
# takes a single file on the command line and loads the other modules on demand.
ENTRIES=""
for E in \
  YModem.Impl.Codec.ymodem_emit_data_block \
  YModem.Impl.Codec.ymodem_recv_data_block \
  YModem.Impl.Client.CanonicalProtocol.new_ymodem_client \
  YModem.Impl.Client.Loop.ymodem_client_start \
  YModem.Impl.Client.Loop.ymodem_client_run \
  YModem.Impl.Server.CanonicalProtocol.new_ymodem_server \
  YModem.Impl.Server.Loop.ymodem_server_run \
  ; do ENTRIES="$ENTRIES --custard_entry $E"; done
EXTERN_TYPES="--custard_extern_type Common.TCP.channel --custard_extern_type Common.TCP.listener"
set -- $MODS
SRC=impl/$1.fst
mkdir -p _output
$FS $F --codegen KrmlC --custard_split $ENTRIES $EXTERN_TYPES $SRC -o _output/Custard.json >/dev/null
KRMLS=_output/Custard.json

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
