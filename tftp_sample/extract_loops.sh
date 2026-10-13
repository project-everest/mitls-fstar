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
KRML=$EP/opt/karamel/out/bin/krml
export PATH=$EP/opt/z3:$PATH
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include $LP/pulse --include spec --include impl"

MODS="TFTP.Impl.Codec TFTP.Impl.Client.CanonicalProtocol TFTP.Impl.Client.Loop TFTP.Impl.Server.Plan TFTP.Impl.Server.CanonicalProtocol TFTP.Impl.Server.Loop"

# Custard (F*'s whole-program extractor) extracts, from the checked files, the
# functions the C drivers in verified/ and interop/ call and everything they
# reach, into one .krml with one karamel file per F* module (--custard_split).
# Extraction is by reachability, so these roots are the whole C surface.  Custard
# takes a single file on the command line and loads the other modules on demand.
ENTRIES=""
for E in \
  TFTP.Impl.Client.CanonicalProtocol.new_tftp_client \
  TFTP.Impl.Client.Loop.tftp_client_start \
  TFTP.Impl.Client.Loop.tftp_client_run \
  TFTP.Impl.Server.CanonicalProtocol.new_tftp_server \
  TFTP.Impl.Server.Loop.tftp_server_run \
  ; do ENTRIES="$ENTRIES --custard_entry $E"; done
EXTERN_TYPES="--custard_extern_type Common.TCP.channel --custard_extern_type Common.TCP.listener"
set -- $MODS
SRC=impl/$1.fst
mkdir -p _output
$FS $F --codegen KrmlC --custard_split $ENTRIES $EXTERN_TYPES $SRC -o _output/Custard.krml >/dev/null
KRMLS=_output/Custard.krml

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
