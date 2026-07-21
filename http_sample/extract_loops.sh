#!/usr/bin/env bash
# Extract the verified HTTP/1.1 driver loop (+ its codec deps) to a single C
# bundle, mirroring tftp_sample/extract_loops.sh.  The verified Pulse loop
# http_server_run (HTTP.Impl.Server.Loop) and the codec leaves it reuses
# (http_emit_chunk / http_emit_empty_chunk in HTTP.Impl.Codec.Chunked) lower to
# first-order Low* C in _extract/HTTP_Verified.c — the runnable verified
# orchestration the vloop_test harness links against.
set -e
EP=${EVERPARSE_HOME:-/workspaces/agentic-tls/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/src/lowparse
KRML=$EP/opt/FStar/karamel/out/bin/krml
export PATH=$EP/opt/z3:$PATH
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include $LP/pulse --include spec --include impl"

MODS="HTTP.Impl.Codec.Chunked HTTP.Impl.Codec.Chunked.Stream HTTP.Impl.Loop.Chunked.Stream HTTP.Impl.Server.Loop HTTP.Impl.Client.Loop HTTP.Impl.Codec.Length HTTP.Impl.Server.Loop.Length HTTP.Impl.Client.Loop.Length HTTP.Impl.Codec.Request HTTP.Impl.Codec.Response HTTP.Impl.Client.Loop.Get"

for M in $MODS; do
  KM=_output/$(echo "$M" | tr . _).krml
  case "$M" in
    HTTP.Wire.*) SRC=spec/$M.fst ;;
    *)           SRC=impl/$M.fst ;;
  esac
  $FS $F --codegen krml --extract_module "$M" --odir _output "$SRC" --krmloutput "$KM" >/dev/null 2>&1
done

KRMLS=""
for M in $MODS; do KRMLS="$KRMLS _output/$(echo "$M" | tr . _).krml"; done

rm -rf _extract
mkdir -p _extract
$KRML -tmpdir _extract -skip-compilation -warn-error -2-9-17 \
  -bundle 'HTTP.Impl.Server.Loop+HTTP.Impl.Client.Loop+HTTP.Impl.Codec.Chunked+HTTP.Impl.Codec.Chunked.Stream+HTTP.Impl.Loop.Chunked.Stream+HTTP.Impl.Server.Loop.Length+HTTP.Impl.Client.Loop.Length+HTTP.Impl.Codec.Length+HTTP.Impl.Codec.Request+HTTP.Impl.Codec.Response+HTTP.Impl.Client.Loop.Get=[rename=HTTP_Verified]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,LowParse.*,HTTP.Wire.Common,HTTP.Wire.Chunked,HTTP.Wire.Chunked.Stream,HTTP.Wire.Length,Common.StateMachine,Common.WireFormat,Common.WireFormatStateMachine,Common.FileTransfer,Common.TCP.History,Common.ProtocolEndpoint,Common.ProtocolDriver' \
  -no-prefix HTTP.Impl.Server.Loop \
  -no-prefix HTTP.Impl.Client.Loop \
  -no-prefix HTTP.Impl.Codec.Chunked \
  -no-prefix HTTP.Impl.Codec.Chunked.Stream \
  -no-prefix HTTP.Impl.Loop.Chunked.Stream \
  -no-prefix HTTP.Impl.Server.Loop.Length \
  -no-prefix HTTP.Impl.Client.Loop.Length \
  -no-prefix HTTP.Impl.Codec.Length \
  -no-prefix HTTP.Impl.Codec.Request \
  -no-prefix HTTP.Impl.Codec.Response \
  -no-prefix HTTP.Impl.Client.Loop.Get \
  $KRMLS
echo "=== generated ==="
ls -1 _extract/*.c _extract/*.h 2>/dev/null
