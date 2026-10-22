#!/usr/bin/env bash
# Extract the verified HTTP/1.1 driver loop (+ its codec deps) to a single C
# bundle, mirroring tftp_sample/extract_loops.sh.  The verified Pulse loop
# http_server_run (HTTP.Impl.Server.Loop) and the codec leaves it reuses
# (http_emit_chunk / http_emit_empty_chunk in HTTP.Impl.Codec.Chunked) lower to
# first-order C in _extract/HTTP_Verified.c — the runnable verified
# orchestration the vloop_test harness links against.
set -e
EP=${EVERPARSE_HOME:-/workspaces/agentic-tls/tools/everparse}
FS=$EP/opt/FStar/bin/fstar.exe
LP=$EP/lib/everparse/lowparse
export PATH=$EP/opt/z3:$PATH
cd "$(dirname "$0")"
F="--cache_checked_modules --cache_dir _cache --odir _output --already_cached Prims,FStar,Pulse,PulseCore,C,Spec.Loops,LowParse --warn_error -321-241-272-288 --report_assumes warn --ext optimize_let_vc --ext fly_deps --include ../common --include $LP --include spec --include impl"

MODS="HTTP.Impl.Codec.Chunked HTTP.Impl.Codec.Chunked.Stream HTTP.Impl.Loop.Chunked.Stream HTTP.Impl.Server.Loop HTTP.Impl.Client.Loop HTTP.Impl.Codec.Length HTTP.Impl.Server.Loop.Length HTTP.Impl.Client.Loop.Length HTTP.Impl.Codec.Request HTTP.Impl.Codec.Response HTTP.Impl.Client.Loop.Get HTTP.Impl.Codec.Header HTTP.Impl.Loop.Header HTTP.Impl.Codec.RequestLine HTTP.Impl.Loop.Request HTTP.Impl.Codec.RequestPost HTTP.Impl.Loop.RequestPost"

# Custard (F*'s whole-program extractor) extracts, from the checked files, the
# functions the C drivers in verified/ and interop/ call and everything they
# reach, straight to one C file (--codegen C).
# Extraction is by reachability, so these roots are the whole C surface.  Custard
# takes a single file on the command line and loads the other modules on demand.
ENTRIES=""
for E in \
  HTTP.Impl.Codec.Chunked.http_emit_chunk \
  HTTP.Impl.Codec.Chunked.http_emit_empty_chunk \
  HTTP.Impl.Codec.Chunked.http_peek_chunk_size \
  HTTP.Impl.Codec.Chunked.http_recv_chunk \
  HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks \
  HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks_var \
  HTTP.Impl.Loop.Chunked.Stream.http_server_send_stream \
  HTTP.Impl.Loop.Chunked.Stream.http_client_recv_stream \
  HTTP.Impl.Server.Loop.http_server_run \
  HTTP.Impl.Client.Loop.http_client_run \
  HTTP.Impl.Codec.Length.http_emit_body \
  HTTP.Impl.Codec.Length.http_recv_body \
  HTTP.Impl.Codec.Length.http_emit_request \
  HTTP.Impl.Codec.Length.http_emit_response \
  HTTP.Impl.Codec.Length.http_emit_response_var \
  HTTP.Impl.Codec.Length.http_recv_response \
  HTTP.Impl.Codec.Length.http_recv_request \
  HTTP.Impl.Codec.Length.http_recv_request_head \
  HTTP.Impl.Server.Loop.Length.http_server_run_length \
  HTTP.Impl.Server.Loop.Length.http_server_run_length_full \
  HTTP.Impl.Server.Loop.Length.http_server_exchange_length \
  HTTP.Impl.Server.Loop.Length.http_server_exchange_length_head \
  HTTP.Impl.Client.Loop.Length.http_client_run_length \
  HTTP.Impl.Client.Loop.Length.http_client_run_length_full \
  HTTP.Impl.Client.Loop.Length.http_client_exchange_length \
  HTTP.Impl.Codec.Request.http_emit_request_host \
  HTTP.Impl.Codec.Response.http_parse_status_line \
  HTTP.Impl.Codec.Response.parse_dec_at \
  HTTP.Impl.Codec.Response.http_parse_framing \
  HTTP.Impl.Codec.Response.http_parse_response_head \
  HTTP.Impl.Client.Loop.Get.recv_to_eof \
  HTTP.Impl.Client.Loop.Get.http_get \
  HTTP.Impl.Client.Loop.Get.http_get_body_chunked \
  HTTP.Impl.Client.Loop.Get.http_get_body_chunked_var \
  HTTP.Impl.Codec.Header.http_parse_header_field \
  HTTP.Impl.Loop.Header.http_count_headers \
  HTTP.Impl.Loop.Header.http_find_header \
  HTTP.Impl.Loop.Header.http_header_dec \
  HTTP.Impl.Loop.Header.http_parse_headers \
  HTTP.Impl.Loop.Header.http_count_header_named \
  HTTP.Impl.Loop.Header.http_request_framing_ok \
  HTTP.Impl.Loop.Header.http_header_limits_ok \
  HTTP.Impl.Loop.Header.http_connection_close \
  HTTP.Impl.Codec.RequestLine.http_parse_request_line \
  HTTP.Impl.Loop.Request.http_method_eq \
  HTTP.Impl.Loop.Request.http_request_line_ok \
  HTTP.Impl.Loop.Request.http_method_known \
  HTTP.Impl.Loop.Request.http_method_allowed \
  HTTP.Impl.Codec.RequestPost.http_emit_request_post \
  HTTP.Impl.Loop.RequestPost.http_build_post_head \
  ; do ENTRIES="$ENTRIES --custard_entry $E"; done
EXTERN_TYPES="--custard_extern_type Common.TCP.channel@common_tcp_custard.h --custard_extern_type Common.TCP.listener@common_tcp_custard.h"
# The C drivers call the roots by their unqualified names.
NO_PREFIX=""
for M in HTTP.Impl.Server.Loop HTTP.Impl.Client.Loop HTTP.Impl.Codec.Chunked HTTP.Impl.Codec.Chunked.Stream HTTP.Impl.Loop.Chunked.Stream HTTP.Impl.Server.Loop.Length HTTP.Impl.Client.Loop.Length HTTP.Impl.Codec.Length HTTP.Impl.Codec.Request HTTP.Impl.Codec.Response HTTP.Impl.Client.Loop.Get HTTP.Impl.Codec.Header HTTP.Impl.Loop.Header HTTP.Impl.Codec.RequestLine HTTP.Impl.Loop.Request HTTP.Impl.Codec.RequestPost HTTP.Impl.Loop.RequestPost; do NO_PREFIX="$NO_PREFIX --custard_c_no_prefix $M"; done
set -- $MODS
SRC=impl/$1.fst
rm -rf _extract
mkdir -p _extract
$FS $F --codegen C --custard_monomorphize_types true $ENTRIES $NO_PREFIX $EXTERN_TYPES $SRC -o _extract/HTTP_Verified.c >/dev/null
echo "=== generated ==="
ls -1 _extract/*.c _extract/*.h 2>/dev/null
