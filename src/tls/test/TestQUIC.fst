module TestQUIC

// a variant of TestAPI for testing QUIC.fst

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants

open FStar.HyperStack.All
open FStar.HyperStack.ST

open QUIC

(* A flag for runtime debugging of Handshake data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("QIC| "^s^"\n"))
let print_tcp s = discard (IO.debug_print_string ("TCP| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_QUIC then print else (fun _ -> ())
unfold val trace_tcp: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace_tcp = if Flags.debug_QUIC then print_tcp else (fun _ -> ())

// auxiliary reading loop (brittle when using TCP)
private let rec recv_until c (test: QUIC.resultcode -> St bool): St bool =
  let r = recv c in
  trace (match r.code with
  | TLS_would_block -> "would block"
  | TLS_error_local -> "fatal error "^UInt16.to_string r.error
  | TLS_error_alert -> "received fatal alert "^UInt16.to_string r.error
  | TLS_client_early_data -> "client offers early data {secret0}"
  | TLS_client_complete -> "client completes {secret1}; the server is ignoring early data"
  | TLS_client_complete_with_early_data -> "client completes {secret1}: the server is reading early data"
  | TLS_server_accept -> "server accepts without early data {secret1}"
  | TLS_server_accept_with_early_data -> "server accepts with early data {secret0; secret1}"
  | TLS_server_complete -> "server completes" );
  if TLS_error_local? r.code || TLS_error_alert? r.code then false
  else if test r.code then true
  else recv_until c test

let wrap tcp: St Transport.t = // a bit dodgy; measuring flight lengths
  let n = ralloc root 0 in  // counting flight lengths
  let a = ralloc root true in // injecting WouldBlock for testing
  assume false; //17-06-30 framing...
  {
  Transport.snd = (fun x ->
    trace_tcp ("send "^string_of_int (length x)^" bytes");
    n := !n + length x;
    Platform.Tcp.send tcp x);
  Transport.rcv = (fun x ->
    let w = !n in n:= 0;
    trace_tcp ("recv"^(if w>0 then " (after sending "^string_of_int w^" bytes)" else ""));
    a := not !a;
    let r = if !a then
      Platform.Tcp.RecvWouldBlock else
      Platform.Tcp.recv_async tcp x in
    trace_tcp ("recv "^(match r with
    | Platform.Tcp.RecvWouldBlock -> "would block"
    | Platform.Tcp.Received b -> string_of_int (length b)^" bytes"
    | Platform.Tcp.RecvError s -> "error: "^s));
    r ); }

let dump c =
  trace "OK\n";
  let secret0 = FFI.ffiGetExporter c true in
  let secret1 = FFI.ffiGetExporter c false in
  (match secret0 with | Some (_, _, b) -> trace ("early secret: "^print_bytes b) | _ -> ());
  (match secret1 with | Some (_, _, b) -> trace ("exporter secret: "^print_bytes b) | _ -> ());
  trace (string_of_quicParameters (get_parameters c Client));
  trace (string_of_quicParameters (get_parameters c Server))

let ticketed c =
  match (Connection.c_cfg c).peer_name with
  | Some n -> Some? (PSK.lookup n)
  | None -> false

let client config host port offerpsk =
  trace "CLIENT";
  let tcp = Platform.Tcp.connect host port in
  Platform.Tcp.set_nonblock tcp;
  let sr = wrap tcp in
  let c = QUIC.connect sr.Transport.snd sr.Transport.rcv config offerpsk in
  if recv_until c (fun c -> TLS_client_complete? c || TLS_client_complete_with_early_data? c) then
  if recv_until c (fun r -> ticketed c) then
  dump c

let single_server config tcp : ML unit =
  let sr = wrap tcp in
  let c = QUIC.accept sr.Transport.snd sr.Transport.rcv config in
  if recv_until c (fun c -> TLS_server_complete? c) then
  if recv_until c (fun r -> true) then // ticket sending; a bit lame
  dump c

let rec aux_server config sock : ML unit =
 let client = Platform.Tcp.accept sock in
 Platform.Tcp.set_nonblock client;
 let _ = single_server config client in
 aux_server config sock

let server config host port =
 trace "SERVER";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
