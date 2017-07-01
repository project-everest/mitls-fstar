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
private let rec recv_until c p: ML unit = 
  let r = recv c in
  trace (match r with
  | TLS_would_block -> "would block"
  | TLS_error_local e -> "fatal error "^print_bytes e
  | TLS_error_alert e -> "received fatal alert "^print_bytes e
  | TLS_client_early -> "client offers early data {secret0}"
  | TLS_client_complete b -> "client completes {secret1}: the server "^(if b then "receives" else "ignores")^" early data"
  | TLS_server_accept true -> "server accepts with early data {secret0, secret1}"
  | TLS_server_accept false -> "server accepts without early data {secret1}"
  | TLS_server_complete -> "server completes" );
  if p r then () else recv_until c p
  

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
    a := not !a; if !a then Platform.Tcp.RecvWouldBlock else 
    Platform.Tcp.recv_async tcp x); }

let dump c = 
  trace "OK\n";
  let secret0 = get_exporter c false in
  let secret1 = get_exporter c true in
  if Some? secret0 then trace ("early secret: "^print_bytes (Some?.v secret0));
  if Some? secret1 then trace ("main secret:  "^print_bytes (Some?.v secret1));
  trace (string_of_quicParameters (get_parameters c Client));
  trace (string_of_quicParameters (get_parameters c Server))
 
let client config host port offerpsk =
  trace "CLIENT"; 
  let tcp = Platform.Tcp.connect host port in 
  let request = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in 
  let sr = wrap tcp in
  let c = QUIC.connect sr.Transport.snd sr.Transport.rcv config offerpsk in 

  // brittle, as we need to read the ticket without blocking on TCP read.
  recv_until c TLS_client_complete? ; 
  recv_until c TLS_would_block? ; // ticket sending
  recv_until c TLS_would_block? ;
  recv_until c TLS_would_block? ;
  dump c

let single_server config tcp : ML unit =
  let sr = wrap tcp in
  let c = QUIC.accept sr.Transport.snd sr.Transport.rcv config in

  // brittle, as we need to write the ticket without blocking on TCP read.
  recv_until c TLS_server_complete? ;
  recv_until c TLS_would_block? ;  // ticket sending 
  dump c
 
let rec aux_server config sock : ML unit =
 let client = Platform.Tcp.accept sock in
 let _ = single_server config client in
 aux_server config sock

let server config host port =
 trace "SERVER";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
