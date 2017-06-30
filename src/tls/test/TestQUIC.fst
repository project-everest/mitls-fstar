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


private let rec read c : ML QUIC.result = // auxiliary while loop for reading the full response
  match recv c with
  | TLS_would_block -> trace "blocked"; recv c
  | TLS_secret0 -> trace "secret0"; recv c
  | TLS_secret1 -> trace "secret1"; recv c
  | TLS_ticket -> trace "ticket"; recv c
//| TLS_complete -> trace "complete"
  | r -> r

let client config host port =
  trace "CLIENT"; 
  let tcp = Platform.Tcp.connect host port in 
  let request = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in 
  let send x = trace_tcp "send"; Platform.Tcp.send tcp x in
  let recv x = trace_tcp "recv"; Platform.Tcp.recv_async tcp x in
  let c = QUIC.connect send recv config in
  let _ = read c in 
  trace "OK\n"

let single_server config client : ML unit =
  let send x = trace_tcp "send"; Platform.Tcp.send client x in
  let recv x = trace_tcp "recv"; Platform.Tcp.recv_async client x in
  let c = QUIC.accept send recv config in
  let _ = read c in
  trace "OK\n"
 
let rec aux_server config sock : ML unit =
 let client = Platform.Tcp.accept sock in
 let _ = single_server config client in
 aux_server config sock

let server config host port =
 trace "SERVER";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
