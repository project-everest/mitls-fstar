module TestFFI

// a variant of TestAPI for testing FFI.fst

open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants

open Mem

open FFI

(* A flag for runtime debugging of Handshake data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)

inline_for_extraction let ffi_debug = true
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("FFI| "^s^"\n"))
let print_tcp s = discard (IO.debug_print_string ("TCP| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if ffi_debug then print else (fun _ -> ())
unfold val trace_tcp: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace_tcp = if ffi_debug then print_tcp else (fun _ -> ())


private let rec readAll c : ML unit = // auxiliary while loop for reading the full response
  match read c with
  | Received extra -> trace ("Received data:\n"^iutf8 extra); readAll c
  | Errno 0        -> trace "Received close_notify! Socket closed"
  | Errno e        -> trace "Improperly closed connection"


let client config host port =
  trace "===============================================";
  trace "Starting test client..."; (
  let tcp = Platform.Tcp.connect host port in 
  let request = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in 
  let send x = trace_tcp "send"; Platform.Tcp.send tcp x in
  let recv x = trace_tcp "recv"; Platform.Tcp.recv_async tcp x in
  match connect send recv config with 
  | c, 0 -> (
    trace "Read OK, sending HTTP request..."; (
    match write c (utf8 request) with
    | 0 -> (
      match read c with
      | Received response -> (
        trace ("Received data:\n"^iutf8 response);
        trace "Closing connection, irrespective of the response";
        match close c with 
        | 0 -> trace "Sent close_notify, will block waiting for the server's"; readAll c
        | _ -> trace "close error")
      | Errno _ -> trace "read error")  
    | _  -> trace "write error"))
  | _, err  -> trace "connect error" )

//let aux_server config client : ML unit = pr ("Success")
let single_server config client : ML unit =
  let send x = trace_tcp "send"; Platform.Tcp.send client x in
  let recv x = trace_tcp "recv"; Platform.Tcp.recv_async client x in
  match FFI.accept_connected send recv config with
  | c, 0 ->
    begin
    match FFI.read c with
    | Received db ->
      begin
      trace ("Received data: "^(iutf8 db));
      let text = "You are connected to miTLS*!\r\n"
        ^ "This is the request you sent:\r\n\r\n" ^ (iutf8 db) in
      let payload = utf8 ("HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:"
        ^ (string_of_int (length (abytes text))) 
        ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text) in
      match FFI.write c payload with
      | 0 -> 
        begin
        match FFI.read c with
        | Errno 0 -> trace "received close_notify! Closing socket.\n"
        | _ -> trace "improperly closed connection\n"
        end
      | _ -> trace "failed to write HTTP response"
      end
    | _ -> trace "unexpected FFI.read result"
    end
  | _ -> trace "accept_connected error"
 
let rec aux_server config sock : ML unit =
 let client = Platform.Tcp.accept sock in
 let _ = single_server config client in
 aux_server config sock


let server config host port =
 trace "===============================================\n Starting test TLS server...\n";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
