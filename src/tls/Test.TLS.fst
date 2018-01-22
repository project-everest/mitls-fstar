module Test.TLS 
//18-01-20 adapted from test/TestAPI

open FStar.Seq
open FStar.HyperStack
open FStar.Error
open TLSError
open TLSInfo
open TLSConstants

module TLS = TLS
module Range = Range

inline_for_extraction let api_debug = true
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("API| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if api_debug then print else (fun _ -> ())

// unit test for Transport (just plain TCP)

private let rec tcp_read_loop tcp: St unit = 
  match Transport.recv tcp (*maxlen:*) 5 with 
  | FStar.Tcp.RecvWouldBlock -> trace "wouldBlock"; tcp_read_loop tcp 
  | FStar.Tcp.RecvError e -> trace ("read error: "^e)
  | FStar.Tcp.Received fresh -> trace ("received: "^Bytes.print_bytes fresh);  tcp_read_loop tcp 

let tcp_client host port: St unit = 
  trace "tcp client"; 
  let tcp = Transport.connect host port in
  let b = Bytes.utf8_encode "not much" in
  match Transport.send tcp b with 
  | Error s -> trace ("send error: "^s)
  | Correct _ -> trace ("sent: "^Bytes.print_bytes b) 
  
let tcp_server host port: St unit = 
  trace "tcp server";
  let listener = Tcp.listen host port in
  let tcp = Transport.accept listener in 
  tcp_read_loop tcp 

open TLS 

// a permissive client loop (not checking the TLS state machine)
let rec client_read con host: ML unit =
  let r = TLS.currentId con Reader in
  match TLS.read con r with
  | Update true -> // aggressively using 0RTT
    trace "sending 0-RTT request";
    let payload = Bytes.utf8_encode ("GET /0rtt HTTP/1.0\r\nConnection: keep-alive\r\nHost: "^host^"\r\n\r\n") in
    let id = TLS.currentId con Writer in
    let rg : Range.frange id = Range.point (Bytes.length payload) in
    let f = DataStream.appFragment id rg payload in
    (match TLS.write con f with
    | Written -> client_read con host
    | WriteError _ t -> trace ("Write error:"^t)
    | _ -> trace "unexpected ioresult_w")
  | Complete ->
    trace "read OK, sending HTTP request";
    let payload = Bytes.utf8_encode ("GET / HTTP/1.0\r\nConnection: close\r\nHost: " ^ host ^ "\r\n\r\n") in
    let id = TLS.currentId con Writer in
    let rg : Range.frange id = Range.point (Bytes.length payload) in
    let f = DataStream.appFragment id rg payload in
    (match TLS.write con f with
    | Written -> client_read con host
    | WriteError _ t -> trace ("Write error:"^t)
    | _ -> trace "unexpected ioresult_w")
  | Read (DataStream.Data d) ->
    let db = DataStream.appBytes d in
    let Some txt = Bytes.iutf8_opt db in 
    trace ("received data: "^txt);
    client_read con host
  | ReadError _ t ->
    trace ("ReadError: "^t)
  | Read (DataStream.Close) ->
    trace "got close_notify, clean closure.\n"
  | Read (DataStream.Alert a)->
    trace ("Got alert: "^string_of_ad a);
    trace "closing connection.\n";
    let _ = TLS.writeCloseNotify con in
    ()
  | other -> trace ("unexpected read result: "^string_of_ioresult_i #r other)

let client config host port offerticket offerpsk =
  trace "*** Starting miTLS client...";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let con = TLS.resume rid tcp config offerticket offerpsk in
  client_read con host

private let rec server_read con: ML unit =
    // a somewhat generic server loop, with synchronous writing in-between reads.
    let id = TLS.currentId con Reader in
    let r = TLS.read con id in
    trace (TLS.string_of_ioresult_i r);
    match r with
    | Complete -> trace "connection complete"; server_read con
    | Update false -> trace "connection still in handshake"; server_read con
    | Update true ->
      begin
        trace "connection writable";
        let id = TLS.currentId con Writer in
        // we make a point of sending a padded empty fragment, because we can!
        match TLS.write con (DataStream.appFragment id (0,10) Bytes.empty_bytes) with
        | Written -> trace "sent 0.5 empty fragment"; server_read con
        | w -> trace ("failed to write 0.5 fragment: "^string_of_ioresult_w w)
      end
    | Read (DataStream.Alert a) -> trace ("unexpected alert: "^string_of_ad a)
    | Read (DataStream.Data d) ->
      begin
      let db = DataStream.appBytes d in
      let Some txt = Bytes.iutf8_opt db in 
      trace ("Received data: "^txt);
      let response = "You are connected to miTLS*!\r\n"
        ^ "This is the request you sent:\r\n\r\n" ^ txt in
      let payload = Bytes.utf8_encode ("HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: "
        ^ string_of_int (String.length response)
        ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n"^response) in
      let id = TLS.currentId con Writer in
      let rg : Range.frange id = Range.point (Bytes.length payload) in
      let f = DataStream.appFragment id rg payload in
      match TLS.write con f with
      | Written  ->
       begin
        trace "Closing down...";
	match writeCloseNotify con with
        | WriteClose ->
          let id = TLS.currentId con Reader in
          (match TLS.read con id with
          | Read DataStream.Close -> trace "Received close_notify! Closing socket."
          | _ -> trace "Peer did not send close_notify.")
        | WriteError _ r -> trace ("Failed to close: "^r)
       end
      | w -> trace ("failed to write HTTP response")
     end
    | r -> trace ("unexpected read result: "^string_of_ioresult_i #id r)

private let rec server_loop rid sock config: ML unit =
  let c = TLS.accept rid sock config in
  server_read c;
  server_loop rid sock config

let server config host port =
 trace "*** Starting test TLS server ***";
 let sock = Tcp.listen host port in
 let rid = new_region root in
 server_loop rid sock config
