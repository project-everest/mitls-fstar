module TestAPI

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants
open TLS

module CC = CoreCrypto

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

// a permissive client loop (not checking the TLS state machine)
let rec client_read con host: ML unit =
  let r = TLS.currentId con Reader in
  match TLS.read con r with
  | Update true // aggressively using 0RTT 
  | Complete ->
       trace "Read OK, sending HTTP request...";
       let payload = utf8 ("GET /r HTTP/1.1\r\nConnection: close\r\nHost: " ^ host ^ "\r\n\r\n") in
       let id = TLS.currentId con Writer in
       let rg : Range.frange id = Range.point (length payload) in
       let f = DataStream.appFragment id rg payload in
       (match TLS.write con f with
       | Written -> client_read con host
       | WriteError _ t -> trace ("Write error:"^t)
       | _ -> trace "unexpected ioresult_w")
  | Read (DataStream.Data d) ->
    let db = DataStream.appBytes d in
    trace ("Received data: "^iutf8 db);
    client_read con host
  | ReadError _ t ->
    trace ("ReadError: "^t)
  | Read (DataStream.Close) ->
    // already echoed by TLS
    //let _ = TLS.writeCloseNotify con in
    ()
  | Read (DataStream.Alert a)->
    trace ("Got alert: "^(string_of_ad a)^"\n");
    trace "Closing connection.\n";
    let _ = TLS.writeCloseNotify con in
    ()
  | other -> trace ("unexpected read result: "^string_of_ioresult_i #r other)

let client config host port offerpsk =
  trace "*** Starting miTLS client...";
  let tcp = Transport.connect host port in
  
  let rid = new_region root in
  let con = TLS.resume rid tcp config None offerpsk in
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
        match TLS.write con (DataStream.appFragment id (0,10) empty_bytes) with
        | Written -> trace "sent 0.5 empty fragment"; server_read con
        | w -> trace ("failed to write 0.5 fragment: "^string_of_ioresult_w w)
      end
    | Read (DataStream.Alert a) -> trace ("unexpected alert: "^string_of_ad a)
    | Read (DataStream.Data d) ->
      begin
      let db = DataStream.appBytes d in
      trace ("Received data: "^(iutf8 db));
      let text = "You are connected to miTLS*!\r\n"
        ^ "This is the request you sent:\r\n\r\n" ^ (iutf8 db) in
      let payload = utf8 ("HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:"
        ^ (string_of_int (length (abytes text)))
        ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text) in
      let id = TLS.currentId con Writer in
      let rg : Range.frange id = Range.point (length payload) in
      let f = DataStream.appFragment id rg payload in
      match TLS.write con f with
      | Written  ->
       begin
        trace "Written; now closing";
        match TLS.writeClose con with
        | WriteClose -> (
            let id = TLS.currentId con Reader in
            match TLS.read con id with
            | Read DataStream.Close -> trace "Received close_notify, closing socket. The test succeeds!"
            | r -> trace ("improperly closed connection: "^string_of_ioresult_i #id r))
        | w -> trace ("failed to close_notify")
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
 let sock = Platform.Tcp.listen host port in
 let rid = new_region root in
 server_loop rid sock config
