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


let rec read_loop con r : ML unit =
  match TLS.read con r with
  | Read (DataStream.Data d) ->
    let db = DataStream.appBytes d in
    trace ("Received data: "^(iutf8 db));
    read_loop con r
  | ReadError _ t ->
    trace ("ReadError: "^t^"\n")
  | Read (DataStream.Close) ->
    trace "Got close_notify, closing connection...\n";
    let _ = TLS.writeCloseNotify con in
    ()
  | Read (DataStream.Alert a)->
    trace ("Got alert: "^(string_of_ad a)^"\n");
    trace "Closing connection.\n";
    let _ = TLS.writeCloseNotify con in
    ()

let client config host port offerpsk =
  trace "*** Starting miTLS client...";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let con = TLS.resume rid tcp config None offerpsk in

  let id = TLS.currentId con Reader in
  match TLS.read con id with
    | Complete ->
       trace "Read OK, sending HTTP request...";
       let payload = utf8 ("GET /r HTTP/1.1\r\nConnection: close\r\nHost: " ^ host ^ "\r\n\r\n") in
       let id = TLS.currentId con Writer in
       let rg : Range.frange id = Range.point (length payload) in
       let f = DataStream.appFragment id rg payload in
       (match TLS.write con f with
       | Written ->
         let r = TLS.currentId con Reader in
         read_loop con r
       | WriteError _ t -> trace ("Write error:"^t)
       | _ -> trace "unexpected ioresult_w")
    | ReadError o t ->
      trace ("ReadError: "^t)
    | _ -> trace "unexpected ioresult_i read"

private let rec aux_server config sock : ML unit =
  let rid = new_region root in
  let con = TLS.accept rid sock config in
  let id = TLS.currentId con Reader in

  let r = TLS.read con id in
  trace (TLS.string_of_ioresult_i r);
  let () = match r with
  | Complete ->
   begin
    let id = TLS.currentId con Reader in
    let r = TLS.read con id in
    trace (TLS.string_of_ioresult_i r);
    match r with
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
        trace "Reading again\n";
        let id = TLS.currentId con Reader in
        match TLS.read con id with
        | Read DataStream.Close -> trace "Received close_notify! Closing socket."
        | _ -> trace "improperly closed connection."
       end
      | _ -> trace "failed to write HTTP response."
     end
    | Read (DataStream.Alert a) -> trace ("unexpected alert: "^string_of_ad a)
    | _ -> trace "unexpected read result"
   end
  | _ -> trace "unexpected ioresult_i read."
  in aux_server config sock

let server config host port =
 trace "*** Starting test TLS server ***";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
