module TestAPI

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open HandshakeLog
open Negotiation
open Handshake
open TLSError
open TLSInfo
open TLSConstants
open TLS

module CC = CoreCrypto

let rec read_loop con r =
  match TLS.read con r with
  | Read (DataStream.Data d) ->
    let db = DataStream.appBytes d in
    IO.print_string ("Received data: "^(iutf8 db));
    read_loop con r
  | ReadError _ t ->
    IO.print_string ("ReadError: "^t^"\n")
  | Read (DataStream.Close) ->
    IO.print_string "Got close_notify, closing connection...\n";
    let _ = TLS.writeCloseNotify con in
    ()
  | Read (DataStream.Alert a)->
    IO.print_string ("Got alert: "^(string_of_ad a)^"\n");
    IO.print_string "Closing connection.\n";
    let _ = TLS.writeCloseNotify con in
    ()

let client config host port =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let con = TLS.connect rid tcp config in

  let id = TLS.currentId con Reader in
  match TLS.read con id with
    | Complete ->
       IO.print_string "Read OK, sending HTTP request...\n";
       let payload = utf8 ("GET /r HTTP/1.1\r\nConnection: close\r\nHost: " ^ host ^ "\r\n\r\n") in
       let id = TLS.currentId con Writer in
       let rg : Range.frange id = Range.point (length payload) in
       let f = DataStream.appFragment id rg payload in
       (match TLS.write con f with
       | Written ->
         let r = TLS.currentId con Reader in
         read_loop con r
       | WriteError _ t -> IO.print_string ("Write error:"^t^"\n")
       | _ -> IO.print_string "unexpted ioresult_w\n")
    | ReadError o t ->
      IO.print_string ("ReadError: "^t^"\n")
    | _ -> IO.print_string "unexpected ioresult_i read\n"

private let rec aux_server config sock =
  let rid = new_region root in
  let con = TLS.accept rid sock config in
  let id = TLS.currentId con Reader in

  let () = match TLS.read con id with
  | Complete ->
   begin
    let id = TLS.currentId con Reader in
    match TLS.read con id with
    | Read (DataStream.Data d) ->
     begin
      let db = DataStream.appBytes d in
      IO.print_string ("Received data: "^(iutf8 db));
      let text = "You are connected to miTLS* 1.3!\r\n"
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
        IO.print_string "Reading again\n";
        let id = TLS.currentId con Reader in
        match TLS.read con id with
        | Read DataStream.Close -> IO.print_string "Received close_notify! Closing socket.\n"
        | _ -> IO.print_string "improperly closed connection\n"
       end
      | _ -> IO.print_string "failed to write HTTP response\n"
     end
    | _ -> IO.print_string "unexpected ioresult_w\n"
   end
  | _ -> IO.print_string "unexpected ioresult_i read\n"
  in aux_server config sock

let server config host port =
 IO.print_string "===============================================\n Starting test TLS 1.3 server...\n";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
