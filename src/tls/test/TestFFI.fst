module TestFFI

// a variant of TestAPI for testing FFI.fst

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants

open FFI

private let pr s = IO.print_string ("FFI: "^s^".\n") // verbose
// let pr s = ()  // quieter


private let rec readAll c : ML unit = // auxiliary while loop for reading the full response
  match read c with
  | Received extra -> pr ("Received data:\n"^iutf8 extra); readAll c
  | Errno 0        -> pr "Received close_notify! Socket closed"
  | Errno e        -> pr "Improperly closed connection"


let client config host port =
  pr "===============================================";
  pr "Starting test client..."; (
  let tcp = Platform.Tcp.connect host port in 
  let request = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in 
  let send x = let b = IO.debug_print_string "TCP:send\n" in Platform.Tcp.send tcp x in
  let recv x = let b = IO.debug_print_string "TCP:recv\n" in Platform.Tcp.recv tcp x in
  match connect send recv config with 
  | c, 0 -> (
    pr "Read OK, sending HTTP request..."; (
    match write c (utf8 request) with
    | 0 -> (
      match read c with
      | Received response -> (
        pr ("Received data:\n"^iutf8 response);
        pr "Closing connection, irrespective of the response";
        match close c with 
        | 0 -> pr "Sent close_notify, will block waiting for the server's"; readAll c
        | _ -> pr "close error")
      | Errno _ -> pr "read error")  
    | _  -> pr "write error"))
  | _, err  -> pr "connect error" )


(* TBC one we extend FFI.fst to server 
let rec aux_server config sock =
  let con = FFI.accept sock config in
  match TLS.read con id with
  | Complete ->
   begin
    let id = TLS.currentId con Reader in
    match TLS.read con id with
    | Read (DataStream.Data d) ->
     begin
      let db = DataStream.appBytes d in
      pr ("Received data: "^(iutf8 db));
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
        let id = TLS.currentId con Reader in
        match TLS.read con id with
        | Read DataStream.Close -> pr "Received close_notify! Closing socket.\n"
        | _ -> pr "improperly closed connection\n"
       end
      | _ -> pr "failed to write HTTP response\n"
     end
    | _ -> pr "unexpted ioresult_w\n"
   end
  | _ -> pr "unexpected ioresult_i read\n"
  in aux_server config sock

let server config host port =
 pr "===============================================\n Starting test TLS 1.3 server...\n";
 let sock = Platform.Tcp.listen host port in
 aux_server config sock
*)
