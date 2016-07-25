module TestAPI

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open Platform.Tcp
open HandshakeMessages
open HandshakeLog
open Negotiation
open Handshake
open TLSError
open TLSInfo
open TLSConstants
open TLS
open FFICallbacks
open FFI

module CC = CoreCrypto

/////////////////////////////////////////////////////////////////////////
let s2pv = function
  | "1.2" -> TLS_1p2
  | "1.3" -> TLS_1p3
  | "1.1" -> TLS_1p1
  | "1.0" -> TLS_1p0
  | s -> failwith ("Invalid protocol version specified: "^s)

let ffiConfig version host =
  let v = s2pv version in 
  {defaultConfig with
    minVer = v;
    maxVer = v;
    check_peer_certificate = false;
    cert_chain_file = "c:\\Repos\\mitls-fstar\\data\\test_chain.pem";
    private_key_file = "c:\\Repos\\mitls-fstar\\data\\server.key";
    ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
    safe_resumption = true;
    ciphersuites = cipherSuites_of_nameList [TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256];
  }

type callbacks = FFICallbacks.callbacks

val sendTcpPacket: callbacks:callbacks -> buf:bytes -> Platform.Tcp.EXT (Platform.Error.optResult string unit) 
let sendTcpPacket callbacks buf =  
  let result = FFICallbacks.ocaml_send_tcp callbacks (get_cbytes buf) in 
  if result < 0 then 
    Platform.Error.Error ("socket send failure") 
  else 
    Platform.Error.Correct () 
    
val recvTcpPacket: callbacks:callbacks -> max:nat -> Platform.Tcp.EXT (Platform.Error.optResult string (b:bytes{length b <= max}))
let recvTcpPacket callbacks max =
  let (result,str) = FFICallbacks.recvcb callbacks max in
  if (result <= 0) then
    Platform.Error.Error ("socket recv failure")
  else
    Platform.Error.Correct(abytes str)
  
val ffiConnect: config:config -> callbacks:callbacks -> Connection.connection * int 
let ffiConnect config cb =
  connect (sendTcpPacket cb) (recvTcpPacket cb) config
  
val ffiRecv: Connection.connection -> cbytes  
let ffiRecv c =
  match read c with
    | Received response -> get_cbytes response
    | Errno _ -> get_cbytes empty_bytes
  
val ffiSend: Connection.connection -> cbytes -> int
let ffiSend c b =
  let msg = abytes b in
  write c msg

let client config host port =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let con = TLS.connect rid tcp config in

  let id = TLS.currentId con Reader in
  match TLS.read con id with
    | Complete ->
       IO.print_string "Read OK, sending HTTP request...\n";
       let payload = utf8 ("GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n") in
       let id = TLS.currentId con Writer in
       let rg : Range.frange id = Range.point (length payload) in
       let f = DataStream.appFragment id rg payload in
       (match TLS.write con f with
       | Written -> (
         let id = TLS.currentId con Reader in
         match TLS.read con id with
         | Read (DataStream.Data d) ->
           let db = DataStream.appBytes d in
           IO.print_string ("Received data: "^(iutf8 db));
           let _ = TLS.writeCloseNotify con in
           IO.print_string "Closing connection.\n")
//           (match TLS.read con id with
//           | Read DataStream.Close -> IO.print_string "Received close_notify! Closing socket.\n"
//           | _ -> IO.print_string "improperly closed connection\n"))
       | WriteError _ t -> IO.print_string ("Write error:"^t^"\n")
       | _ -> IO.print_string "unexpted ioresult_w\n")
    | _ -> IO.print_string "unexpected ioresult_i read\n"

let rec aux_server config sock =
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
