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
open TLSInfo
open TLS

module CC = CoreCrypto

let main config host port =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let con = TLS.connect rid tcp config in

  let id = TLS.currentId con Reader in
  let n = match TLS.read con id with
    | Read d -> IO.print_string "Read\n"
    | ReadError i t -> IO.print_string "ReadError\n"
    | CertQuery q _ -> IO.print_string "CertQuery\n"
    | Complete -> IO.print_string "Complete\n"
    | _ -> IO.print_string "unexpected ioresult_i read\n" in

  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
//  let get = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
//  sendRecord tcp pv Content.Application_data get "GET /";
//  let ad = recvEncAppDataRecord tcp pv drd in
  disconnect con
