module TCP.Transport

open FStar.HyperStack.All
open FStar.Bytes
open FStar.Error
open TLSError
open Transport

/// 18-01-23 FStar.Tcp implementation. We now have to coerce
/// FStar.Tcp.networkStream to dyn and back when using TCP instead of
/// C-defined callbacks, and to bridge the Low*/F* calling conventions.
private 
let send_tcp : pfn_send = fun ptr buffer len ->
  let n: FStar.Tcp.networkStream = FStar.Dyn.undyn ptr in
  let v = BufferBytes.to_bytes (UInt32.v len) buffer in 
  match FStar.Tcp.send n v with 
  | Correct () -> Int.Cast.uint32_to_int32 len
  | Error _ignored -> -1l

private
let recv_tcp : pfn_recv = fun ptr buffer len ->
  let n: FStar.Tcp.networkStream = FStar.Dyn.undyn ptr in
  match FStar.Tcp.recv_async n (UInt32.v len) with 
  | FStar.Tcp.RecvWouldBlock -> 0l // return instead EAGAIN or EWOULDBLOCK?
  | FStar.Tcp.RecvError _ignored -> -1l 
  | FStar.Tcp.Received b -> 
    let target = Buffer.sub buffer 0ul (Bytes.len b) in
    BufferBytes.store_bytes (length b) target 0 b;
    Int.Cast.uint32_to_int32 (Bytes.len b)

let wrap (ns:FStar.Tcp.networkStream) : Dv t = callbacks (FStar.Dyn.mkdyn tcp) send_tcp recv_tcp

let listen domain port : ML FStar.Tcp.tcpListener = FStar.Tcp.listen domain port

let accept listener = wrap (FStar.Tcp.accept listener)

let connect domain port = wrap (FStar.Tcp.connect domain port)

let close = FStar.Tcp.close
