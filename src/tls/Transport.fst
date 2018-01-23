module Transport
module HS = FStar.HyperStack //Added automatically

// adding an indirection to TCP for applications that prefer to take control of their IOs.

open FStar.HyperStack.All

open FStar.Tcp
open FStar.Bytes
open FStar.Error
open TLSError

// make this type abstract?

type external = FStar.Dyn.dyn
noeq type t = {
  app_context : external;
  snd: external -> bytes -> ST (optResult string unit) (fun _ -> True) (fun h0 _ h1 -> h0 == h1);
  rcv: external  -> max:nat -> ST (recv_result max) (fun _ -> True) (fun h0 _ h1 -> h0 == h1) }

let callbacks v send recv = { app_context = v; snd = send; rcv = recv }

// platform implementation

/// 18-01-23 after hoisting for Kremlin extraction, we treat the
/// explicit context as a dyn to avoid climbing in universes; this
/// forces us to coerce FStar.Tcp.networkStream to dyn and back when
/// using TCP instead of C-defined callbacks. Any better idea?

#set-options "--lax" 
private let send_tcp (x:external) (b:bytes): ST (optResult string unit) (fun _ -> True) (fun h0 _ h1 -> h0 == h1) = 
  let n: networkStream = FStar.Dyn.undyn x in
  send n b
private let recv_tcp (x:external) (max:nat): ST (recv_result max) (fun _ -> True) (fun h0 _ h1 -> h0 == h1) = 
  let n: networkStream = FStar.Dyn.undyn x in
  recv_async n max
#reset-options


let wrap tcp: t = callbacks (FStar.Dyn.mkdyn tcp) send_tcp recv_tcp
type tcpListener = tcpListener

let listen domain port : ML tcpListener = listen domain port
let accept listener = wrap (accept listener)
let connect domain port = wrap (connect domain port)
let close = close

// following the indirection

let send tcp data = tcp.snd tcp.v data
let recv tcp len = tcp.rcv tcp.v len

val test: t networkStream -> bytes -> ML unit
let test (tcp:t networkStream) (data:bytes) = 
  let h0 = FStar.HyperStack.ST.get() in 
  let _ = tcp.snd tcp.v data in
  let h1 = FStar.HyperStack.ST.get() in 
  assert (h0==h1)


// for now we get a runtime error in case of partial write on an asynchronous socket


// forces read to complete, even if the socket is non-blocking.
// this may cause spinning.

private val really_read_rec: b:bytes -> t 'a -> l:nat -> ST (recv_result (l+length b))
  (fun _ -> True) (fun h0 _ h1 -> h0 == h1)
let rec really_read_rec prev tcp len =
    if len = 0
    then Received prev
    else
      match recv tcp len with
      | RecvWouldBlock -> really_read_rec prev tcp len
      | Received b ->
            let lb = length b in
            if lb = len then Received(prev @| b)
            else if lb = 0 then RecvError "TCP close" //16-07-24 otherwise we loop...
            else really_read_rec (prev @| b) tcp (len - lb)
      | RecvError e -> RecvError e

let really_read = really_read_rec empty_bytes
