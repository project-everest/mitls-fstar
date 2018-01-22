module Transport
module HS = FStar.HyperStack //Added automatically

// adding an indirection to TCP for applications that prefer to take control of their IOs.

open FStar.HyperStack.All

open FStar.Tcp
open FStar.Bytes
open FStar.Error
open TLSError

// make this type abstract?
noeq type t (ctx:Type0) = {
  v: ctx;
  snd: ctx -> bytes -> ST (optResult string unit) (fun _ -> True) (fun h0 _ h1 -> h0 == h1);
  rcv: ctx -> max:nat -> ST (recv_result max) (fun _ -> True) (fun h0 _ h1 -> h0 == h1) }

let callbacks v send recv = { v = v; snd = send; rcv = recv }

// platform implementation

let wrap tcp: t networkStream = callbacks tcp send recv_async
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

private val really_read_rec: b:bytes -> t -> l:nat -> ST (recv_result (l+length b))
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
