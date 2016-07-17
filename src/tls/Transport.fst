module Transport

// adding an indirection to TCP for applications that prefer to take control of their IOs.

open Platform.Tcp 
open Platform.Bytes
open Platform.Error
open TLSError

// make this type abstract? 
noeq type t = 
  { snd: bytes -> EXT (optResult string unit);
    rcv: max:nat -> EXT (optResult string (b:bytes {length b <= max})); 
    } 

let callbacks send recv = { snd = send; rcv = recv } 

// platform implementation

let wrap tcp: t = callbacks (send tcp) (recv tcp)
type tcpListener = tcpListener

let listen domain port : tcpListener = listen domain port
let accept listener = wrap (accept listener)
let connect domain port = wrap (connect domain port)
let close = close

// following the indirection 

let send tcp data = tcp.snd data
let recv tcp len = tcp.rcv len


// reading till we get enough bytes

private val really_read_rec: b:bytes -> t -> l:nat -> EXT (result (lbytes (l+length b)))

let rec really_read_rec prev tcp len = 
    if len = 0 
    then Correct prev
    else 
      match recv tcp len with
      | Correct b -> 
            let lb = length b in
      	    if lb = len then Correct(prev @| b)
      	    else really_read_rec (prev @| b) tcp (len - lb)
      | Error e -> Error(AD_internal_error,e)

let really_read = really_read_rec empty_bytes
