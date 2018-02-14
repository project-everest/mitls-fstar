module Transport

// adding an indirection to TCP for applications that prefer to take control of their IOs.

open FStar.Bytes
open FStar.Error
open TLSError
open Mem


/// 18-01-23 We now have function pointers matching the types used in
/// mitls.h. After hoisting for Kremlin extraction, we treat the
/// explicit context as a dyn to avoid climbing in universes.

type pvoid = FStar.Dyn.dyn
type size_t = UInt32.t 
type pfn_send = 
  pvoid -> 
  output_buffer: FStar.Buffer.buffer UInt8.t -> 
  max_len: size_t -> ST Int32.t
  (requires fun h0 -> 
    Buffer.live h0 output_buffer /\ 
    UInt32.v max_len = Buffer.length output_buffer)
  (ensures fun h0 r h1 -> 
    let v = Int32.v r in
    modifies_none h0 h1 /\
    (v = -1 \/ (0 <= v /\ v <= UInt32.v max_len)))

type pfn_recv = 
  pvoid -> 
  input_buffer: FStar.Buffer.buffer UInt8.t -> 
  max_len: size_t -> ST Int32.t
  (requires fun h0 ->
    Buffer.live h0 input_buffer /\
    UInt32.v max_len = Buffer.length input_buffer)
  (ensures fun h0 r h1 -> 
    let v = Int32.v r in 
    Buffer.modifies_1 input_buffer h0 h1 /\ 
    (v = -1 \/ (0 <= v /\ v <= UInt32.v max_len)))
    
noeq type t = {
  ptr : pvoid;
  snd: pfn_send;
  rcv: pfn_recv }

let callbacks v send recv: t = { ptr = v; snd = send; rcv = recv }

// following the indirection
let send t buffer len = t.snd t.ptr buffer len 
let recv t buffer len = t.rcv t.ptr buffer len 

// val test: t -> b: Buffer.buffer UInt8.t {Buffer.length b = 5} -> ST unit
//   (requires fun h0 -> Buffer.live h0 b)
//   (ensures fun h0 r h1 -> h0 == h1)
// let test t b =
//   let _ = send t b 5ul in
//   ()

// for now we get a runtime error in case of partial write on an asynchronous socket

(* 18-01-23 not used in quic2c? 

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
*)



