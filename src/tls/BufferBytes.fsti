(**
Functions to go back and forth between FStar.Bytes and Buffers
*)
module BufferBytes

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Seq
open FStar.Bytes

(* module U32 = FStar.UInt32 *)
(* #set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1" *)

type lbuffer (l:nat) = b:Buffer.buffer UInt8.t {Buffer.length b == l}

val to_bytes: l:nat -> buf:lbuffer l -> Stack (b:bytes{length b = l})
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 b h1 -> h0 == h1 /\ b = Bytes.hide (Buffer.as_seq h0 buf)))
(* let rec to_bytes l buf = *)
(*   if l = 0 then empty_bytes *)
(*   else *)
(*     let b = Buffer.index buf 0ul in *)
(*     let s = abyte b in *)
(*     let t = to_bytes (l - 1) (Buffer.sub buf 1ul (U32.uint_to_t (l-1))) in *)
(*     let r = s @| t in *)
(*     (//lemma_len_append s t; //TODO bytes NS 09/27 seems unnecessary *)
(*      r) *)

val store_bytes: len:nat -> buf:lbuffer len -> i:nat{i <= len} -> b:bytes{length b = len} -> Stack unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1))
(* let rec store_bytes len buf i s = *)
(*   if i < len then *)
(*     let i_ul = U32.uint_to_t i in *)
(*     let () = Buffer.upd buf i_ul s.[i_ul] in *)
(*     store_bytes len buf (i + 1) s *)

val from_bytes: b:bytes{UInt.fits (length b) 32} -> Stack (lbuffer (length b))
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 -> 
    Buffer.modifies_0 h0 h1 /\ 
    Buffer.live h1 buf /\
    b = Bytes.hide (Buffer.as_seq h0 buf)))
(* let from_bytes b = *)
(*   let buf = Buffer.rcreate root 0uy (U32.uint_to_t (length b)) in *)
(*   store_bytes (length b) buf 0 b; *)
(*   buf *)
