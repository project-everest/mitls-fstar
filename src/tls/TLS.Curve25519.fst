module TLS.Curve25519

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST

open FStar.Bytes
open Platform.Error

module X = Curve25519
module CC = CoreCrypto
module U32 = FStar.UInt32

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

// Test files replace the rand function with a deterministic variant.
let rand: ref (n:nat -> ST (lbytes n) (requires fun h->True) (ensures fun h0 _ h1 -> modifies_none h0 h1)) =
  ralloc root CC.random

// FIXME: Convert between Platform bytes (Seq.seq Char.char) and Hacl.Spec.Lib.bytes (Seq.seq UInt8.t)
// Kremlin issue why isn't this being warned on?
private let bytes2hacl_aux (b : bytes) (i : nat) = FStar.Bytes.get b (U32.uint_to_t i)

let bytes2hacl (b:bytes) : Tot (s:Seq.seq UInt8.t{Seq.length s = length b}) =
Seq.init (length b) (bytes2hacl_aux b)

private let hacl2bytes_aux (s : Seq.seq UInt8.t) (i : U32.t) =
Seq.index s (U32.v i)

let hacl2bytes (s:Seq.seq UInt8.t) : Tot (b:bytes{length b = Seq.length s}) =
  FStar.Bytes.init (FStar.UInt32.uint_to_t (Seq.length s)) (hacl2bytes_aux s)

// let point_of_scalar (s:scalar) : Tot point =
//   let base_point = Seq.upd (Seq.create 32 0uy) 0 9uy in
//   let p = X.scalarmult (bytes2hacl s) base_point in
//   hacl2bytes p

let scalarmult (secret:Bytes.lbytes 32) (point:Bytes.lbytes 32) 
  : ST (lbytes 32)
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 -> modifies_none h0 h1)) = 
  let out = Buffer.create 0uy 32ul in
  let scalar = BufferBytes.from_bytes secret in
  let point = BufferBytes.from_bytes point in
  X.crypto_scalarmult out scalar point;
  BufferBytes.to_bytes 32 out

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s : lbytes 32 = !rand 32 in
  let base_point = Bytes.set_byte (Bytes.create 32ul 0uy) 0ul 9uy in
  scalarmult s base_point, s
  
let mul (k:scalar) (p:point) : ST point
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  = scalarmult k p
