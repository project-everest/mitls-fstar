module Curve25519

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST

open FStar.Bytes
open Platform.Error

module X = Spec.Curve25519
module CC = CoreCrypto

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

// Test files replace the rand function with a deterministic variant.
let rand: ref (n:nat -> ST (lbytes n) (requires fun h->True) (ensures fun h0 _ h1 -> modifies_none h0 h1)) =
  ralloc root CC.random

// FIXME: Convert between Platform bytes (Seq.seq Char.char) and Hacl.Spec.Lib.bytes (Seq.seq UInt8.t)
let bytes2hacl (b:bytes) : Tot (s:Seq.seq UInt8.t{Seq.length s = Seq.length b}) =
  Seq.init (length b) (fun i ->
    UInt8.uint_to_t (FStar.Char.int_of_char (FStar.Bytes.index b i)))

let hacl2bytes (s:Seq.seq UInt8.t) : Tot (b:bytes{length b = Seq.length s}) =
  FStar.Bytes.initBytes (Seq.length s) (fun i ->
    FStar.Char.char_of_int (UInt8.v (Seq.index s i)))

let point_of_scalar (s:scalar) : Tot point =
  let base_point = Seq.upd (Seq.create 32 0uy) 0 9uy in
  let p = X.scalarmult (bytes2hacl s) base_point in
  hacl2bytes p

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s : lbytes 32 = !rand 32 in
  (point_of_scalar s, s)

let mul (k:scalar) (p:point) : Tot point =
  let p = X.scalarmult (bytes2hacl k) (bytes2hacl p) in
  hacl2bytes p
