module Curve25519

open FStar.Heap

open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST

open Platform.Bytes

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare): Tot point = fst k

(* 18-02-10 MERGE delete, subsumed by HaclProvider
// FIXME: Convert between Platform bytes (Seq.seq Char.char) and Hacl.Spec.Lib.bytes (Seq.seq UInt8.t)
private let bytes2hacl (b:bytes) : Tot (s:Seq.seq UInt8.t{Seq.length s = Seq.length b}) =
  Seq.init (length b) (fun i ->
    UInt8.uint_to_t (FStar.Char.int_of_char (Platform.Bytes.index b i)))

private let hacl2bytes (s:Seq.seq UInt8.t) : Tot (b:bytes{length b = Seq.length s}) =
  Platform.Bytes.initBytes (Seq.length s) (fun i ->
    FStar.Char.char_of_int (UInt8.v (Seq.index s i)))

private let scalarmult k p = 
  let p = Spec.Curve25519.scalarmult (bytes2hacl k) (bytes2hacl p) in
  hacl2bytes p

let point_of_scalar (s:scalar) : Tot point =
  let base_point = Seq.upd (Seq.create 32 0uy) 0 9uy in
  let p = X.scalarmult (bytes2hacl s) base_point in
  hacl2bytes p
*)

assume 
val mul: secret:scalar -> point:point -> ST (lbytes 32)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1) 

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s: lbytes 32 = CoreCrypto.random 32 in
  let base: point = Seq.upd (Seq.create 32 0uy) 0 9uy in
  mul s base, s
