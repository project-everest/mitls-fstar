module TLS.Curve25519
module HS = FStar.HyperStack //Added automatically

open FStar.Heap

open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST

open FStar.Bytes
open FStar.Error

module CC = CoreCrypto
module U32 = FStar.UInt32

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

// Test files replace the rand function with a deterministic variant.
let rand: ref (n:nat -> ST (lbytes n) (requires fun h->True) (ensures fun h0 _ h1 -> modifies_none h0 h1)) =
  ralloc root CC.random

let scalarmult (secret:Bytes.lbytes 32) (point:Bytes.lbytes 32) 
  : ST (lbytes 32)
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 -> modifies_none h0 h1)) = 
  LowCProvider.crypto_scalarmult secret point

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
