module TLS.Curve25519

open FStar.Heap

open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST

open FStar.Bytes

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare): Tot point = fst k

//NS: 2/2 See issue #21 and #14
// Test files used to replace the rand function with a deterministic variant.
// let rand: ref (n:nat -> ST (lbytes n) (requires fun h->True) (ensures fun h0 _ h1 -> modifies_none h0 h1)) =
//   ralloc root CC.random

val mul: secret:scalar -> point:point -> ST (lbytes 32)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1) 
let mul secret point = HaclProvider.crypto_scalarmult secret point

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s: lbytes 32 = CoreCrypto.random 32 in
  let base: point = Bytes.set_byte (Bytes.create 32ul 0uy) 0ul 9uy in
  mul s base, s
