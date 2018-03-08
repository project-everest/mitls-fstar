module TLS.Curve25519

open FStar.Bytes
open FStar.Error

open FStar.HyperStack.ST

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

//NS: 2/2 See issue #21 and #14
// Test files replace the rand function with a deterministic variant.
// let rand: ref (n:nat -> ST (lbytes n) (requires fun h->True) (ensures fun h0 _ h1 -> modifies_none h0 h1)) =
//   ralloc root CoreCrypto.random

let scalarmult (secret:Bytes.lbytes 32) (point:Bytes.lbytes 32)
  : ST (lbytes 32)
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 -> modifies_none h0 h1)) =
  HaclProvider.crypto_scalarmult secret point

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s : lbytes 32 = CoreCrypto.random 32 in
  let base_point =
    Bytes.bytes_of_hex
      "0900000000000000000000000000000000000000000000000000000000000000" in
  assume (Bytes.length base_point == 32);
  scalarmult s base_point, s

let mul (k:scalar) (p:point) : ST point
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  = scalarmult k p
