module TLS.Curve25519

open FStar.Bytes
open FStar.Error

open FStar.HyperStack.ST

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

let scalarmult (secret:Bytes.lbytes 32) (point:Bytes.lbytes 32)
  : ST (lbytes 32)
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 -> modifies_none h0 h1)) =
  EverCrypt.Bytes.x25519 secret point

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s : lbytes 32 = CoreCrypto.random 32 in
  let base_point = Bytes.create 1ul 9uy @| Bytes.create 31ul 0uy in
  scalarmult s base_point, s

let mul (k:scalar) (p:point) : ST point
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  = scalarmult k p
