module TLS.Curve25519

open FStar.Bytes
open FStar.Error

open FStar.HyperStack.ST

module B = FStar.Bytes
module LB = LowStar.Buffer

type scalar = lbytes 32
type point = lbytes 32
type keyshare = point * scalar

let pubshare (k:keyshare) : Tot point = fst k

let scalarmult (secret:Bytes.lbytes 32) (point:Bytes.lbytes 32)
  : ST (lbytes 32)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1)) =
  push_frame ();
  let lp = B.len point in
  let ls = B.len secret in
  let pb = LB.alloca 0uy lp in
  let sb = LB.alloca 0uy ls in
  let out = LB.alloca 0uy 32ul in
  B.store_bytes point pb;
  B.store_bytes secret sb;
  assume false;
  EverCrypt.x25519 out sb pb;
  pop_frame (); B.of_buffer 32ul out

let keygen () : ST keyshare
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let s : lbytes 32 = Random.sample32 32ul in
  let base_point = Bytes.create 1ul 9uy @| Bytes.create 31ul 0uy in
  scalarmult s base_point, s

let mul (k:scalar) (p:point) : ST point
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  = scalarmult k p
