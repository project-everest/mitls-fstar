module MITLS.Repr.PskIdentity
module RO = MITLS.Repr.Opaque
open FStar.Integers
module LP = LowParse.Low.Base
module HS = FStar.HyperStack
open FStar.HyperStack.ST
module R = MITLS.Repr
module PI = Parsers.PskIdentity
module B = LowStar.Buffer

noeq
type t #p #q (b:LP.slice p q) = {
  identity: RO.repr b;
  obfuscated_ticket_age: uint_32
}

let valid #p #q (#b:LP.slice p q) (x:t b) (h:HS.mem) =
  RO.valid x.identity h

let mk #p #q (b:LP.slice p q) (r:R.repr PI.pskIdentity b)
  : Stack (t b)
    (requires
      R.valid r)
    (ensures fun h0 r h1 ->
      valid r h1 /\
      B.modifies B.loc_none h0 h1)
  = admit()

let write #p #q (#b:LP.slice p q) (x:t b)
  : Stack (R.repr PI.pskIdentity b)
    (requires fun h0 ->
      UInt32.v (RO.end_pos x.identity) + 4 < UInt32.v LP.(b.len) /\
      valid x h0 /\
      R.rewritable b
        (RO.start_pos x.identity)
        (RO.end_pos x.identity + 4ul)
        h0)
    (ensures fun h0 r h1 ->
      R.valid r h1 /\
      B.modifies (R.fp r) h0 h1 /\
      R.(r.start_pos) == RO.start_pos x.identity /\
      R.(r.end_pos) == RO.end_pos x.identity + 4ul)
  = admit()
