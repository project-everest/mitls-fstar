module MITLS.Repr.OfferedPsks
module RL = MITLS.Repr.List
module RO = MITLS.Repr.Opaque
module R_PSK = MITLS.Repr.PskIdentity
module LP = LowParse.Low.Base
module PSK = Parsers.PskIdentity
module PBE = Parsers.PskBinderEntry
module HS = FStar.HyperStack
module R = MITLS.Repr
module OPSK = Parsers.OfferedPsks
module B = LowStar.Buffer
open FStar.HyperStack.ST

noeq
type t #p #q (b:LP.slice p q) = {
  identities: RL.repr PSK.pskIdentity b;
  binders: RL.repr PBE.pskBinderEntry b
}

let related #p #q (#b:LP.slice p q) (x:t b)
            #p' #q' (#b':LP.slice p' q') (r:R.repr OPSK.offeredPsks b') =
   RL.value x.identities == OPSK.((R.value r).identities) /\
   RL.value x.binders == OPSK.((R.value r).binders)

let valid #p #q (#b:LP.slice p q) (x:t b) (h:HS.mem) =
  RL.valid x.identities h /\
  RL.valid x.binders h /\
  RL.(x.identities.end_pos == x.binders.start_pos)

let mk #p #q (#b:LP.slice p q) (r0:R.repr_p _ b OPSK.offeredPsks_parser)
  : Stack (t b)
    (requires fun h ->
      R.valid r0 h)
    (ensures fun h0 x h1 ->
      B.modifies B.loc_none h0 h1 /\
      valid x h1 /\
      related x r0)
  = admit()

let elim #p #q (#b:LP.slice p q) (x:t b)
  : Stack (R.repr OPSK.offeredPsks b)
    (requires
      valid x)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      related x r)
  = admit()
