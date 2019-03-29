module MITLS.Repr.ClientHello
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module CH = Parsers.ClientHello
open FStar.Integers
open FStar.HyperStack.ST

let repr #p #q (b:LP.slice p q) =
  R.repr_p CH.clientHello b CH.clientHello_parser

let mk #p #q (b:LP.slice p q) (from to:R.index b)
  : Stack (repr b)
    (requires R.valid_pos b CH.clientHello_parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid r h1)
  = R.mk b from to CH.clientHello_parser

let version (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.valid r)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == CH.((R.value r).version))
  = let open R in
    R.reveal_valid();
    let pos = CH.accessor_clientHello_version b r.start_pos in
    Parsers.ProtocolVersion.protocolVersion_reader b pos
