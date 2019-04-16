module MITLS.Repr.ClientHello
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ClientHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with clientHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module CH = Parsers.ClientHello
open FStar.Integers
open FStar.HyperStack.ST

let t = CH.clientHello

let repr (b:R.slice) =
  R.repr_p CH.clientHello b CH.clientHello_parser

let version (#b:R.slice) (r:repr b)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.valid r)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == CH.((R.value r).version))
  = let open R in
    R.reveal_valid();
    let pos = CH.accessor_clientHello_version b r.start_pos in
    Parsers.ProtocolVersion.protocolVersion_reader b pos
