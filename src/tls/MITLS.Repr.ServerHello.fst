module MITLS.Repr.ServerHello
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module SH = Parsers.ServerHello
open FStar.Integers
open FStar.HyperStack.ST

let repr #p #q (b:LP.slice p q) =
  R.repr_p SH.serverHello b SH.serverHello_parser

let mk #p #q (b:LP.slice p q) (from to:R.index b)
  : Stack (repr b)
    (requires R.valid_pos b SH.serverHello_parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid r h1)
  = R.mk b from to SH.serverHello_parser

let cipherSuite (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid r)
    (ensures fun h0 cs h1 ->
      B.modifies B.loc_none h0 h1 /\
      cs == SH.((R.value r).cipher_suite))
  = let open R in
    R.reveal_valid();
    let pos = SH.accessor_serverHello_cipher_suite b r.start_pos in
    Parsers.CipherSuite.cipherSuite_reader b pos
