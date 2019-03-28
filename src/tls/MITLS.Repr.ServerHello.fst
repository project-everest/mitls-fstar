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
  = let open R in
    let h = get () in
    let m =
      let v = LP.contents SH.serverHello_parser h b from in
      Ghost.hide ({
        parser_kind = _;
        parser = SH.serverHello_parser;
        value = v
      })
    in
    {
      start_pos = from;
      end_pos = to;
      meta = m
    }

let cipherSuite (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid r)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1)
  = let open R in
    let pos = SH.accessor_serverHello_cipher_suite b r.start_pos in
    Parsers.CipherSuite.cipherSuite_reader b pos
