module MITLS.Repr.ServerHello
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ServerHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with serverHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module SH = Parsers.ServerHello
open FStar.Integers
open FStar.HyperStack.ST

let t = SH.serverHello

let repr (b:R.slice) =
  R.repr_p SH.serverHello b SH.serverHello_parser

let cipherSuite (#b:R.slice) (r:repr b)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid r)
    (ensures fun h0 cs h1 ->
      B.modifies B.loc_none h0 h1 /\
      cs == SH.((R.value r).cipher_suite))
  = let open R in
    R.reveal_valid();
    let pos = SH.accessor_serverHello_cipher_suite b r.start_pos in
    Parsers.CipherSuite.cipherSuite_reader b pos
