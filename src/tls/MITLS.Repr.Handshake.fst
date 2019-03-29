module MITLS.Repr.Handshake
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module HSM = Parsers.Handshake
module RCH = MITLS.Repr.ClientHello
module RSH = MITLS.Repr.ServerHello
open FStar.Integers
open FStar.HyperStack.ST

let repr #p #q (b:LP.slice p q) =
  R.repr_p HSM.handshake b HSM.handshake_parser

let mk #p #q (b:LP.slice p q) (from to:R.index b)
  : Stack (repr b)
    (requires R.valid_pos b HSM.handshake_parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid r h1)
  = R.mk b from to HSM.handshake_parser

let handshakeType (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.HandshakeType.handshakeType
    (requires
      R.valid r)
    (ensures fun h0 ht h1 ->
      B.modifies B.loc_none h0 h1 /\
      ht == HSM.tag_of_handshake (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    handshakeType_reader b r.start_pos

let clientHello (#b:LP.slice 'p 'q) (r:repr b)
  : Stack (RCH.repr b)
    (requires fun h ->
      R.valid r h /\
      HSM.tag_of_handshake (R.value r) == Parsers.HandshakeType.Client_hello)
    (ensures fun h0 ch h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid ch h1 /\
      R.value ch == HSM.M_client_hello?._0 (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let pos' = HSM.handshake_accessor_client_hello b r.start_pos in
    assume (LP.valid Parsers.ClientHello.clientHello_parser h b pos');
    let end_pos = Parsers.ClientHello.clientHello_jumper b pos' in
    let ch_repr = RCH.mk b pos' end_pos in
    admit();
    ch_repr

let serverHello (#b:LP.slice 'p 'q) (r:repr b)
  : Stack (RSH.repr b)
    (requires fun h ->
      R.valid r h /\
      HSM.tag_of_handshake (R.value r) == Parsers.HandshakeType.Server_hello)
    (ensures fun h0 sh h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid sh h1 /\
      R.value sh == HSM.M_server_hello?._0 (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let pos' = HSM.handshake_accessor_server_hello b r.start_pos in
    assume (LP.valid Parsers.ServerHello.serverHello_parser h b pos');
    let end_pos = Parsers.ServerHello.serverHello_jumper b pos' in
    let sh_repr = RSH.mk b pos' end_pos in
    admit();
    sh_repr
