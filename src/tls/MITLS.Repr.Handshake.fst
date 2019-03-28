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

let handshakeType (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.HandshakeType.handshakeType
    (requires
      R.valid r)
    (ensures fun h0 _ h1 ->
      B.modifies B.loc_none h0 h1)
  = let open R in
    let open Parsers.HandshakeType in
    handshakeType_reader b r.start_pos

let clientHello (#b:LP.slice 'p 'q) (r:repr b)
  : Stack (option (RCH.repr b))
    (requires
      R.valid r)
    (ensures fun h0 ch h1 ->
      B.modifies B.loc_none h0 h1 /\
      (Some? ch ==> R.valid (Some?.v ch) h1))
  = let open R in
    let open Parsers.HandshakeType in
    let tag = handshakeType_reader b r.start_pos in
    match tag with
    | Client_hello ->
      let h = get () in
      let pos' = HSM.handshake_accessor_client_hello b r.start_pos in
      assume (LP.valid Parsers.ClientHello.clientHello_parser h b pos');
      let end_pos = Parsers.ClientHello.clientHello_jumper b pos' in
      let ch_repr = RCH.mk b pos' end_pos in
      Some ch_repr
    | _ -> None

let serverHello (#b:LP.slice 'p 'q) (r:repr b)
  : Stack (option (RSH.repr b))
    (requires
      R.valid r)
    (ensures fun h0 sh h1 ->
      B.modifies B.loc_none h0 h1 /\
      (Some? sh ==> R.valid (Some?.v sh) h1))
  = let open R in
    let open Parsers.HandshakeType in
    let tag = handshakeType_reader b r.start_pos in
    match tag with
    | Server_hello ->
      let h = get () in
      let pos' = HSM.handshake_accessor_server_hello b r.start_pos in
      assume (LP.valid Parsers.ServerHello.serverHello_parser h b pos');
      let end_pos = Parsers.ServerHello.serverHello_jumper b pos' in
      let sh_repr = RSH.mk b pos' end_pos in
      Some sh_repr
    | _ -> None
