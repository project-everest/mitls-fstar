module Parsers.TicketContents12.Low
include Parsers.ProtocolVersion
include Parsers.CipherSuite
include Parsers.Boolean
include Parsers.TicketContents12
include Parsers.TicketContents12_master_secret.Low

module HS = FStar.HyperStack
module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

val valid_ticketContents12_intro
  (h: HS.mem)
  (input: LP.slice)
  (pos: U32.t)
: Lemma
  (requires (
    LP.valid protocolVersion_parser h input pos /\ (
    let pos1 = LP.get_valid_pos protocolVersion_parser h input pos in
    LP.valid cipherSuite_parser h input pos1 /\ (
    let pos2 = LP.get_valid_pos cipherSuite_parser h input pos1 in
    LP.valid boolean_parser h input pos2 /\ (
    let pos3 = LP.get_valid_pos boolean_parser h input pos2 in
    LP.valid ticketContents12_master_secret_parser h input pos3
  )))))
  (ensures (
    let pos1 = LP.get_valid_pos protocolVersion_parser h input pos in
    let pos2 = LP.get_valid_pos cipherSuite_parser h input pos1 in
    let pos3 = LP.get_valid_pos boolean_parser h input pos2 in
    let pos4 = LP.get_valid_pos ticketContents12_master_secret_parser h input pos3 in
    LP.valid_content_pos ticketContents12_parser h input pos
      ({
        pv = LP.contents protocolVersion_parser h input pos;
        Parsers.TicketContents12.cs = LP.contents cipherSuite_parser h input pos1;
        ems = LP.contents boolean_parser h input pos2;
        master_secret = LP.contents ticketContents12_master_secret_parser h input pos3;
      })
      pos4
  ))
