module Parsers.TicketContents13.Low
include Parsers.CipherSuite
include Parsers.TicketContents13

module HS = FStar.HyperStack
module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

val valid_ticketContents13_intro
  (h: HS.mem)
  (input: LP.slice)
  (pos: U32.t)
: Lemma
  (requires (
    LP.valid cipherSuite_parser h input pos /\ (
    let pos1 = LP.get_valid_pos cipherSuite_parser h input pos in
    LP.valid ticketContents13_rms_parser h input pos1 /\ (
    let pos2 = LP.get_valid_pos ticketContents13_rms_parser h input pos1 in
    LP.valid ticketContents13_nonce_parser h input pos2 /\ (
    let pos3 = LP.get_valid_pos ticketContents13_nonce_parser h input pos2 in
    LP.valid LPI.parse_u32 h input pos3 /\ (
    let pos4 = LP.get_valid_pos LPI.parse_u32 h input pos3 in
    LP.valid LPI.parse_u32 h input pos4 /\ (
    let pos5 = LP.get_valid_pos LPI.parse_u32 h input pos4 in
    LP.valid ticketContents13_custom_data_parser h input pos5
  )))))))
  (ensures (
    let pos1 = LP.get_valid_pos cipherSuite_parser h input pos in
    let pos2 = LP.get_valid_pos ticketContents13_rms_parser h input pos1 in
    let pos3 = LP.get_valid_pos ticketContents13_nonce_parser h input pos2 in
    let pos4 = LP.get_valid_pos LPI.parse_u32 h input pos3 in
    let pos5 = LP.get_valid_pos LPI.parse_u32 h input pos4 in
    LP.valid_content_pos ticketContents13_parser h input pos
      ({
        cs = LP.contents cipherSuite_parser h input pos;
        rms = LP.contents ticketContents13_rms_parser h input pos1;
        nonce = LP.contents ticketContents13_nonce_parser h input pos2;
        creation_time = LP.contents LPI.parse_u32 h input pos3;
        age_add = LP.contents LPI.parse_u32 h input pos4;
        custom_data = LP.contents ticketContents13_custom_data_parser h input pos5;
      })
      (LP.get_valid_pos ticketContents13_custom_data_parser h input pos5)
  ))
