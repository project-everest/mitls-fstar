module Parsers.Ticket.Low
open Parsers.ProtocolVersion
open Parsers.CipherSuite
open Parsers.Boolean
open Parsers.TicketContents12
open Parsers.TicketContents13
open Parsers.TicketVersion
open Parsers.TicketContents

module HS = FStar.HyperStack
module LP = LowParse.Low.Base
module LPB = LowParse.Spec.Bytes
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

val write_protocolVersion : LP.leaf_writer_strong protocolVersion_serializer

val write_cipherSuite : LP.leaf_writer_strong cipherSuite_serializer

val write_boolean : LP.leaf_writer_strong boolean_serializer

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

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val finalize_case_ticketContents12
  (input: LP.slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos + 1 <= 4294967295 /\
    LP.valid ticketContents12_parser h input (pos `U32.add` 1ul) // special case because enum values have a constant-size representation here
  ))
  (ensures (fun h pos' h' ->
    let pos1 = pos `U32.add` 1ul in
    B.modifies (LP.loc_slice_from_to input pos pos1) h h' /\
    LP.valid_content_pos
      ticketContents_parser
      h'
      input
      pos
      (Case_ticket12 (LP.contents ticketContents12_parser h input pos1))
      pos'
    /\
    pos' == LP.get_valid_pos ticketContents12_parser h input pos1
  ))

val finalize_case_ticketContents13
  (input: LP.slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos + 1 <= 4294967295 /\
    LP.valid ticketContents13_parser h input (pos `U32.add` 1ul) // special case because enum values have a constant-size representation here
  ))
  (ensures (fun h pos' h' ->
    let pos1 = pos `U32.add` 1ul in
    B.modifies (LP.loc_slice_from_to input pos pos1) h h' /\
    LP.valid_content_pos
      ticketContents_parser
      h'
      input
      pos
      (Case_ticket13 (LP.contents ticketContents13_parser h input pos1))
      pos'
    /\
    pos' == LP.get_valid_pos ticketContents13_parser h input pos1
  ))

val write_ticketContents12_master_secret : LP.leaf_writer_strong ticketContents12_master_secret_serializer
