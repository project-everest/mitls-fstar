module Parsers.TicketContents13.Low
open Parsers.CipherSuite
open Parsers.TicketContents13

module HS = FStar.HyperStack
module LP = LowParse.Low
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

friend Parsers.TicketContents13


let valid_ticketContents13_intro h input pos =
  let cs = LP.contents cipherSuite_parser h input pos in
  let pos1 = LP.get_valid_pos cipherSuite_parser h input pos in
  let rms = LP.contents ticketContents13_rms_parser h input pos1 in
  let pos2 = LP.get_valid_pos ticketContents13_rms_parser h input pos1 in
  let nonce = LP.contents ticketContents13_nonce_parser h input pos2 in
  let pos3 = LP.get_valid_pos ticketContents13_nonce_parser h input pos2 in
  let creation_time = LP.contents LP.parse_u32 h input pos3 in
  let pos4 = LP.get_valid_pos LP.parse_u32 h input pos3 in
  let age_add = LP.contents LP.parse_u32 h input pos4 in
  let pos5 = LP.get_valid_pos LP.parse_u32 h input pos4 in
  let custom_data = LP.contents ticketContents13_custom_data_parser h input pos5 in
  let pos6 = LP.get_valid_pos ticketContents13_custom_data_parser h input pos5 in
  LP.valid_nondep_then_intro h cipherSuite_parser ticketContents13_rms_parser
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser)
  ticketContents13_nonce_parser
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  ) LP.parse_u32
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  `LP.nondep_then` LP.parse_u32
  ) LP.parse_u32
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  `LP.nondep_then` LP.parse_u32
  `LP.nondep_then` LP.parse_u32
  ) ticketContents13_custom_data_parser input pos;
  assert_norm (ticketContents13' == LP.get_parser_type (
    cipherSuite_parser
    `LP.nondep_then` ticketContents13_rms_parser
    `LP.nondep_then` ticketContents13_nonce_parser
    `LP.nondep_then` LP.parse_u32
    `LP.nondep_then` LP.parse_u32
    `LP.nondep_then` ticketContents13_custom_data_parser
  )); // because of refinements
  synth_ticketContents13_injective ();
  LP.valid_synth_intro h ticketContents13'_parser synth_ticketContents13 input pos
