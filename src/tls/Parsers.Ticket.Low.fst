module Parsers.Ticket.Low
open Parsers.ProtocolVersion
open Parsers.CipherSuite
open Parsers.Boolean
open Parsers.TicketContents12
open Parsers.TicketContents13
open Parsers.TicketVersion
open Parsers.TicketContents

module HS = FStar.HyperStack
module LP = LowParse.Low
module LPT = LowParse.SLow.Tac.Enum
module LPB = LowParse.Spec.Bytes
module U32 = FStar.UInt32

friend Parsers.ProtocolVersion
friend Parsers.CipherSuite
friend Parsers.Boolean
friend Parsers.TicketContents12
friend Parsers.TicketContents13
friend Parsers.TicketVersion
friend Parsers.TicketContents

let write_protocolVersion =
  lemma_synth_protocolVersion_inj ();
  lemma_synth_protocolVersion_inv ();
  LP.write_synth
    (LP.write_maybe_enum_key LP.write_u16 protocolVersion_enum (_ by (LPT.enum_repr_of_key_tac protocolVersion_enum)))
    synth_protocolVersion
    synth_protocolVersion_inv
    (fun x -> synth_protocolVersion_inv x)
    ()

let write_cipherSuite =
  lemma_synth_cipherSuite_inj ();
  lemma_synth_cipherSuite_inv ();
  LP.write_synth
    (LP.write_maybe_enum_key LP.write_u16 cipherSuite_enum (_ by (LPT.enum_repr_of_key_tac cipherSuite_enum)))
    synth_cipherSuite
    synth_cipherSuite_inv
    (fun x -> synth_cipherSuite_inv x)
    ()

let write_boolean =
  lemma_synth_boolean_inj ();
  lemma_synth_boolean_inv ();
  LP.write_synth
    (LP.write_enum_key LP.write_u8 boolean_enum (_ by (LPT.enum_repr_of_key_tac boolean_enum)))
    synth_boolean
    synth_boolean_inv
    (fun x -> synth_boolean_inv x)
    ()

#reset-options "--max_fuel 0 --max_ifuel 0"

let valid_ticketContents12_intro h input pos =
  synth_ticketContents12_injective();
  LP.valid_synth h ticketContents12'_parser synth_ticketContents12 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` boolean_parser) ticketContents12_master_secret_parser input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser) boolean_parser input pos;
  LP.valid_nondep_then h protocolVersion_parser cipherSuite_parser input pos

#set-options "--z3rlimit 16 --print_z3_statistics"

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

inline_for_extraction
let write_ticketVersion_key : LP.leaf_writer_strong serialize_ticketVersion_key =
  LP.write_enum_key LP.write_u8 ticketVersion_enum (_ by (LPT.enum_repr_of_key_tac ticketVersion_enum))

inline_for_extraction
let jump_ticketContents12 : LP.jumper ticketContents12_parser =
  LP.jump_constant_size ticketContents12_parser 53ul ()

#reset-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --print_z3_statistics --z3refresh --using_facts_from '* -Parsers +Parsers.Ticket.Low +Parsers.TicketContents12 +Parsers.TicketVersion +Parsers.TicketContents -LowParse +LowParse.Spec.Base +LowParse.Low.Base +LowParse.Spec.Combinators +LowParse.Spec.Enum +LowParse.Spec.Sum +LowParse.Low.Sum -FStar.Tactics -FStar.Reflection' --print_implicits"

let finalize_case_ticketContents12 input pos =
  [@inline_let] let _ =
    assert_norm (LP.list_mem Ticket12 (LP.list_map fst ticketVersion_enum) == true);
    assert_norm ((LP.get_parser_kind parse_ticketVersion_key).LP.parser_kind_low == 1);
    assert_norm ((LP.get_parser_kind parse_ticketVersion_key).LP.parser_kind_high == Some 1)
  in
  let pos1 = write_ticketVersion_key Ticket12 input pos in
  let h = HST.get () in
  [@inline_let] let _ =
    LP.valid_sum_intro h ticketContents_sum ticketVersion_repr_parser parse_ticketContents_cases input pos
  in
  [@inline_let] let _ = assert_norm (LP.parse_sum_kind (LP.get_parser_kind ticketVersion_repr_parser) ticketContents_sum parse_ticketContents_cases == ticketContents_parser_kind) in
  jump_ticketContents12 input pos1

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 16 --print_z3_statistics"

inline_for_extraction
let jump_ticketContents13 : LP.jumper ticketContents13_parser =
  assert_norm (ticketContents13' == LP.get_parser_type (
    cipherSuite_parser
    `LP.nondep_then` ticketContents13_rms_parser
    `LP.nondep_then` ticketContents13_nonce_parser
    `LP.nondep_then` LP.parse_u32
    `LP.nondep_then` LP.parse_u32
    `LP.nondep_then` ticketContents13_custom_data_parser
  )); // because of refinements
  synth_ticketContents13_injective ();
  LP.jump_synth
    (LP.jump_constant_size cipherSuite_parser 2ul ()
    `LP.jump_nondep_then`
    LP.jump_bounded_vlbytes 32 255
    `LP.jump_nondep_then`
    LP.jump_bounded_vlbytes 0 255
    `LP.jump_nondep_then`
    LP.jump_u32
    `LP.jump_nondep_then`
    LP.jump_u32
    `LP.jump_nondep_then`
    LP.jump_bounded_vlbytes 0 65535)
    synth_ticketContents13
    ()

#reset-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --print_z3_statistics --z3refresh --using_facts_from '* -Parsers +Parsers.Ticket.Low +Parsers.TicketContents13 +Parsers.TicketVersion +Parsers.TicketContents -LowParse +LowParse.Spec.Base +LowParse.Low.Base +LowParse.Spec.Combinators +LowParse.Spec.Enum +LowParse.Spec.Sum +LowParse.Low.Sum -FStar.Tactics -FStar.Reflection' --print_implicits"

let finalize_case_ticketContents13 input pos =
  [@inline_let] let _ =
    assert_norm (LP.list_mem Ticket13 (LP.list_map fst ticketVersion_enum) == true);
    assert_norm ((LP.get_parser_kind parse_ticketVersion_key).LP.parser_kind_low == 1);
    assert_norm ((LP.get_parser_kind parse_ticketVersion_key).LP.parser_kind_high == Some 1)
  in
  let pos1 = write_ticketVersion_key Ticket13 input pos in
  let h = HST.get () in
  [@inline_let] let _ =
    LP.valid_sum_intro h ticketContents_sum ticketVersion_repr_parser parse_ticketContents_cases input pos
  in
  [@inline_let] let _ = assert_norm (LP.parse_sum_kind (LP.get_parser_kind ticketVersion_repr_parser) ticketContents_sum parse_ticketContents_cases == ticketContents_parser_kind) in
  jump_ticketContents13 input pos1
