module Parsers.TicketContents12.Low
open Parsers.ProtocolVersion
open Parsers.CipherSuite
open Parsers.Boolean
open Parsers.TicketContents12
open Parsers.TicketContents12_master_secret.Low

module HS = FStar.HyperStack
module LP = LowParse.Low
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

friend Parsers.TicketContents12

let valid_ticketContents12_intro h input pos =
  synth_ticketContents12_injective();
  LP.valid_synth h ticketContents12'_parser synth_ticketContents12 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` boolean_parser) ticketContents12_master_secret_parser input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser) boolean_parser input pos;
  LP.valid_nondep_then h protocolVersion_parser cipherSuite_parser input pos
