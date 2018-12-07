module Parsers.TicketContents.Low
open Parsers.TicketContents12.Low
open Parsers.TicketContents13.Low
open Parsers.TicketContents

module HS = FStar.HyperStack
module LP = LowParse.Low
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int
module LPT = LowParse.SLow.Tac.Sum
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

friend Parsers.TicketVersion
friend Parsers.TicketContents

open Parsers.TicketVersion

#push-options "--z3rlimit 16"

let finalize_case_ticketContents12 input pos =
  LP.finalize_sum_case ticketContents_sum ticketVersion_repr_serializer ticketVersion_repr_writer parse_ticketContents_cases (_ by (LPT.enum_repr_of_key_tac (LP.sum_enum ticketContents_sum))) (ticketVersion_as_enum_key Ticket12) input pos

let finalize_case_ticketContents13 input pos =
  LP.finalize_sum_case ticketContents_sum ticketVersion_repr_serializer ticketVersion_repr_writer parse_ticketContents_cases (_ by (LPT.enum_repr_of_key_tac (LP.sum_enum ticketContents_sum))) (ticketVersion_as_enum_key Ticket13) input pos

#pop-options

