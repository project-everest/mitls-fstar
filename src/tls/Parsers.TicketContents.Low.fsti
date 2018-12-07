module Parsers.TicketContents.Low
include Parsers.TicketContents12.Low
include Parsers.TicketContents13.Low
include Parsers.TicketContents

module HS = FStar.HyperStack
module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val finalize_case_ticketContents12
  (input: LP.slice)
  (pos: U32.t)
: HST.Stack unit
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
      (LP.get_valid_pos ticketContents12_parser h input pos1)
  ))

val finalize_case_ticketContents13
  (input: LP.slice)
  (pos: U32.t)
: HST.Stack unit
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
      (LP.get_valid_pos ticketContents13_parser h input pos1)
  ))
