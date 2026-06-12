module TLS13.Wire.Spec.NonExact
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

(* The non-exact-consumption soundness lemma for the Handshake arm of
   [TLS13.Wire.Spec.parse_tls_message].  When the QuackyDucky handshake parser
   succeeds but does not consume the whole record fragment, the spec yields
   [None].  Proving this requires opening the generated grammar to expose the
   1-byte message-type tag, hence the [friend] declarations above. *)

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec
module LPI = LowParse.Spec.Int
module LPE = LowParse.Spec.Enum
module LPSum = LowParse.Spec.Sum

(* The message-type byte parsed by the handshake grammar is never the
   NewSessionTicket tag (4): that handshake case carries an uninhabited payload
   ([squash False]) so its case parser always fails. *)
let lemma_handshake_tag_not_nst
  (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed))
    (ensures B.length fragment >= 1 /\ U8.v (Seq.index fragment 0) <> 4)
=
  LPSum.parse_sum_eq'' GHS.handshake_sum HT.handshakeType_repr_parser GHS.parse_handshake_cases fragment;
  match LP.parse HT.handshakeType_repr_parser fragment with
  | None -> ()
  | Some (k', ck) ->
    LP.parser_kind_prop_equiv LPI.parse_u8_kind HT.handshakeType_repr_parser;
    assert (B.length fragment >= 1);
    LPI.parse_u8_spec' fragment;
    assert (k' == Seq.index fragment 0);
    if U8.v (Seq.index fragment 0) = 4 then begin
      assert (k' == 4uy);
      assert_norm (LP.sum_enum GHS.handshake_sum == HT.handshakeType_enum);
      assert_norm (LPE.maybe_enum_key_of_repr HT.handshakeType_enum 4uy == LPE.Known HT.New_session_ticket);
      assert_norm (FStar.Pervasives.dsnd (GHS.parse_handshake_cases HT.New_session_ticket) == LP.parse_false);
      LP.parser_kind_prop_equiv LP.parse_false_kind LP.parse_false
    end else ()

let lemma_ptm_handshake_nonexact_none
  (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              consumed <> B.length fragment)
    (ensures WS.parse_tls_message T.Handshake fragment == None)
=
  lemma_handshake_tag_not_nst fragment v consumed;
  LP.parser_kind_prop_equiv GHS.handshake_parser_kind GHS.handshake_parser;
  assert (consumed >= 5);
  assert (B.length fragment > 5)
