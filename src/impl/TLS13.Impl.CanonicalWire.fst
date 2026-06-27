module TLS13.Impl.CanonicalWire

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WF = Common.WireFormat
module WS = TLS13.Wire.Spec

(**
  A first canonical Common.WireFormat adapter for TLS records.

  The message is the parsed TLS record together with the standard TLS record
  fragment bound.  The parser uses [parse_record_wire], so it accepts the
  legacy-version ClientHello record form used by the low-level endpoint
  decoders.  Serialization is canonical TLS record serialization; this module
  intentionally does not yet preserve the exact raw bytes of legacy-version
  records.  See the canonical protocol modules for the role-specific boundary
  definitions and the remaining raw-byte proof obligations.
 **)
type wire_message = r:M.tls_record { B.length r.M.record_fragment <= 16640 }

let wire_equal (x y:wire_message) : GTot prop =
  x.M.record_outer_type == y.M.record_outer_type /\
  Seq.equal x.M.record_fragment y.M.record_fragment

let wire_serialize (msg:wire_message) : GTot B.bytes =
  WS.serialize_record msg.M.record_outer_type msg.M.record_fragment

let wire_parse (bytes:B.bytes) : GTot (WF.parse_result wire_message) =
  match WS.parse_record_wire bytes with
  | None -> None
  | Some (content_type, fragment, consumed) ->
    WS.lemma_parse_record_wire_fragment_bound bytes;
    WS.lemma_parse_record_wire_some_consumed_positive
      bytes
      content_type
      fragment
      consumed;
    let msg : wire_message = {
      M.record_outer_type = content_type;
      M.record_fragment = fragment;
    } in
    Some (msg, Seq.slice bytes consumed (B.length bytes))

let lemma_wire_parse_serialize_exact
  (msg:wire_message)
  : Lemma
      (ensures
        exists parsed.
          wire_parse (wire_serialize msg) == Some (parsed, Seq.empty) /\
          wire_equal parsed msg)
=
  WS.lemma_parse_record_serialize_record
    msg.M.record_outer_type
    msg.M.record_fragment;
  WS.lemma_parse_record_implies_parse_record_wire (wire_serialize msg);
  WS.lemma_parse_record_wire_fragment_bound (wire_serialize msg);
  assert (WS.parse_record_wire (wire_serialize msg) ==
    Some (
      msg.M.record_outer_type,
      msg.M.record_fragment,
      B.length (wire_serialize msg)));
  Seq.lemma_len_slice
    (wire_serialize msg)
    (B.length (wire_serialize msg))
    (B.length (wire_serialize msg));
  assert (Seq.equal
    (Seq.slice
      (wire_serialize msg)
      (B.length (wire_serialize msg))
      (B.length (wire_serialize msg)))
    Seq.empty);
  assert (exists parsed.
    wire_parse (wire_serialize msg) == Some (parsed, Seq.empty) /\
    wire_equal parsed msg)

noextract
let tls_record_wire_format : WF.wire_format wire_message =
  {
    WF.wf_equal = wire_equal;
    WF.wf_serialize = wire_serialize;
    WF.wf_parse = wire_parse;
    WF.wf_parse_serialize_exact = lemma_wire_parse_serialize_exact;
  }
