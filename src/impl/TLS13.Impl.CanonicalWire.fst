module TLS13.Impl.CanonicalWire

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WF = Common.WireFormat
module RVD = TLS13.Wire.Spec.RevealDecode
module WS = TLS13.Wire.Spec

(**
  A Common.WireFormat adapter for raw TLS records.

  The message preserves the exact record bytes consumed from the TCP stream.
  This is important for TLS 1.3 because the server must accept the legacy
  ClientHello record version while the canonical serializer always emits the
  TLS 1.2 record version.  Keeping the raw prefix in the message lets the common
  protocol class account for TCP histories without canonicalizing away those
  audit-relevant bytes.
 **)
noeq
type wire_message = {
  wm_raw: B.bytes;
  wm_content_type: T.content_type;
  wm_fragment: M.sealed_record;
  wm_parse_ok:
    squash
      (WS.parse_record_wire wm_raw ==
        Some (wm_content_type, wm_fragment, B.length wm_raw));
}

let wire_serialize (msg:wire_message) : GTot B.bytes =
  msg.wm_raw

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
    let raw = Seq.slice bytes 0 consumed in
    RVD.lemma_parse_record_wire_prefix bytes content_type fragment consumed;
    let msg = {
      wm_raw = raw;
      wm_content_type = content_type;
      wm_fragment = fragment;
      wm_parse_ok = ();
    } in
    Some (msg, Seq.slice bytes consumed (B.length bytes))

let empty_wire_outputs : list wire_message = []

let wire_outputs_of_full_record (raw:B.bytes) : GTot (list wire_message) =
  if B.length raw == 0 then []
  else
    match WS.parse_record_wire raw with
    | None -> []
    | Some (content_type, fragment, consumed) ->
      if consumed == B.length raw then (
        WS.lemma_parse_record_wire_fragment_bound raw;
        [{
          wm_raw = raw;
          wm_content_type = content_type;
          wm_fragment = fragment;
          wm_parse_ok = ();
        }]
      ) else []

let lemma_wire_parse_serialize_exact
  (msg:wire_message)
  : Lemma
      (ensures
        exists parsed.
          wire_parse (wire_serialize msg) == Some (parsed, Seq.empty) /\
          parsed == msg)
=
  assert (WS.parse_record_wire msg.wm_raw ==
    Some (msg.wm_content_type, msg.wm_fragment, B.length msg.wm_raw));
  WS.lemma_parse_record_wire_fragment_bound msg.wm_raw;
  Seq.lemma_len_slice
    msg.wm_raw
    0
    (B.length msg.wm_raw);
  assert (Seq.equal
    (Seq.slice
      msg.wm_raw
      (B.length msg.wm_raw)
      (B.length msg.wm_raw))
    Seq.empty);
  assert (Seq.equal (Seq.slice msg.wm_raw 0 (B.length msg.wm_raw)) msg.wm_raw);
  assert (exists parsed.
    wire_parse (wire_serialize msg) == Some (parsed, Seq.empty) /\
    parsed == msg)

noextract
let tls_record_wire_format : WF.wire_format wire_message =
{
  WF.wf_serialize = wire_serialize;
  WF.wf_parse = wire_parse;
  WF.wf_parse_serialize_exact = lemma_wire_parse_serialize_exact;
  }

let lemma_wire_outputs_of_empty ()
  : Lemma
      (ensures
        wire_outputs_of_full_record B.empty == [] /\
        Seq.equal
          (WF.serialize_all tls_record_wire_format (wire_outputs_of_full_record B.empty))
          B.empty)
=
  ()

let lemma_wire_outputs_of_full_record_serializes
  (raw:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  : Lemma
      (requires
        WS.parse_record_wire raw == Some (content_type, fragment, B.length raw))
      (ensures
        Seq.equal
          (WF.serialize_all tls_record_wire_format (wire_outputs_of_full_record raw))
          raw)
=
  WS.lemma_parse_record_wire_some_consumed_positive
    raw
    content_type
    fragment
    (B.length raw);
  assert (B.length raw > 0);
  WS.lemma_parse_record_wire_fragment_bound raw;
  match WS.parse_record_wire raw with
  | Some (ct, frag, consumed) ->
    assert (ct == content_type);
    assert (frag == fragment);
    assert (consumed == B.length raw);
    (match wire_outputs_of_full_record raw with
    | [msg] ->
      assert (msg.wm_raw == raw);
      Seq.append_empty_r msg.wm_raw;
      assert (Seq.equal
        (WF.serialize_all tls_record_wire_format [msg])
        raw)
    | _ ->
      assert False)
  | None ->
    assert False
