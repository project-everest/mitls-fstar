module TLS13.Impl.CanonicalWire

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WF = Common.WireFormat
module RVD = TLS13.Wire.Spec.RevealDecode
module WS = TLS13.Wire.Spec
module WU = TLS13.Wire.Spec.Reveal.Util

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

let lemma_wire_parse_serialize_prefix
  (msg:wire_message)
  (tail:B.bytes)
  : Lemma
      (ensures
        exists parsed.
          wire_parse (B.append (wire_serialize msg) tail) ==
            Some (parsed, tail) /\
          parsed == msg)
=
  assert (wire_serialize msg == msg.wm_raw);
  assert (WS.parse_record_wire msg.wm_raw ==
    Some (msg.wm_content_type, msg.wm_fragment, B.length msg.wm_raw));
  let full = B.append msg.wm_raw tail in
  Seq.lemma_len_append msg.wm_raw tail;
  WU.lemma_slice_append_left msg.wm_raw tail;
  Seq.lemma_eq_elim
    (Seq.slice full 0 (B.length msg.wm_raw))
    msg.wm_raw;
  RVD.lemma_parse_record_wire_from_prefix
    full
    msg.wm_content_type
    msg.wm_fragment
    (B.length msg.wm_raw);
  assert (WS.parse_record_wire full ==
    Some (msg.wm_content_type, msg.wm_fragment, B.length msg.wm_raw));
  CL.lemma_raw_slice_append_suffix msg.wm_raw tail;
  assert (CL.raw_slice full (B.length msg.wm_raw) (B.length full) ==
    Seq.slice full (B.length msg.wm_raw) (B.length full));
  Seq.lemma_eq_elim
    tail
    (Seq.slice full (B.length msg.wm_raw) (B.length full));
  match wire_parse full with
  | None ->
    assert False
  | Some (parsed, rest) ->
    assert (rest == tail);
    assert (parsed.wm_raw == msg.wm_raw);
    assert (parsed.wm_content_type == msg.wm_content_type);
    assert (parsed.wm_fragment == msg.wm_fragment);
    assert (parsed == msg);
    assert (exists parsed'.
      wire_parse (B.append (wire_serialize msg) tail) ==
        Some (parsed', tail) /\
      parsed' == msg)

noextract
let tls_record_wire_format_stream_laws
  : WF.wire_format_stream_laws wire_message tls_record_wire_format
  =
  {
    WF.wfsl_parse_serialize_prefix = lemma_wire_parse_serialize_prefix;
  }

let rec lemma_wire_serialize_all_append
  (left right:list wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all tls_record_wire_format (left `FStar.List.Tot.append` right))
          (B.append
            (WF.serialize_all tls_record_wire_format left)
            (WF.serialize_all tls_record_wire_format right)))
      (decreases left)
=
  match left with
  | [] ->
    Seq.append_empty_l (WF.serialize_all tls_record_wire_format right)
  | msg :: tl ->
    lemma_wire_serialize_all_append tl right;
    Seq.append_assoc
      (wire_serialize msg)
      (WF.serialize_all tls_record_wire_format tl)
      (WF.serialize_all tls_record_wire_format right)

let lemma_wire_parse_serialize_with_tail_inverse
  (msgs:list wire_message)
  (tail:B.bytes)
  : Lemma
      (ensures
        WF.parses_as
          tls_record_wire_format
          (WF.serialize_with_tail tls_record_wire_format msgs tail)
          msgs
          tail)
=
  WF.lemma_parse_serialize_with_tail_inverse
    tls_record_wire_format
    tls_record_wire_format_stream_laws
    msgs
    tail

let lemma_wire_parse_serialize_all_inverse
  (msgs:list wire_message)
  : Lemma
      (ensures
        WF.parses_as
          tls_record_wire_format
          (WF.serialize_all tls_record_wire_format msgs)
          msgs
          Seq.empty)
=
  WF.lemma_parse_serialize_all_inverse
    tls_record_wire_format
    tls_record_wire_format_stream_laws
    msgs

let lemma_b_empty_seq_empty ()
  : Lemma (Seq.equal B.empty Seq.empty)
=
  Seq.lemma_eq_intro B.empty Seq.empty

let rec lemma_serialize_with_b_empty_is_serialize_all
  (msgs:list wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_with_tail
            tls_record_wire_format
            msgs
            B.empty)
          (WF.serialize_all tls_record_wire_format msgs))
      (decreases msgs)
=
  match msgs with
  | [] ->
    lemma_b_empty_seq_empty ()
  | _ :: rest ->
    lemma_serialize_with_b_empty_is_serialize_all rest

let rec lemma_wire_parses_as_serialize_with_tail
  (bytes:B.bytes)
  (msgs:list wire_message)
  (residual:B.bytes)
  : Lemma
      (requires
        WF.parses_as
          tls_record_wire_format
          bytes
          msgs
          residual)
      (ensures
        Seq.equal
          bytes
          (WF.serialize_with_tail
            tls_record_wire_format
            msgs
            residual))
      (decreases msgs)
=
  match msgs with
  | [] ->
    assert (Seq.equal bytes residual)
  | msg :: rest ->
    eliminate exists (parsed_msg:wire_message) (bytes_after_msg:B.bytes).
      wire_parse bytes == Some (parsed_msg, bytes_after_msg) /\
      parsed_msg == msg /\
      WF.parses_as
        tls_record_wire_format
        bytes_after_msg
        rest
        residual
    returns
      Seq.equal
        bytes
        (WF.serialize_with_tail
          tls_record_wire_format
          (msg :: rest)
          residual)
    with _.
    (
      match WS.parse_record_wire bytes with
      | None ->
        assert False
      | Some (content_type, fragment, consumed) ->
        WS.lemma_parse_record_wire_some_consumed_positive
          bytes
          content_type
          fragment
          consumed;
        assert (consumed <= B.length bytes);
        assert (parsed_msg.wm_raw == Seq.slice bytes 0 consumed);
        assert (bytes_after_msg == Seq.slice bytes consumed (B.length bytes));
        Seq.lemma_split bytes consumed;
        lemma_wire_parses_as_serialize_with_tail
          bytes_after_msg
          rest
          residual;
        assert (Seq.equal
          bytes_after_msg
          (WF.serialize_with_tail
            tls_record_wire_format
            rest
            residual));
        assert (wire_serialize msg == msg.wm_raw);
        assert (Seq.equal
          (WF.serialize_with_tail
            tls_record_wire_format
            (msg :: rest)
            residual)
          (B.append
            msg.wm_raw
            (WF.serialize_with_tail
              tls_record_wire_format
              rest
              residual)));
        assert (Seq.equal
          bytes
          (B.append
            (Seq.slice bytes 0 consumed)
            (Seq.slice bytes consumed (B.length bytes))));
        assert (Seq.equal
          bytes
          (WF.serialize_with_tail
            tls_record_wire_format
            (msg :: rest)
            residual))
    )

let lemma_wire_parses_as_serialize_all
  (bytes:B.bytes)
  (msgs:list wire_message)
  : Lemma
      (requires
        WF.parses_as
          tls_record_wire_format
          bytes
          msgs
          Seq.empty)
      (ensures
        Seq.equal
          bytes
          (WF.serialize_all tls_record_wire_format msgs))
=
  lemma_wire_parses_as_serialize_with_tail bytes msgs Seq.empty

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
