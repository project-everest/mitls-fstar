module TLS13.ConnectionState.NoCcsRecordAux

(**
  Self-contained record-structure helpers used to discharge the
  `log_has_no_received_ccs` hypothesis of
  `TLS13.ConnectionState.ServerCanonicalShape`.

  Two facts are re-established here (their originals live in
  `TLS13.ConnectionState.Lemmas` but are NOT exported through that module's
  interface):

    * `lemma_raw_records_exactly_segmented`: a byte log parsing as EXACTLY
      `count` records of common outer type `outer` also decomposes RECORD BY
      RECORD (`raw_records_segmented`), a shape amenable to a
      `W.parse_record`-driven induction.

  On top of it we prove the KEY new lemma for the client-output CCS-freeness
  argument:

    * `lemma_segmented_msgs_outer`: if a wire-message list `msgs` serializes to a
      byte log that record-by-record has common outer type `outer`, then EVERY
      message in `msgs` has content type `outer`.

  These are pure spec facts over `TLS13.Wire.Spec` / `TLS13.ConnectionLog` and
  the `TLS13.Spec.Endpoint.Wire` record wire-format instance.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module CW = TLS13.Spec.Endpoint.Wire
module WF = Common.WireFormat
module L = FStar.List.Tot

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Replay

(* ------------------------------------------------------------------ *)
(* Re-proved record-decomposition chain (originals hidden behind the   *)
(* TLS13.ConnectionState.Lemmas interface).                            *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_raw_records_exactly_nonempty_decompose
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         length tail.CL.values == count - 1 /\
         all_records_outer_type outer tail.CL.values))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (parsed.CL.residual == tail.CL.residual);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (all_records_outer_type outer tail.CL.values);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (Seq.equal tail.CL.residual B.empty);
      assert (length tail.CL.values == count - 1);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        (let rest' = Seq.slice raw consumed' (B.length raw) in
         let tail' = CL.parse_record_prefix_fuel (B.length raw) rest' in
         CL.record_stream_serializes rest' tail' /\
         Seq.equal tail'.CL.residual B.empty /\
         length tail'.CL.values == count - 1 /\
         all_records_outer_type outer tail'.CL.values))
    )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_raw_records_exactly_nonempty_decompose_prefix
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        raw_records_exactly
          (Seq.slice raw consumed (B.length raw))
          outer
          (count - 1))
=
  lemma_raw_records_exactly_nonempty_decompose raw outer count;
  match W.parse_record raw with
  | None ->
    assert False
  | Some (content_type, fragment, consumed) ->
    assert (content_type == outer);
    assert (consumed > 0);
    assert (consumed <= B.length raw);
    let rest = Seq.slice raw consumed (B.length raw) in
    let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
    assert (CL.record_stream_serializes rest tail);
    assert (Seq.equal tail.CL.residual B.empty);
    assert (length tail.CL.values == count - 1);
    assert (all_records_outer_type outer tail.CL.values);
    Seq.lemma_len_slice raw consumed (B.length raw);
    assert (consumed + B.length rest == B.length raw);
    assert (B.length rest + 1 <= B.length raw);
    CL.lemma_parse_record_prefix_fuel_eq_parse_record_prefix (B.length raw) rest;
    assert (tail == CL.parse_record_prefix rest);
    let parsed_rest = CL.parse_record_prefix rest in
    assert (raw_records_exactly rest outer (count - 1));
    assert (exists fragment'. exists (consumed':nat).
      W.parse_record raw == Some (outer, fragment', consumed') /\
      consumed' > 0 /\
      consumed' <= B.length raw /\
      raw_records_exactly
        (Seq.slice raw consumed' (B.length raw))
        outer
        (count - 1))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_raw_records_exactly_segmented
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count)
      (ensures raw_records_segmented raw outer count)
      (decreases count)
=
  if count == 0 then (
    let parsed = CL.parse_record_prefix raw in
    assert (CL.record_stream_serializes raw parsed);
    assert (Seq.equal parsed.CL.residual B.empty);
    assert (length parsed.CL.values == 0);
    match parsed.CL.values with
    | [] ->
      assert (CL.serialize_tls_records parsed.CL.values == B.empty);
      assert (parsed.CL.consumed == 0);
      assert (Seq.equal parsed.CL.residual
                        (Seq.slice raw parsed.CL.consumed (B.length raw)));
      Seq.lemma_eq_elim parsed.CL.residual B.empty;
      Seq.lemma_eq_elim
        parsed.CL.residual
        (Seq.slice raw parsed.CL.consumed (B.length raw));
      Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
      assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
      assert (parsed.CL.consumed == 0);
      assert (B.length raw == 0);
      Seq.lemma_eq_intro raw B.empty
    | _ :: _ ->
      assert False
  ) else (
    lemma_raw_records_exactly_nonempty_decompose_prefix raw outer count;
    match W.parse_record raw with
    | None -> assert False
    | Some (content_type, fragment, consumed) ->
      assert (content_type == outer);
      assert (consumed > 0);
      assert (consumed <= B.length raw);
      let rest = Seq.slice raw consumed (B.length raw) in
      assert (raw_records_exactly rest outer (count - 1));
      lemma_raw_records_exactly_segmented rest outer (count - 1);
      assert (raw_records_segmented rest outer (count - 1));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        raw_records_segmented
          (Seq.slice raw consumed' (B.length raw))
          outer
          (count - 1))
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* Wire-format bridge: the record wire-parse of a byte log with a       *)
(* known `parse_record_wire` prefix.                                    *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_parse_record_wire_empty_none (raw:B.bytes)
  : Lemma
      (requires Seq.equal raw B.empty)
      (ensures W.parse_record_wire raw == None)
=
  Seq.lemma_eq_elim raw B.empty;
  match W.parse_record_wire raw with
  | None -> ()
  | Some (ct, frag, consumed) ->
    W.lemma_parse_record_wire_some_consumed_positive raw ct frag consumed
#pop-options

(* ------------------------------------------------------------------ *)
(* KEY LEMMA — record-by-record outer type transfers to every wire      *)
(* message in a decomposition.                                          *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_segmented_msgs_outer
  (raw:B.bytes) (outer:T.content_type) (count:nat) (msgs:list CW.wire_message)
  : Lemma
      (requires
        raw_records_segmented raw outer count /\
        WF.parses_as CW.tls_record_wire_format raw msgs Seq.empty)
      (ensures forall (wm:CW.wire_message).
        L.memP wm msgs ==> wm.CW.wm_content_type == outer)
      (decreases count)
=
  if count = 0 then (
    // raw_records_segmented raw outer 0 == Seq.equal raw B.empty
    match msgs with
    | [] -> ()
    | w :: rest ->
      // parses_as forces wire_parse raw = Some(..) but raw is empty
      lemma_parse_record_wire_empty_none raw;
      CW.lemma_wire_parse_none raw;
      assert (CW.wire_parse raw == None)
  ) else (
    eliminate exists (frag:M.sealed_record) (consumed:nat).
      W.parse_record raw == Some (outer, frag, consumed) /\
      consumed > 0 /\
      consumed <= B.length raw /\
      raw_records_segmented (Seq.slice raw consumed (B.length raw)) outer (count - 1)
    with
    (
      W.lemma_parse_record_implies_parse_record_wire raw;
      assert (W.parse_record_wire raw == Some (outer, frag, consumed));
      match msgs with
      | [] -> ()
      | w :: rest ->
        eliminate exists (parsed:CW.wire_message) (bytes_after:B.bytes).
          CW.wire_parse raw == Some (parsed, bytes_after) /\
          parsed == w /\
          WF.parses_as CW.tls_record_wire_format bytes_after rest Seq.empty
        with
        (
          match W.parse_record_wire raw with
          | None -> ()
          | Some (content_type, fragment, consumed') ->
            W.lemma_parse_record_wire_some_consumed_positive
              raw content_type fragment consumed';
            assert (content_type == outer);
            assert (parsed.CW.wm_content_type == content_type);
            assert (w.CW.wm_content_type == outer);
            assert (bytes_after == Seq.slice raw consumed' (B.length raw));
            assert (WF.parses_as CW.tls_record_wire_format bytes_after rest Seq.empty);
            lemma_segmented_msgs_outer bytes_after outer (count - 1) rest
        )
    )
  )
#pop-options
