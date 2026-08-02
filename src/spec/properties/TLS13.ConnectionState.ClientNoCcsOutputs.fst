module TLS13.ConnectionState.ClientNoCcsOutputs

(**
  STEP 5 of the server-flight ChangeCipherSpec-freeness derivation.

  A CANONICAL-reachable TLS 1.3 CLIENT never emits a wire record whose content
  type is [ChangeCipherSpec].  Concretely, for any trace of official
  [EC.client_step]s, every wire message in [SM.trace_wire_outputs] has
  [wm_content_type <> T.Change_cipher_spec].

  Rationale: the client canonical SEND alphabet is
  { ClientHello, Finished, ApplicationData, CloseNotify, KeyUpdate }
  (see [EC.client_local_event_matches]); of these only ClientHello is a cleartext
  send (outer type Handshake) and the rest are protected (outer type
  ApplicationData).  None serializes to a [Change_cipher_spec] record.  Combined
  with [NoCcsRecordAux.lemma_segmented_msgs_outer] this pins every emitted wire
  message's content type away from CCS.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module CW = TLS13.Spec.Endpoint.Wire
module WF = Common.WireFormat
module SM = Common.StateMachine
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module EAPI = TLS13.Spec.Endpoint.API
module CTy = TLS13.Impl.CanonicalTypes
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module SMCan = TLS13.Spec.StateMachine.Canonical
module GCH = TLS13.Wire.Generated.ClientHello
module Aux = TLS13.ConnectionState.NoCcsRecordAux
module L = FStar.List.Tot

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Replay

(* ------------------------------------------------------------------ *)
(* Per-message outer-type facts.                                       *)
(* ------------------------------------------------------------------ *)

(** A cleartext handshake message serializes to a single Handshake-typed record
    (or, in the pathological oversize case, to the empty log). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_cleartext_handshake_segmented (hs:M.handshake_msg) (raw:B.bytes)
  : Lemma
      (requires Seq.equal raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hs)))
      (ensures Seq.equal raw B.empty \/ raw_records_segmented raw T.Handshake 1)
=
  W.lemma_serialize_tls_message_handshake hs;
  let frag = W.serialize_handshake hs in
  // serialized_cleartext_tls_message (TlsHandshake hs) == serialize_record Handshake frag
  assert (CS.serialized_cleartext_tls_message (M.TlsHandshake hs) ==
          W.serialize_record T.Handshake frag);
  Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hs));
  assert (raw == W.serialize_record T.Handshake frag);
  if B.length frag <= 16640 then (
    W.lemma_parse_record_serialize_record T.Handshake frag;
    // parse_record raw == Some (Handshake, frag, B.length raw), B.length raw == 5 + len frag
    let consumed = B.length raw in
    assert (W.parse_record raw == Some (T.Handshake, frag, consumed));
    assert (consumed > 0);
    Seq.lemma_len_slice raw consumed (B.length raw);
    assert (Seq.equal (Seq.slice raw consumed (B.length raw)) B.empty);
    assert (raw_records_segmented (Seq.slice raw consumed (B.length raw)) T.Handshake 0);
    assert (raw_records_segmented raw T.Handshake 1)
  ) else (
    W.lemma_serialize_record_oversize T.Handshake frag;
    assert (raw == B.empty);
    Seq.lemma_eq_elim raw B.empty
  )
#pop-options

(** From a legal client-sent byte delta, derive a non-CCS record segmentation of
    that delta. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_sent_delta_segmented
  (st0:CS.connection_state)
  (sem:EC.local_event)
  (msg:CL.directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        EC.client_local_event_matches st0 sem (CS.ConnNetworkEvent msg) /\
        msg.CL.message_direction == CL.Sent /\
        CS.network_message_raw_delta_legal st0.CS.cs_model msg raw)
      (ensures exists (outer:T.content_type) (k:nat).
        outer <> T.Change_cipher_spec /\ raw_records_segmented raw outer k)
=
  if CS.network_message_is_cleartext CL.Sent msg.CL.message_value then (
    // client cleartext send is necessarily a ClientHello
    assert (exists (ch:GCH.clientHello).
      msg.CL.message_value == M.TlsHandshake (M.ClientHello ch));
    eliminate exists (ch:GCH.clientHello).
      msg.CL.message_value == M.TlsHandshake (M.ClientHello ch)
    returns (exists (outer:T.content_type) (k:nat).
      outer <> T.Change_cipher_spec /\ raw_records_segmented raw outer k)
    with _.
    (
      // cleartext_tls_message_raw (ClientHello ch) raw == Seq.equal raw serialized
      assert (CS.cleartext_tls_message_raw msg.CL.message_value raw);
      assert (Seq.equal raw
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))));
      lemma_cleartext_handshake_segmented (M.ClientHello ch) raw;
      // Handshake or empty; both give outer != CCS
      (if Seq.equal raw B.empty then
        assert (raw_records_segmented raw T.Handshake 0)
       else
        assert (raw_records_segmented raw T.Handshake 1));
      assert (T.Handshake <> T.Change_cipher_spec)
    )
  ) else (
    // protected send: all records are ApplicationData
    let count = CS.protected_record_count CL.Sent msg.CL.message_value in
    assert (raw_records_exactly raw T.Application_data count);
    Aux.lemma_raw_records_exactly_segmented raw T.Application_data count;
    assert (raw_records_segmented raw T.Application_data count);
    assert (T.Application_data <> T.Change_cipher_spec)
  )
#pop-options

(** The client SEND alphabet: a matched client network event is a SENT event and,
    if cleartext, a ClientHello. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_sent_msg_shape
  (st0:CS.connection_state)
  (sem:EC.local_event)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires EC.client_local_event_matches st0 sem (CS.ConnNetworkEvent msg))
      (ensures
        msg.CL.message_direction == CL.Sent /\
        (CS.network_message_is_cleartext CL.Sent msg.CL.message_value ==>
          (exists (ch:GCH.clientHello).
            msg.CL.message_value == M.TlsHandshake (M.ClientHello ch))))
=
  ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Serialize-all conclusion.                                            *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_outputs_no_ccs_from_segmented
  (so:list CW.wire_message) (outer:T.content_type) (k:nat)
  : Lemma
      (requires
        outer <> T.Change_cipher_spec /\
        raw_records_segmented
          (WF.serialize_all CW.tls_record_wire_format so) outer k)
      (ensures forall (wm:CW.wire_message).
        L.memP wm so ==> wm.CW.wm_content_type <> T.Change_cipher_spec)
=
  PNTWL.lemma_wire_parse_serialize_all_inverse so;
  Aux.lemma_segmented_msgs_outer
    (WF.serialize_all CW.tls_record_wire_format so) outer k so
#pop-options

(** A byte log that serializes an empty output list. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_outputs_no_ccs_from_empty
  (so:list CW.wire_message)
  : Lemma
      (requires
        Seq.equal (WF.serialize_all CW.tls_record_wire_format so) B.empty)
      (ensures forall (wm:CW.wire_message).
        L.memP wm so ==> wm.CW.wm_content_type <> T.Change_cipher_spec)
=
  assert (raw_records_segmented
    (WF.serialize_all CW.tls_record_wire_format so) T.Handshake 0);
  lemma_outputs_no_ccs_from_segmented so T.Handshake 0
#pop-options

(* ------------------------------------------------------------------ *)
(* Per-step CCS-freeness of the client's wire outputs.                 *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_step_outputs_no_ccs
  (st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 ev st1 out)
      (ensures forall (wm:CW.wire_message).
        L.memP wm out.SM.so_wire_outputs ==>
        wm.CW.wm_content_type <> T.Change_cipher_spec)
=
  match ev with
  | SM.WireEvent wire ->
    // received event: raw_sent (= serialize_all so) forced empty
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received; CL.message_value = msg; } in
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent =
             WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       EC.network_input_message_projection st0 wire msg /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns (forall (wm:CW.wire_message).
      L.memP wm out.SM.so_wire_outputs ==>
      wm.CW.wm_content_type <> T.Change_cipher_spec)
    with _.
    (
      // event_raw_delta_legal (Received) forces delta_raw_sent == empty
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        B.empty);
      lemma_outputs_no_ccs_from_empty out.SM.so_wire_outputs
    )
  | SM.LocalEvent local ->
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (EC.client_local_event_matches st0
         (CTy.client_local_event_semantic local) conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns (forall (wm:CW.wire_message).
      L.memP wm out.SM.so_wire_outputs ==>
      wm.CW.wm_content_type <> T.Change_cipher_spec)
    with _.
    (
      // serialize_all so == raw_sent
      Seq.lemma_eq_elim
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        raw_sent;
      match conn_ev with
      | CS.ConnLocalEvent _ ->
        // event_raw_delta_legal (local) forces raw_sent == empty
        assert (Seq.equal raw_sent B.empty);
        lemma_outputs_no_ccs_from_empty out.SM.so_wire_outputs
      | CS.ConnProtectedHandshake _ ->
        // event_raw_delta_legal (protected handshake) forces raw_sent == empty
        assert (Seq.equal raw_sent B.empty);
        lemma_outputs_no_ccs_from_empty out.SM.so_wire_outputs
      | CS.ConnNetworkEvent msg ->
        lemma_client_sent_msg_shape st0
          (CTy.client_local_event_semantic local) msg;
        assert (msg.CL.message_direction == CL.Sent);
        // event_raw_delta_legal (Sent) gives network_message_raw_delta_legal
        assert (CS.network_message_raw_delta_legal st0.CS.cs_model msg raw_sent);
        lemma_client_sent_delta_segmented st0
          (CTy.client_local_event_semantic local) msg raw_sent;
        eliminate exists (outer:T.content_type) (k:nat).
          outer <> T.Change_cipher_spec /\ raw_records_segmented raw_sent outer k
        returns (forall (wm:CW.wire_message).
          L.memP wm out.SM.so_wire_outputs ==>
          wm.CW.wm_content_type <> T.Change_cipher_spec)
        with _.
        (
          assert (raw_records_segmented
            (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
            outer k);
          lemma_outputs_no_ccs_from_segmented out.SM.so_wire_outputs outer k
        )
    )
#pop-options

(* ------------------------------------------------------------------ *)
(* STEP 5 — trace induction.                                           *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_client_trace_outputs_ccs_free
  (client_initial:EC.client_initial_state)
  (st0 client:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches
          (EC.client_state_machine #CTy.client_local_event client_initial)
          st0 trace client)
      (ensures forall (wm:CW.wire_message).
        L.memP wm (SM.trace_wire_outputs trace) ==>
        wm.CW.wm_content_type <> T.Change_cipher_spec)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    lemma_client_step_outputs_no_ccs st0 tr.SM.tr_next_state tr.SM.tr_event tr.SM.tr_output;
    lemma_client_trace_outputs_ccs_free client_initial tr.SM.tr_next_state client rest;
    introduce forall (wm:CW.wire_message).
      L.memP wm (SM.trace_wire_outputs trace) ==>
      wm.CW.wm_content_type <> T.Change_cipher_spec
    with (introduce _ ==> _
      with _hyp.
      L.append_memP tr.SM.tr_output.SM.so_wire_outputs
                    (SM.trace_wire_outputs rest) wm)
#pop-options
