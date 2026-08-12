module TLS13.ConnectionState.ServerNoCcsOutputs

(**
  STEP 5 (CLIENT-log mirror) of the ChangeCipherSpec-freeness derivation.

  A CANONICAL-reachable TLS 1.3 SERVER never emits a wire record whose content
  type is [ChangeCipherSpec].  Concretely, for any trace of official
  [ES.server_step]s, every wire message in [SM.trace_wire_outputs] has
  [wm_content_type <> T.Change_cipher_spec].

  Rationale: the server canonical SEND alphabet is
  { ServerHello, EncryptedExtensions, Certificate, CertificateVerify, Finished,
    ApplicationData, CloseNotify }
  (see [ES.server_local_event_matches]); of these only ServerHello is a cleartext
  send (outer type Handshake) and the rest are protected (outer type
  ApplicationData).  None serializes to a [Change_cipher_spec] record.  Combined
  with [NoCcsRecordAux.lemma_segmented_msgs_outer] this pins every emitted wire
  message's content type away from CCS.

  This is the exact role-swap of [TLS13.ConnectionState.ClientNoCcsOutputs].
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
module ES = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module CTy = TLS13.Impl.CanonicalTypes
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module SMCan = TLS13.Spec.StateMachine.Canonical
module GSH = TLS13.Wire.Generated.ServerHello
module Aux = TLS13.ConnectionState.NoCcsRecordAux
module L = FStar.List.Tot

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Replay

(* ------------------------------------------------------------------ *)
(* Per-message outer-type facts.                                       *)
(* ------------------------------------------------------------------ *)

(** A cleartext handshake message serializes to a single Handshake-typed record
    (or, in the pathological oversize case, to the empty log).  Role-agnostic;
    identical to the client-side helper. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_cleartext_handshake_segmented (hs:M.handshake_msg) (raw:B.bytes)
  : Lemma
      (requires Seq.equal raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hs)))
      (ensures Seq.equal raw B.empty \/ raw_records_segmented raw T.Handshake 1)
=
  W.lemma_serialize_tls_message_handshake hs;
  let frag = W.serialize_handshake hs in
  assert (CS.serialized_cleartext_tls_message (M.TlsHandshake hs) ==
          W.serialize_record T.Handshake frag);
  Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hs));
  assert (raw == W.serialize_record T.Handshake frag);
  if B.length frag <= 16640 then (
    W.lemma_parse_record_serialize_record T.Handshake frag;
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

(** From a legal server-sent byte delta, derive a non-CCS record segmentation of
    that delta. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_sent_delta_segmented
  (st0:CS.connection_state)
  (sem:ES.local_event)
  (msg:CL.directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        ES.server_local_event_matches sem (CS.ConnNetworkEvent msg) /\
        msg.CL.message_direction == CL.Sent /\
        CS.network_message_raw_delta_legal st0.CS.cs_model msg raw)
      (ensures exists (outer:T.content_type) (k:nat).
        outer <> T.Change_cipher_spec /\ raw_records_segmented raw outer k)
=
  if CS.network_message_is_cleartext CL.Sent msg.CL.message_value then (
    // server cleartext send is necessarily a ServerHello
    assert (exists (sh:GSH.serverHello).
      msg.CL.message_value == M.TlsHandshake (M.ServerHello sh));
    eliminate exists (sh:GSH.serverHello).
      msg.CL.message_value == M.TlsHandshake (M.ServerHello sh)
    with
    (
      assert (CS.cleartext_tls_message_raw msg.CL.message_value raw);
      assert (Seq.equal raw
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))));
      lemma_cleartext_handshake_segmented (M.ServerHello sh) raw;
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

(** The server SEND alphabet: a matched server network event is a SENT event and,
    if cleartext, a ServerHello. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_sent_msg_shape
  (sem:ES.local_event)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires ES.server_local_event_matches sem (CS.ConnNetworkEvent msg))
      (ensures
        msg.CL.message_direction == CL.Sent /\
        (CS.network_message_is_cleartext CL.Sent msg.CL.message_value ==>
          (exists (sh:GSH.serverHello).
            msg.CL.message_value == M.TlsHandshake (M.ServerHello sh))))
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
(* Per-step CCS-freeness of the server's wire outputs.                 *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_server_step_outputs_no_ccs
  (st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 ev st1 out)
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
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    with
    (
      // event_raw_delta_legal (Received) forces delta_raw_sent == empty
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        B.empty);
      lemma_outputs_no_ccs_from_empty out.SM.so_wire_outputs
    )
  | SM.LocalEvent local ->
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (ES.server_representation_matches local conn_ev /\
       ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
    with
    (
      // convert the CTy representation to the semantic vocabulary.
      CTy.lemma_server_local_event_semantic_exact local conn_ev;
      // serialize_all so == raw_sent
      Seq.lemma_eq_elim
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        raw_sent;
      assert (CS.legal_connection_delta st0
                { CS.delta_event = conn_ev;
                  CS.delta_raw_sent = raw_sent;
                  CS.delta_raw_received = B.empty; } st1);
      match conn_ev with
      | CS.ConnLocalEvent _ ->
        // event_raw_delta_legal (local) forces raw_sent == empty
        assert (Seq.equal raw_sent B.empty);
        lemma_outputs_no_ccs_from_empty out.SM.so_wire_outputs
      | CS.ConnNetworkEvent msg ->
        lemma_server_sent_msg_shape
          (CTy.server_local_event_semantic local) msg;
        assert (msg.CL.message_direction == CL.Sent);
        // event_raw_delta_legal (Sent) gives network_message_raw_delta_legal
        assert (CS.network_message_raw_delta_legal st0.CS.cs_model msg raw_sent);
        lemma_server_sent_delta_segmented st0
          (CTy.server_local_event_semantic local) msg raw_sent;
        eliminate exists (outer:T.content_type) (k:nat).
          outer <> T.Change_cipher_spec /\ raw_records_segmented raw_sent outer k
        with
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
let rec lemma_server_trace_outputs_ccs_free
  (server_initial:ES.server_initial_state)
  (st0 server:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches
          (ES.server_state_machine #CTy.server_local_event server_initial)
          st0 trace server)
      (ensures forall (wm:CW.wire_message).
        L.memP wm (SM.trace_wire_outputs trace) ==>
        wm.CW.wm_content_type <> T.Change_cipher_spec)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    lemma_server_step_outputs_no_ccs st0 tr.SM.tr_next_state tr.SM.tr_event tr.SM.tr_output;
    lemma_server_trace_outputs_ccs_free server_initial tr.SM.tr_next_state server rest;
    introduce forall (wm:CW.wire_message).
      L.memP wm (SM.trace_wire_outputs trace) ==>
      wm.CW.wm_content_type <> T.Change_cipher_spec
    with (introduce _ ==> _
      with
      L.append_memP tr.SM.tr_output.SM.so_wire_outputs
                    (SM.trace_wire_outputs rest) wm)
#pop-options
