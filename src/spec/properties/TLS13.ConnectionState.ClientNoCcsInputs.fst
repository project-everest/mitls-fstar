module TLS13.ConnectionState.ClientNoCcsInputs

(**
  STEP 6 (CLIENT-log mirror) of the ChangeCipherSpec-freeness derivation.

  If a canonical-reachable TLS 1.3 CLIENT consumed only wire records whose
  content type is not [ChangeCipherSpec] (i.e. every wire message in
  [WFSM.trace_input_messages client_trace] has
  [wm_content_type <> T.Change_cipher_spec]), then its connection event log
  contains no received ChangeCipherSpec network event, i.e.
  [CCShape.log_has_no_received_ccs client.cs_event_log].

  Route (per canonical step):
  - A client [WireEvent wire] step appends exactly one connection event
    [ConnNetworkEvent {Received; msg}] to the log (via [legal_connection_delta]).
    If that event were a received CCS ([msg == M.TlsChangeCipherSpec]) then
    [event_raw_delta_legal]/[network_message_raw_delta_legal] force the consumed
    bytes [wire.wm_raw] to equal [serialized_cleartext_tls_message CCS], which by
    the record parse/serialize round-trip pins [wire.wm_content_type ==
    T.Change_cipher_spec] -- contradicting the CCS-free-input hypothesis (the
    wire message is in [event_input_messages]).  Hence [msg <> CCS] and the
    appended event is not a received CCS.
  - A client [LocalEvent local] step appends a connection event matched by
    [client_local_event_matches]; all its network branches force
    [message_direction == Sent], so the appended event is never a received CCS.

  Threading [log_has_no_received_ccs] along the trace (base: the initial log is
  CCS-free) yields the conclusion for the reached state.

  This is the exact role-swap of [TLS13.ConnectionState.ServerNoCcsInputs].  The
  record-structure => content-type tie [lemma_received_ccs_wire_content] is
  role-agnostic; since [ServerNoCcsInputs] has no interface exposing it, it is
  re-proved identically here.
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
module WFSM = Common.WireFormatStateMachine
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module EAPI = TLS13.Spec.Endpoint.API
module CTy = TLS13.Impl.CanonicalTypes
module SMCan = TLS13.Spec.StateMachine.Canonical
module CCShape = TLS13.ConnectionState.ClientCanonicalShape
module L = FStar.List.Tot

open FStar.List.Tot
open TLS13.Spec.StateMachine

(* ------------------------------------------------------------------ *)
(* The record-structure => content-type tie for a received CCS.        *)
(* (Role-agnostic; re-proved identically from ServerNoCcsInputs.)      *)
(* ------------------------------------------------------------------ *)

(** If the bytes consumed by a wire message equal the canonical serialization of
    a ChangeCipherSpec record, then the wire message's content type is
    [T.Change_cipher_spec]. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_received_ccs_wire_content (wire:CW.wire_message)
  : Lemma
      (requires
        Seq.equal (CW.wire_serialize wire)
          (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec))
      (ensures wire.CW.wm_content_type == T.Change_cipher_spec)
=
  W.lemma_serialize_tls_message_change_cipher_spec ();
  let frag = B.singleton 1uy in
  assert (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec ==
          W.serialize_record T.Change_cipher_spec frag);
  assert (CW.wire_serialize wire == wire.CW.wm_raw);
  Seq.lemma_eq_elim wire.CW.wm_raw (W.serialize_record T.Change_cipher_spec frag);
  assert (wire.CW.wm_raw == W.serialize_record T.Change_cipher_spec frag);
  assert (B.length frag == 1);
  W.lemma_parse_record_serialize_record T.Change_cipher_spec frag;
  W.lemma_parse_record_implies_parse_record_wire
    (W.serialize_record T.Change_cipher_spec frag)
#pop-options

(* ------------------------------------------------------------------ *)
(* A matched client LOCAL event is never a received CCS.               *)
(* ------------------------------------------------------------------ *)

(** Every connection event compatible with a client local-event semantics is
    either a local event or a SENT network event -- never a received CCS. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_local_matches_not_received_ccs
  (st:CS.connection_state) (sem:EC.local_event) (conn_ev:CS.conn_event)
  : Lemma
      (requires EC.client_local_event_matches st sem conn_ev)
      (ensures CCShape.is_received_ccs conn_ev == false)
=
  match conn_ev with
  | CS.ConnLocalEvent _ -> ()
  | CS.ConnProtectedHandshake _ -> ()
  | CS.ConnNetworkEvent msg ->
    // for any matching local event, a network event must be SENT
    ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Per-step: the appended connection event is not a received CCS.      *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_step_appends_non_ccs
  (st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        (forall (wm:CW.wire_message).
          L.memP wm (WFSM.event_input_messages ev) ==>
          wm.CW.wm_content_type <> T.Change_cipher_spec))
      (ensures
        (exists (ce:CS.conn_event).
          st1.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
          CCShape.is_received_ccs ce == false))
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists (conn_ev:CS.conn_event).
      (EC.client_wire_received_event st0 wire conn_ev /\
       SMCan.canonical_wire_step st0 st1 conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
         (CW.wire_serialize wire) /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns (exists (ce:CS.conn_event).
      st1.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
      CCShape.is_received_ccs ce == false)
    with _.
    (
      // canonical_wire_step (unfold) gives legal_connection_delta, hence the log
      // append and the received raw-delta legality.
      assert (CS.legal_connection_delta st0
                { CS.delta_event = conn_ev;
                  CS.delta_raw_sent =
                    WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
                  CS.delta_raw_received = CW.wire_serialize wire; } st1);
      assert (st1.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev]);
      assert (L.memP wire (WFSM.event_input_messages ev));
      // rule out a received CCS
      (match conn_ev with
       | CS.ConnProtectedHandshake _ -> ()
       | CS.ConnLocalEvent _ -> ()
       | CS.ConnNetworkEvent dm ->
         (match dm.CL.message_value with
          | M.TlsChangeCipherSpec ->
            // event_raw_delta_legal (Received) => network_message_raw_delta_legal
            assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                      dm
                      (CW.wire_serialize wire));
            assert (Seq.equal (CW.wire_serialize wire)
                      (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec));
            lemma_received_ccs_wire_content wire;
            assert (wire.CW.wm_content_type == T.Change_cipher_spec);
            assert (False)
          | _ -> ()));
      assert (CCShape.is_received_ccs conn_ev == false);
      introduce exists (ce:CS.conn_event).
        st1.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
        CCShape.is_received_ccs ce == false
      with conn_ev and ()
    )
  | SM.LocalEvent local ->
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (EC.client_representation_matches st0 local conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
    returns (exists (ce:CS.conn_event).
      st1.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
      CCShape.is_received_ccs ce == false)
    with _.
    (
      // instance: client_representation_matches == CTy.client_local_event_matches
      CTy.lemma_client_local_event_semantic_exact st0 local conn_ev;
      lemma_client_local_matches_not_received_ccs
        st0 (CTy.client_local_event_semantic local) conn_ev;
      assert (CS.legal_connection_delta st0
                { CS.delta_event = conn_ev;
                  CS.delta_raw_sent = raw_sent;
                  CS.delta_raw_received = B.empty; } st1);
      assert (st1.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev]);
      assert (CCShape.is_received_ccs conn_ev == false);
      introduce exists (ce:CS.conn_event).
        st1.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
        CCShape.is_received_ccs ce == false
      with conn_ev and ()
    )
#pop-options

(* ------------------------------------------------------------------ *)
(* Append preserves CCS-freeness.                                      *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_log_append_non_ccs
  (log:list CS.conn_event) (ce:CS.conn_event)
  : Lemma
      (requires
        CCShape.log_has_no_received_ccs log /\
        CCShape.is_received_ccs ce == false)
      (ensures CCShape.log_has_no_received_ccs (L.append log [ce]))
=
  introduce forall (ev:CS.conn_event).
    L.memP ev (L.append log [ce]) ==> CCShape.is_received_ccs ev == false
  with (introduce _ ==> _
    with _hyp.
    L.append_memP log [ce] ev)
#pop-options

(* ------------------------------------------------------------------ *)
(* STEP 6 -- trace induction.                                          *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_client_no_ccs_event_from_ccs_free_inputs
  (client_initial:EC.client_initial_state)
  (st0 client:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches
          (EC.client_state_machine #CTy.client_local_event client_initial)
          st0 trace client /\
        CCShape.log_has_no_received_ccs st0.CS.cs_event_log /\
        (forall (wm:CW.wire_message).
          L.memP wm (WFSM.trace_input_messages trace) ==>
          wm.CW.wm_content_type <> T.Change_cipher_spec))
      (ensures CCShape.log_has_no_received_ccs client.CS.cs_event_log)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    // per-step input hypothesis and recursion input hypothesis
    introduce forall (wm:CW.wire_message).
      (L.memP wm (WFSM.event_input_messages tr.SM.tr_event) \/
       L.memP wm (WFSM.trace_input_messages rest)) ==>
      wm.CW.wm_content_type <> T.Change_cipher_spec
    with (introduce _ ==> _
      with _hyp.
      L.append_memP (WFSM.event_input_messages tr.SM.tr_event)
                    (WFSM.trace_input_messages rest) wm);
    lemma_client_step_appends_non_ccs
      st0 tr.SM.tr_next_state tr.SM.tr_event tr.SM.tr_output;
    eliminate exists (ce:CS.conn_event).
      tr.SM.tr_next_state.CS.cs_event_log == L.append st0.CS.cs_event_log [ce] /\
      CCShape.is_received_ccs ce == false
    returns CCShape.log_has_no_received_ccs tr.SM.tr_next_state.CS.cs_event_log
    with _.
    (
      lemma_log_append_non_ccs st0.CS.cs_event_log ce
    );
    lemma_client_no_ccs_event_from_ccs_free_inputs
      client_initial tr.SM.tr_next_state client rest
#pop-options
