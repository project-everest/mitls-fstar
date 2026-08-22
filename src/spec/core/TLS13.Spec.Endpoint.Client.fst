module TLS13.Spec.Endpoint.Client

module API = TLS13.Spec.Endpoint.API
module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SM = Common.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module W = TLS13.Spec.Endpoint.Wire
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module X = TLS13.X509.Spec

(**
  Pure client-endpoint vocabulary and state machine.

  The local-event constructors describe semantic client actions.  In
  particular, they are independent of the extraction ABI enum used by the
  concrete client.  [client_step] is polymorphic in an implementation event
  representation and accepts an explicit total projection into this vocabulary.
 **)

type local_event =
  | ClientStartHandshake
  | ClientDeriveSharedSecret
  | ClientInstallClientHandshakeTrafficKeys
  | ClientInstallServerHandshakeTrafficKeys
  | ClientInstallClientApplicationTrafficKeys
  | ClientInstallServerApplicationTrafficKeys
  | ClientValidateCertificate of B.bytes
  | ClientVerifyCertificateSignature
  | ClientVerifyFinished
  | ClientDeliverApplicationData of B.bytes
  | ClientSendClientHello
  | ClientSendClientFinished
  | ClientSendApplicationData of B.bytes
  (**
    Send a KeyUpdate.  The request form is part of the action: a client may
    answer a peer's [update_requested] with [update_not_requested], and may
    also rotate spontaneously with either form (RFC 8446 §4.6.3).
   **)
  | ClientSendKeyUpdate of M.key_update_request
  | ClientSendCloseNotify
  | ClientFail
  (**
    Internal event: process one handshake message already retained in the
    pending-plaintext buffer.  It consumes no wire input and produces no wire
    output; the message it processes is determined by the pending buffer, not
    by the event.
   **)
  | ClientProcessPendingHandshake

let validation_peer
  (st:CS.connection_state)
  (payload:B.bytes)
  : X.peer_identity =
  {
    X.validated_hostname =
      st.CS.cs_model.CS.model_config.CS.config_server_name;
    X.leaf_public_key = payload;
    X.permitted_signature_schemes = [];
  }

let client_local_event_matches
  (st:CS.connection_state)
  (local:local_event)
  (ev:CS.conn_event)
  : prop =
  match local, ev with
  | ClientDeliverApplicationData payload,
    CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) ->
      Seq.equal bytes payload
  | ClientSendApplicationData payload, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsApplicationData bytes -> Seq.equal bytes payload
       | _ -> False)
  | ClientSendClientHello, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.ClientHello _) -> True
       | _ -> False)
  | ClientSendClientFinished, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.Finished _) -> True
       | _ -> False)
  | ClientSendCloseNotify, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      msg.CL.message_value == M.TlsAlert TLS13.Types.Close_notify
  | ClientSendKeyUpdate req, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      msg.CL.message_value == M.TlsKeyUpdate req
  | ClientStartHandshake,
    CS.ConnLocalEvent (CS.LocalStartHandshake _) ->
      True
  | ClientDeriveSharedSecret,
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) ->
      True
  | ClientInstallClientHandshakeTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      install.CS.install_epoch == CS.TrafficHandshake /\
      install.CS.install_direction == CS.TrafficWrite
  | ClientInstallServerHandshakeTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      install.CS.install_epoch == CS.TrafficHandshake /\
      install.CS.install_direction == CS.TrafficRead
  | ClientInstallClientApplicationTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      install.CS.install_epoch == CS.TrafficApplication /\
      install.CS.install_direction == CS.TrafficWrite
  | ClientInstallServerApplicationTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      install.CS.install_epoch == CS.TrafficApplication /\
      install.CS.install_direction == CS.TrafficRead
  | ClientValidateCertificate payload,
    CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ->
      peer == validation_peer st payload
  | ClientVerifyCertificateSignature,
    CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ->
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv
  | ClientVerifyFinished,
    CS.ConnLocalEvent (CS.LocalVerifyFinished _) ->
      True
  | ClientFail, CS.ConnLocalEvent (CS.LocalFail _) ->
      True
  | ClientProcessPendingHandshake, CS.ConnProtectedHandshake step ->
      step.CS.protected_handshake_head == false
  | _, _ ->
      False

class client_event_representation (a:Type0) = {
  client_event_semantic: a -> GTot local_event;
  client_representation_matches:
    CS.connection_state -> a -> CS.conn_event -> prop;
  client_representation_exact:
    st:CS.connection_state ->
    input:a ->
    ev:CS.conn_event ->
      Lemma
        (client_representation_matches st input ev <==>
         client_local_event_matches st (client_event_semantic input) ev);
}

let client_local_outputs_match
  (ev:CS.conn_event)
  (outs:list API.local_output)
  : prop =
  API.local_outputs_match ev outs

let client_wire_outputs_match
  (raw_sent:B.bytes)
  (outs:list W.wire_message)
  : prop =
  Seq.equal
    (WF.serialize_all W.tls_record_wire_format outs)
    raw_sent

(**
  Representation-independent meaning of a successfully decoded client network
  input.  Cleartext messages are tied to their exact raw-record representation;
  protected messages are tied to the record-layer open and inner-message decode.
 **)
let network_input_message_projection
  (st0:CS.connection_state)
  (wire:W.wire_message)
  (msg:M.tls_message)
  : prop =
  if CS.network_message_is_cleartext CL.Received msg
  then CS.received_cleartext_tls_message_raw msg (W.wire_serialize wire)
  else
    SMCan.received_single_protected_message_decode
      st0.CS.cs_model
      msg
      (W.wire_serialize wire)

(**
  The connection event a client's receipt of one record may induce.

  Either a semantic received message — a cleartext message, or a protected
  record whose plaintext is a single non-handshake message — or the *head* step
  of a protected handshake record, whose remaining plaintext is retained as
  pending state and drained by subsequent internal events.

  Both shapes describe exactly one physical record: [event_raw_delta_legal]
  pins a head [ConnProtectedHandshake] to [raw_records_exactly _
  Application_data 1], and a received [ConnNetworkEvent] to its own raw shape.
  Having one [WireEvent] case covering both is what removes the receive-path
  fork; see INTERNAL_EVENT_PLAN.md §1.1.
 **)
let client_wire_received_event
  (st0:CS.connection_state)
  (wire:W.wire_message)
  (conn_ev:CS.conn_event)
  : GTot prop =
  match conn_ev with
  | CS.ConnNetworkEvent tm ->
    tm.CL.message_direction == CL.Received /\
    network_input_message_projection st0 wire tm.CL.message_value
  | CS.ConnProtectedHandshake step ->
    step.CS.protected_handshake_head == true
  (* A CLIENT buffers cleartext handshake bytes for exactly one message: the
     ServerHello.  A server that sizes its records below the hello -- a large
     key share, a long cookie, HelloRetryRequest material -- splits it, and a
     client that refuses the split cannot talk to that server at all.  The rule
     is therefore the same one the server has for the ClientHello
     ([TLS13.Spec.Endpoint.Server.server_wire_received_event]); the asymmetry
     that used to be recorded here was an implementation gap, not a protocol
     fact. *)
  | CS.ConnCleartextHandshake _ -> True
  | CS.ConnLocalEvent _ -> False

(** A client wire step whose POST-state buffer is EMPTY cannot have been a
    cleartext buffering step: [legal_cleartext_handshake_step] insists the
    buffered fragment is non-empty, so the post-state stream
    [pending ++ fragment] is non-empty too.

    The exact mirror of
    [TLS13.Spec.Endpoint.Server.lemma_wire_received_event_empty_buffer_not_buffering],
    except that the client has a THIRD shape to leave standing: a protected
    handshake head.  So the conclusion is a disjunction rather than a single
    case. **)
let lemma_client_wire_received_event_empty_buffer_not_buffering
  (st0:CS.connection_state)
  (wire:W.wire_message)
  (conn_ev:CS.conn_event)
  (m1:CS.connection_model)
  : Lemma
      (requires
        client_wire_received_event st0 wire conn_ev /\
        CS.step_model st0.CS.cs_model conn_ev == Some m1 /\
        CS.cleartext_handshake_buffer_empty m1)
      (ensures
        (CS.ConnNetworkEvent? conn_ev /\
         (CS.ConnNetworkEvent?._0 conn_ev).CL.message_direction == CL.Received /\
         network_input_message_projection
           st0 wire (CS.ConnNetworkEvent?._0 conn_ev).CL.message_value) \/
        (CS.ConnProtectedHandshake? conn_ev /\
         (CS.ConnProtectedHandshake?._0 conn_ev).CS.protected_handshake_head == true))
  = match conn_ev with
    | CS.ConnCleartextHandshake step ->
      Seq.lemma_len_append
        (CS.pending_cleartext_handshake st0.CS.cs_model)
        step.CS.cleartext_handshake_fragment;
      assert (0 < B.length (CS.cleartext_handshake_stream st0.CS.cs_model step));
      assert (Seq.equal (CS.pending_cleartext_handshake m1)
                        (CS.cleartext_handshake_stream st0.CS.cs_model step))
    | _ -> ()

let client_step
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0:CS.connection_state)
  (ev:SM.event W.wire_message local_event_repr)
  (st1:CS.connection_state)
  (out:SM.step_output W.wire_message API.local_output)
  : GTot prop =
  match ev with
  | SM.WireEvent wire ->
    exists conn_ev.
      client_wire_received_event st0 wire conn_ev /\
      SMCan.canonical_wire_step
        st0
        st1
        conn_ev
        (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
        (W.wire_serialize wire) /\
      client_local_outputs_match conn_ev out.SM.so_local_outputs
  | SM.LocalEvent local ->
    exists conn_ev raw_sent.
      client_representation_matches st0 local conn_ev /\
      client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step
        st0
        st1
        conn_ev
        raw_sent
        B.empty

(** THE REUSABLE VACUITY HOOK.  Every site that inverts a client wire step into
    its [conn_event] and pins the POST-state cleartext buffer empty can dispose
    of the [ConnCleartextHandshake] arm with a single call to this lemma.

    Stated over [SMCan.canonical_wire_step] rather than over [client_step] so
    that it applies inside an already-eliminated existential, which is the shape
    all those sites are in. **)
let lemma_client_wire_step_not_cleartext_buffering
  (st0 st1:CS.connection_state)
  (conn_ev:CS.conn_event)
  (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        SMCan.canonical_wire_step st0 st1 conn_ev raw_sent raw_received /\
        CS.cleartext_handshake_buffer_empty st1.CS.cs_model)
      (ensures ~(CS.ConnCleartextHandshake? conn_ev))
  = match conn_ev with
    | CS.ConnCleartextHandshake step ->
      Seq.lemma_len_append
        (CS.pending_cleartext_handshake st0.CS.cs_model)
        step.CS.cleartext_handshake_fragment;
      assert (0 < B.length (CS.cleartext_handshake_stream st0.CS.cs_model step));
      assert (Seq.equal (CS.pending_cleartext_handshake st1.CS.cs_model)
                        (CS.cleartext_handshake_stream st0.CS.cs_model step))
    | _ -> ()

(**
  Introduction: a received-network-message witness yields a client wire step.
  This is the pre-existing shape of [client_step]'s [WireEvent] case, retained
  as a lemma so producers need not know about the generalised disjunction.
 **)
let lemma_client_wire_step_from_network_witness
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  (wire:W.wire_message)
  (msg:M.tls_message)
  (out:SM.step_output W.wire_message API.local_output)
  : Lemma
      (requires (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        SMCan.canonical_wire_step
          st0 st1 conn_ev
          (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
          (W.wire_serialize wire) /\
        network_input_message_projection st0 wire msg /\
        client_local_outputs_match conn_ev out.SM.so_local_outputs))
      (ensures
        client_step #local_event_repr st0 (SM.WireEvent wire) st1 out)
  =
  let conn_ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = msg;
    } in
  assert (client_wire_received_event st0 wire conn_ev)

(**
  Introduction: the head step of a protected handshake record yields a client
  wire step.  This is the disjunct that removes the receive-path fork.
 **)
let lemma_client_wire_step_from_protected_head_witness
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  (wire:W.wire_message)
  (step:CS.protected_handshake_step)
  (out:SM.step_output W.wire_message API.local_output)
  : Lemma
      (requires
        step.CS.protected_handshake_head == true /\
        SMCan.canonical_wire_step
          st0 st1 (CS.ConnProtectedHandshake step)
          (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
          (W.wire_serialize wire) /\
        client_local_outputs_match
          (CS.ConnProtectedHandshake step)
          out.SM.so_local_outputs)
      (ensures
        client_step #local_event_repr st0 (SM.WireEvent wire) st1 out)
  =
  assert (client_wire_received_event st0 wire (CS.ConnProtectedHandshake step))

(**
  Introduction: a cleartext handshake BUFFERING step yields a client wire step.

  The twin of [lemma_client_wire_step_from_protected_head_witness] and of
  [TLS13.Spec.Endpoint.Server.lemma_server_wire_step_from_cleartext_witness],
  and cheaper than either: [client_wire_received_event] accepts
  [ConnCleartextHandshake] outright, with no side condition -- a cleartext
  buffering step never delivers, so there is no [head] flag to set.
 **)
let lemma_client_wire_step_from_cleartext_witness
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  (wire:W.wire_message)
  (step:CS.cleartext_handshake_step)
  (out:SM.step_output W.wire_message API.local_output)
  : Lemma
      (requires
        SMCan.canonical_wire_step
          st0 st1 (CS.ConnCleartextHandshake step)
          (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
          (W.wire_serialize wire) /\
        client_local_outputs_match
          (CS.ConnCleartextHandshake step)
          out.SM.so_local_outputs)
      (ensures
        client_step #local_event_repr st0 (SM.WireEvent wire) st1 out)
  =
  assert (client_wire_received_event st0 wire (CS.ConnCleartextHandshake step))

(**
  Elimination: a client wire step is described by exactly one connection event,
  which is either a received network message or a protected-handshake head.
 **)
let lemma_client_wire_step_inversion
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  (wire:W.wire_message)
  (out:SM.step_output W.wire_message API.local_output)
  : Lemma
      (requires
        client_step #local_event_repr st0 (SM.WireEvent wire) st1 out)
      (ensures
        exists conn_ev.
          client_wire_received_event st0 wire conn_ev /\
          SMCan.canonical_wire_step
            st0 st1 conn_ev
            (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
            (W.wire_serialize wire) /\
          client_local_outputs_match conn_ev out.SM.so_local_outputs)
  = ()

(** THE PAIRED-SYSTEM CLIENT STEP -- [client_step] restricted to steps that
    leave the pending cleartext-handshake buffer EMPTY.  The exact mirror of
    [TLS13.Spec.Endpoint.Server.server_step_nonbuffering], and carried for the
    same reason.

    [client_step] itself admits a [ConnCleartextHandshake] buffering step: that
    is the generality the CLIENT IMPLEMENTATION needs in order to reassemble a
    ServerHello split across records.  The PAIRED SYSTEM
    ([TLS13.System.tls_machine_iface]) is a different artifact -- a closed world
    in which the verified client faces the verified server -- and that server
    emits its ServerHello as exactly one record, so the paired client never has
    cause to buffer.  Cross-record ServerHellos arise only against a THIRD-PARTY
    server, which the paired-system theorems do not model.

    Because a buffering step always leaves a NON-EMPTY buffer
    ([legal_cleartext_handshake_step] requires a non-empty fragment), pinning the
    post-state buffer empty is EXACTLY "this step did not buffer". **)
let client_step_nonbuffering
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0:CS.connection_state)
  (ev:SM.event W.wire_message local_event_repr)
  (st1:CS.connection_state)
  (out:SM.step_output W.wire_message API.local_output)
  : GTot prop =
  client_step #local_event_repr st0 ev st1 out /\
  CS.cleartext_handshake_buffer_empty st1.CS.cs_model

type client_initial_state =
  st:CS.connection_state{
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint
  }

noextract
let client_state_machine
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (initial:client_initial_state)
  : SM.state_machine
      CS.connection_state
      W.wire_message
      local_event_repr
      API.local_output
  =
  {
    SM.sm_initial_state = initial;
    SM.sm_step = client_step;
  }

noextract
let client_system
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (initial:client_initial_state)
  : WFSM.wire_format_state_machine
      CS.connection_state
      W.wire_message
      local_event_repr
      API.local_output
  =
  {
    WFSM.wfsm_state_machine = client_state_machine initial;
    WFSM.wfsm_wire_format = W.tls_record_wire_format;
  }

let client_canonical_step_rel
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  : prop =
  exists
    (ev:SM.event W.wire_message local_event_repr)
    (out:SM.step_output W.wire_message API.local_output).
      client_step st0 ev st1 out

let client_progress_preorder
  (#local_event_repr:Type0)
  {| client_event_representation local_event_repr |}
  =
  RTC.closure (client_canonical_step_rel #local_event_repr)
