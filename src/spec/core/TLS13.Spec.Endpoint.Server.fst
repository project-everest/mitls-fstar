module TLS13.Spec.Endpoint.Server

module API = TLS13.Spec.Endpoint.API
module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SM = Common.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module T = TLS13.Types
module W = TLS13.Spec.Endpoint.Wire
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

(**
  Pure server-endpoint vocabulary and state machine.  The semantic local-event
  type is deliberately independent of the concrete C-ABI enum.
 **)

type local_event =
  | ServerStart
  | ServerSelectParameters
  | ServerDeriveSharedSecret
  | ServerInstallClientHandshakeTrafficKeys
  | ServerInstallServerHandshakeTrafficKeys
  | ServerInstallClientApplicationTrafficKeys
  | ServerInstallServerApplicationTrafficKeys
  | ServerSignCertificateVerify
  | ServerVerifyClientFinished
  | ServerDeliverApplicationData of B.bytes
  | ServerSendServerHello
  | ServerSendEncryptedExtensions
  | ServerSendCertificate
  | ServerSendCertificateVerify
  | ServerSendServerFinished
  | ServerSendApplicationData of B.bytes
  (**
    Send a KeyUpdate.  RFC 8446 §4.6.3 puts the two endpoints on an equal
    footing here: a server may answer a client's [update_requested], and may
    equally initiate a rotation of its own sending key.  The request form is
    part of the action, exactly as for [ClientSendKeyUpdate].
   **)
  | ServerSendKeyUpdate of M.key_update_request
  | ServerSendCloseNotify
  | ServerFail

let server_local_event_matches
  (local:local_event)
  (ev:CS.conn_event)
  : prop =
  match local, ev with
  | ServerDeliverApplicationData payload,
    CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) ->
      Seq.equal bytes payload
  | ServerSendApplicationData payload, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsApplicationData bytes -> Seq.equal bytes payload
       | _ -> False)
  | ServerSendServerHello, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.ServerHello _) -> True
       | _ -> False)
  | ServerSendEncryptedExtensions, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.EncryptedExtensions _) -> True
       | _ -> False)
  | ServerSendCertificate, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.Certificate _) -> True
       | _ -> False)
  | ServerSendCertificateVerify, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.CertificateVerify _) -> True
       | _ -> False)
  | ServerSendServerFinished, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      (match msg.CL.message_value with
       | M.TlsHandshake (M.Finished _) -> True
       | _ -> False)
  | ServerSendKeyUpdate req, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      msg.CL.message_value == M.TlsKeyUpdate req
  | ServerSendCloseNotify, CS.ConnNetworkEvent msg ->
      msg.CL.message_direction == CL.Sent /\
      msg.CL.message_value == M.TlsAlert T.Close_notify
  | ServerStart, CS.ConnLocalEvent CS.LocalStartServer ->
      True
  | ServerSelectParameters,
    CS.ConnLocalEvent (CS.LocalSelectServerParameters _) ->
      True
  | ServerDeriveSharedSecret,
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) ->
      True
  | ServerInstallClientHandshakeTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      role_install.CS.install_role == CS.ServerEndpoint /\
      role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
      role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | ServerInstallServerHandshakeTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      role_install.CS.install_role == CS.ServerEndpoint /\
      role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
      role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | ServerInstallClientApplicationTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      role_install.CS.install_role == CS.ServerEndpoint /\
      role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
      role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | ServerInstallServerApplicationTrafficKeys,
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      role_install.CS.install_role == CS.ServerEndpoint /\
      role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
      role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | ServerSignCertificateVerify,
    CS.ConnLocalEvent (CS.LocalSignCertificateVerify _) ->
      True
  | ServerVerifyClientFinished,
    CS.ConnLocalEvent (CS.LocalVerifyClientFinished _) ->
      True
  | ServerFail, CS.ConnLocalEvent (CS.LocalFail _) ->
      True
  | _, _ ->
      False

class server_event_representation (a:Type0) = {
  server_event_semantic: a -> GTot local_event;
  server_representation_matches:
    a -> CS.conn_event -> prop;
  server_representation_exact:
    input:a ->
    ev:CS.conn_event ->
      Lemma
        (server_representation_matches input ev <==>
         server_local_event_matches (server_event_semantic input) ev);
}

let server_local_outputs_match
  (ev:CS.conn_event)
  (outs:list API.local_output)
  : prop =
  API.local_outputs_match ev outs

let server_wire_outputs_match
  (raw_sent:B.bytes)
  (outs:list W.wire_message)
  : prop =
  Seq.equal
    (WF.serialize_all W.tls_record_wire_format outs)
    raw_sent

(**
  The connection events a SERVER may attribute to taking delivery of one wire
  record.  Two shapes, exactly as on the client (see
  [TLS13.Spec.Endpoint.Client.client_wire_received_event]):

  - [ConnNetworkEvent] with [Received] direction -- the record carried a whole
    TLS message, which the server interprets;
  - [ConnCleartextHandshake] -- the record carried a cleartext handshake
    fragment that does NOT yet complete a message, so its bytes are set aside
    and reassembled with those of later records.  This is what lets a server
    accept a ClientHello split across several records, which real clients do
    whenever the hello exceeds the peer's record size (large key shares, long
    SNI/ALPN lists, GREASE).

  A server never receives a [ConnProtectedHandshake] step: that is the CLIENT's
  reassembly of protected handshake records, driven by a different
  [conn_event], and admitting it here would let the server bypass its own
  cleartext-handshake rules.
 **)
let server_wire_received_event
  (conn_ev:CS.conn_event)
  : GTot prop =
  match conn_ev with
  | CS.ConnNetworkEvent tm -> tm.CL.message_direction == CL.Received
  | CS.ConnCleartextHandshake _ -> True
  | CS.ConnProtectedHandshake _ -> False
  | CS.ConnLocalEvent _ -> False

(** A wire step whose POST-state buffer is EMPTY cannot have been a buffering
    step: [legal_cleartext_handshake_step] insists the buffered fragment is
    non-empty, so the post-state stream [pending ++ fragment] is non-empty too.

    This is the vacuity argument every site that still pins the buffer empty
    needs in order to recover the old "the event is a received network message"
    reading of a wire step. **)
let lemma_wire_received_event_empty_buffer_not_buffering
  (m0:CS.connection_model)
  (conn_ev:CS.conn_event)
  (m1:CS.connection_model)
  : Lemma
      (requires
        server_wire_received_event conn_ev /\
        CS.step_model m0 conn_ev == Some m1 /\
        CS.cleartext_handshake_buffer_empty m1)
      (ensures
        CS.ConnNetworkEvent? conn_ev /\
        (CS.ConnNetworkEvent?._0 conn_ev).CL.message_direction == CL.Received)
  = match conn_ev with
    | CS.ConnCleartextHandshake step ->
      Seq.lemma_len_append
        (CS.pending_cleartext_handshake m0)
        step.CS.cleartext_handshake_fragment;
      assert (0 < B.length (CS.cleartext_handshake_stream m0 step));
      assert (Seq.equal (CS.pending_cleartext_handshake m1)
                        (CS.cleartext_handshake_stream m0 step))
    | _ -> ()

let server_step
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (st0:CS.connection_state)
  (ev:SM.event W.wire_message local_event_repr)
  (st1:CS.connection_state)
  (out:SM.step_output W.wire_message API.local_output)
  : GTot prop =
  match ev with
  | SM.WireEvent wire ->
    exists conn_ev.
      server_wire_received_event conn_ev /\
      SMCan.canonical_wire_step
        st0
        st1
        conn_ev
        (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
        (W.wire_serialize wire) /\
      server_local_outputs_match conn_ev out.SM.so_local_outputs
  | SM.LocalEvent local ->
    exists conn_ev raw_sent.
      server_representation_matches local conn_ev /\
      server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step
        st0
        st1
        conn_ev
        raw_sent
        B.empty

(**
  Introduction: a cleartext handshake BUFFERING step yields a server wire step.

  The twin of [lemma_client_wire_step_from_protected_head_witness], and much
  cheaper than it: [server_wire_received_event] already accepts
  [ConnCleartextHandshake] outright, so there is no side condition to check --
  no [head] flag, because a cleartext buffering step never delivers and hence is
  never a "head".
 **)
let lemma_server_wire_step_from_cleartext_witness
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
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
        server_local_outputs_match
          (CS.ConnCleartextHandshake step)
          out.SM.so_local_outputs)
      (ensures
        server_step #local_event_repr st0 (SM.WireEvent wire) st1 out)
  =
  assert (server_wire_received_event (CS.ConnCleartextHandshake step))

type server_initial_state =
  st:CS.connection_state{
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint
  }

noextract

(** THE PAIRED-SYSTEM SERVER STEP -- [server_step] restricted to steps that
    leave the pending cleartext-handshake buffer EMPTY.

    [server_step] itself admits a [ConnCleartextHandshake] buffering step: that
    is the generality the SERVER IMPLEMENTATION needs in order to reassemble a
    ClientHello split across records, and the canonical state machine
    ([server_state_machine]), the reachability relation ([WStep.server_sm]) and
    the refinement relation ([server_canonical_step_rel]) are all built over the
    general step.

    The PAIRED SYSTEM ([TLS13.System.tls_machine_iface]) is a different artifact:
    a closed world in which the verified client faces the verified server.  That
    client emits each cleartext handshake message as exactly one record, so the
    paired server never has cause to buffer -- cross-record ClientHellos arise
    only against a THIRD-PARTY client, which the paired-system theorems do not
    model.  Proving "the paired client never splits" needs the cross-endpoint
    record-material agreement, which lives above [TLS13.System]; so the product
    takes it as its scope rather than as a theorem, exactly as it already does
    for the client's own protected-handshake buffering
    ([CCShape.no_buffering_steps]).

    Because a buffering step always leaves a NON-EMPTY buffer
    ([legal_cleartext_handshake_step] requires a non-empty fragment), pinning the
    post-state buffer empty is EXACTLY "this step did not buffer".  That is what
    makes [SCShape.no_cleartext_buffering_steps s.server.cs_event_log] an
    INDUCTIVE conjunct of [TLS13.System.tls_system_inv], which is in turn what
    lets the system-level wire bridges keep reading "the delivered raw bytes ARE
    the ClientHello" off a delivery. **)
let server_step_nonbuffering
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (st0:CS.connection_state)
  (ev:SM.event W.wire_message local_event_repr)
  (st1:CS.connection_state)
  (out:SM.step_output W.wire_message API.local_output)
  : GTot prop =
  server_step #local_event_repr st0 ev st1 out /\
  CS.cleartext_handshake_buffer_empty st1.CS.cs_model

(** THE RECEIVED-MESSAGE BRIDGE for a server wire step whose post-state pending
    buffer is empty.

    [server_step] now quantifies over a [conn_event] satisfying
    [server_wire_received_event], which admits a [ConnCleartextHandshake]
    buffering step as well as a received network message.  Every site that still
    pins the pending buffer empty on the post-state can rule the buffering case
    out (a buffering step always leaves a NON-empty buffer) and recover the
    original "there is a received [tls_message]" reading.  This lemma performs
    that recovery once, so those sites need only a single call in front of their
    existing [eliminate exists (msg:M.tls_message)]. **)
let lemma_server_wire_step_received_msg
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (st0:CS.connection_state)
  (wire:W.wire_message)
  (st1:CS.connection_state)
  (out:SM.step_output W.wire_message API.local_output)
  : Lemma
      (requires
        server_step #local_event_repr st0 (SM.WireEvent wire) st1 out /\
        CS.cleartext_handshake_buffer_empty st1.CS.cs_model)
      (ensures
        (exists (msg:M.tls_message).
          (let conn_ev =
             CS.ConnNetworkEvent {
               CL.message_direction = CL.Received;
               CL.message_value = msg;
             } in
           CS.legal_connection_delta
             st0
             {
               CS.delta_event = conn_ev;
               CS.delta_raw_sent =
                 WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs;
               CS.delta_raw_received = W.wire_serialize wire;
             }
             st1 /\
           SMCan.sent_event_nonempty_seal_projection
             st0.CS.cs_model conn_ev
             (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs) /\
           SMCan.received_event_nonempty_decode_projection
             st0.CS.cs_model conn_ev (W.wire_serialize wire) /\
           server_local_outputs_match conn_ev out.SM.so_local_outputs)))
  = eliminate exists (conn_ev:CS.conn_event).
      (server_wire_received_event conn_ev /\
       SMCan.canonical_wire_step
         st0 st1 conn_ev
         (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs)
         (W.wire_serialize wire) /\
       server_local_outputs_match conn_ev out.SM.so_local_outputs)
    with
    (
      lemma_wire_received_event_empty_buffer_not_buffering
        st0.CS.cs_model conn_ev st1.CS.cs_model;
      let dm = CS.ConnNetworkEvent?._0 conn_ev in
      assert (conn_ev ==
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = dm.CL.message_value;
              });
      introduce exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = W.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all W.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (W.wire_serialize wire) /\
         server_local_outputs_match conn_ev out.SM.so_local_outputs)
      with dm.CL.message_value and ()
    )
let server_state_machine
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (initial:server_initial_state)
  : SM.state_machine
      CS.connection_state
      W.wire_message
      local_event_repr
      API.local_output
  =
  {
    SM.sm_initial_state = initial;
    SM.sm_step = server_step;
  }

noextract
let server_system
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (initial:server_initial_state)
  : WFSM.wire_format_state_machine
      CS.connection_state
      W.wire_message
      local_event_repr
      API.local_output
  =
  {
    WFSM.wfsm_state_machine = server_state_machine initial;
    WFSM.wfsm_wire_format = W.tls_record_wire_format;
  }

let server_canonical_step_rel
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  (st0 st1:CS.connection_state)
  : prop =
  exists
    (ev:SM.event W.wire_message local_event_repr)
    (out:SM.step_output W.wire_message API.local_output).
      server_step st0 ev st1 out

let server_progress_preorder
  (#local_event_repr:Type0)
  {| server_event_representation local_event_repr |}
  =
  RTC.closure (server_canonical_step_rel #local_event_repr)
