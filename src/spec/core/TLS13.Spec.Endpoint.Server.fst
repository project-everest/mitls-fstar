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
    exists msg.
      let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
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

type server_initial_state =
  st:CS.connection_state{
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint
  }

noextract
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
