module TLS13.Impl.Server.Types

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module M = TLS13.Messages
module R = TLS13.Record.Spec
module SM = TLS13.StateMachine
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(**
  Extraction-facing server step shapes and theorem vocabulary.

  This module deliberately mirrors the public client theorem surface while
  keeping server-specific implementation details out of the pure spec.  The
  eventual Pulse server handlers should prove these predicates directly.
**)

include TLS13.Impl.Endpoint.Types

type server_status = endpoint_status

type server_response = endpoint_response

type server_buffer_response = endpoint_buffer_response

type local_event_kind =
  | LocalStartServer
  | LocalSelectServerParameters
  | LocalDeriveSharedSecret
  | LocalInstallClientHandshakeTrafficKeys
  | LocalInstallServerHandshakeTrafficKeys
  | LocalInstallClientApplicationTrafficKeys
  | LocalInstallServerApplicationTrafficKeys
  | LocalSignCertificateVerify
  | LocalVerifyClientFinished
  | LocalDeliverApplicationData
  | LocalSendServerHello
  | LocalSendEncryptedExtensions
  | LocalSendCertificate
  | LocalSendCertificateVerify
  | LocalSendServerFinished
  | LocalSendApplicationData
  | LocalSendCloseNotify
  | LocalFail

type local_payload_kind =
  | LocalPayloadNone
  | LocalPayloadCertificateVerifySignature
  | LocalPayloadApplicationData

type next_local_action = {
  next_local_ready: bool;
  next_local_kind: local_event_kind;
  next_local_payload: local_payload_kind;
}

let server_state_core_correct
  (st:CS.connection_state)
  : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  Some? st.CS.cs_model.CS.model_config.CS.config_server /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg ->
     B.length cfg.CS.server_certificate_chain <=
       Bounds.max_server_certificate_chain_len
   | None -> False) /\
  CS.connection_state_consistent st /\
  CS.connection_state_full_log_consistent_for_role CS.ServerEndpoint st

let server_state_correct
  (st:CS.connection_state)
  : prop =
  server_state_core_correct st /\
  CS.connection_state_sent_seal_replay_consistent st /\
  CS.connection_state_received_decode_replay_consistent st

let server_raw_to_message_replay_consistent
  (st:CS.connection_state)
  : prop =
  CS.connection_state_raw_event_replay_consistent st /\
  CS.connection_state_protected_raw_segmented_replay_consistent st /\
  CS.connection_state_sent_seal_replay_consistent st /\
  CS.connection_state_received_decode_replay_consistent st

let server_end_to_end_invariant
  (st:CS.connection_state)
  : prop =
  server_state_correct st /\
  server_raw_to_message_replay_consistent st

let lemma_initial_server_state_correct
  (cfg:CS.connection_config)
  : Lemma
      (requires cfg.CS.config_role == CS.ServerEndpoint /\
                Some? cfg.CS.config_server /\
                (match cfg.CS.config_server with
                 | Some server_cfg ->
                   B.length server_cfg.CS.server_certificate_chain <=
                     Bounds.max_server_certificate_chain_len
                 | None -> False))
      (ensures server_state_correct (CS.initial cfg))
=
  CSL.lemma_initial_full_log_consistent_for_role CS.ServerEndpoint cfg;
  CSL.lemma_connection_state_protected_raw_segmented_replay (CS.initial cfg);
  CSL.lemma_initial_sent_seal_replay_consistent cfg;
  CSL.lemma_initial_received_decode_replay_consistent cfg;
  assert (CS.connection_state_evolves (CS.initial cfg) (CS.initial cfg))

let lemma_initial_server_end_to_end_invariant
  (cfg:CS.connection_config)
  : Lemma
      (requires cfg.CS.config_role == CS.ServerEndpoint /\
                Some? cfg.CS.config_server /\
                (match cfg.CS.config_server with
                 | Some server_cfg ->
                   B.length server_cfg.CS.server_certificate_chain <=
                     Bounds.max_server_certificate_chain_len
                 | None -> False))
      (ensures server_end_to_end_invariant (CS.initial cfg))
=
  lemma_initial_server_state_correct cfg;
  assert (server_raw_to_message_replay_consistent (CS.initial cfg))

let lemma_server_state_correct_protected_raw_segmented_replay
  (st:CS.connection_state)
  : Lemma
      (requires server_state_correct st)
      (ensures CS.connection_state_protected_raw_segmented_replay_consistent st)
=
  CSL.lemma_connection_state_protected_raw_segmented_replay st

let lemma_model_record_keys_consistent_for_role_record_read_key_schedule_projection
  (role:CS.endpoint_role)
  (model:CS.connection_model)
  : Lemma
      (requires CS.model_record_keys_consistent_for_role role model)
      (ensures CS.record_read_key_schedule_projection_for_role role model)
=
  match model.CS.model_control with
  | CS.ControlFailed _ -> ()
  | _ ->
    let keys = model.CS.model_handshake.CS.hs_keys in
    let read = model.CS.model_record.CS.record_read in
    assert (CS.record_keys_match_key_schedule_for_role
      role
      CS.TrafficRead
      model.CS.model_control
      keys
      read);
    (match read.R.epoch with
     | R.Initial -> ()
     | R.Handshake ->
       assert (CS.traffic_material_option_matches_record_direction
         (CS.traffic_material_for_label
           keys
           CS.TrafficHandshake
           (CS.traffic_label_for_endpoint_direction role CS.TrafficRead))
         read);
       (match CS.traffic_material_for_label
         keys
         CS.TrafficHandshake
         (CS.traffic_label_for_endpoint_direction role CS.TrafficRead) with
        | Some material ->
          assert (exists material'.
            CS.traffic_material_for_label
              keys
              CS.TrafficHandshake
              (CS.traffic_label_for_endpoint_direction role CS.TrafficRead) ==
                Some material' /\
            CS.traffic_material_matches_record_direction material' read)
        | None -> assert False)
     | R.Application ->
       assert (CS.traffic_material_option_matches_record_direction
         (CS.traffic_material_for_label
           keys
           CS.TrafficApplication
           (CS.traffic_label_for_endpoint_direction role CS.TrafficRead))
         read);
       (match CS.traffic_material_for_label
         keys
         CS.TrafficApplication
         (CS.traffic_label_for_endpoint_direction role CS.TrafficRead) with
        | Some material ->
          assert (exists material'.
            CS.traffic_material_for_label
              keys
              CS.TrafficApplication
              (CS.traffic_label_for_endpoint_direction role CS.TrafficRead) ==
                Some material' /\
            CS.traffic_material_matches_record_direction material' read)
        | None -> assert False))

let lemma_server_state_correct_record_read_key_schedule_projection
  (st:CS.connection_state)
  : Lemma
      (requires server_state_correct st)
      (ensures CS.record_read_key_schedule_projection_for_role
        CS.ServerEndpoint
        st.CS.cs_model)
=
  assert (server_state_core_correct st);
  assert (CS.connection_state_full_log_consistent_for_role CS.ServerEndpoint st);
  assert (CS.connection_state_layered_log_consistent_for_role CS.ServerEndpoint st);
  assert (CS.connection_state_record_keys_consistent_for_role CS.ServerEndpoint st);
  lemma_model_record_keys_consistent_for_role_record_read_key_schedule_projection
    CS.ServerEndpoint
    st.CS.cs_model

noextract
let response_network_out (resp:server_response) (network_out:B.bytes) : B.bytes =
  if SZ.v resp.network_out_len <= B.length network_out
  then Seq.slice network_out 0 (SZ.v resp.network_out_len)
  else B.empty

noextract
let response_app_out (resp:server_response) (app_out:B.bytes) : B.bytes =
  if SZ.v resp.app_out_len <= B.length app_out
  then Seq.slice app_out 0 (SZ.v resp.app_out_len)
  else B.empty

noextract
let event_api_app_out
  (ev:CS.conn_event)
  : B.bytes =
  CL.concat_bytes (CS.conn_event_app_received_delta ev)

noextract
let response_app_out_matches_event
  (resp:server_response)
  (ev:CS.conn_event)
  (app_out:B.bytes)
  : prop =
  Seq.equal (response_app_out resp app_out) (event_api_app_out ev)

noextract
let event_api_app_sent (ev:CS.conn_event) : GTot B.bytes =
  CL.concat_bytes (CS.conn_event_app_sent_delta ev)

let local_event_kind_matches
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : prop =
  match kind, ev with
  | LocalDeliverApplicationData, CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) ->
    Seq.equal bytes payload
  | LocalSendApplicationData, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes -> Seq.equal bytes payload
     | _ -> False)
  | LocalSendServerHello, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.ServerHello _) -> True
     | _ -> False)
  | LocalSendEncryptedExtensions, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.EncryptedExtensions _) -> True
     | _ -> False)
  | LocalSendCertificate, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.Certificate _) -> True
     | _ -> False)
  | LocalSendCertificateVerify, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.CertificateVerify _) -> True
     | _ -> False)
  | LocalSendServerFinished, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.Finished _) -> True
     | _ -> False)
  | LocalSendCloseNotify, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    msg.CL.message_value == M.TlsAlert T.CloseNotify
  | LocalStartServer, CS.ConnLocalEvent CS.LocalStartServer ->
    True
  | LocalSelectServerParameters, CS.ConnLocalEvent (CS.LocalSelectServerParameters _) ->
    True
  | LocalDeriveSharedSecret, CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) ->
    True
  | LocalInstallClientHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | LocalInstallServerHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | LocalInstallClientApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | LocalInstallServerApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | LocalSignCertificateVerify, CS.ConnLocalEvent (CS.LocalSignCertificateVerify _) ->
    True
  | LocalVerifyClientFinished, CS.ConnLocalEvent (CS.LocalVerifyClientFinished _) ->
    True
  | LocalFail, CS.ConnLocalEvent (CS.LocalFail _) ->
    True
  | _, _ ->
    False

let local_payload_matches_app_sent_delta
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : prop =
  match kind with
  | LocalSendApplicationData ->
    Seq.equal (event_api_app_sent ev) payload
  | _ ->
    Seq.equal (event_api_app_sent ev) B.empty

let local_event_supported_profile
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : prop =
  match kind, ev with
  | LocalSendApplicationData, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes ->
       B.length bytes <= SM.max_application_data_fragment_len /\
       CS.protected_record_count CL.Sent msg.CL.message_value == 1
     | _ -> False)
  | LocalSendApplicationData, _ ->
    False
  | _, _ ->
    True

let legal_response_for_event
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1 /\
  SZ.v resp.network_out_len == B.length raw_sent /\
  SZ.v resp.app_out_len <= B.length app_out /\
  Seq.equal (response_network_out resp network_out) raw_sent /\
  response_app_out_matches_event resp ev app_out

let unexpected_message_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == IllegalTransition /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.UnexpectedMessage)))
    B.empty
    B.empty
    network_out
    app_out

let decode_error_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == DecodeError /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
    B.empty
    B.empty
    network_out
    app_out

let legal_local_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  local_event_kind_matches kind payload ev /\
  local_payload_matches_app_sent_delta kind payload ev /\
  local_event_supported_profile kind payload ev /\
  CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent /\
  resp.status == StepOk /\
  legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out

let legal_handled_local_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  (exists ev raw_sent raw_received.
     legal_local_response
       st0
       st1
       resp
       kind
       payload
       ev
       raw_sent
       raw_received
       network_out
       app_out) \/
  unexpected_message_response st0 st1 resp network_out app_out

let received_message_event (msg:M.tls_message) : CS.conn_event =
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  }

let received_message_delta
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : CS.connection_delta =
  {
    CS.delta_event = received_message_event msg;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  }

let legal_network_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  (resp.status == DecodeError ==> False) /\
  (resp.status == NeedMoreInput ==> False) /\
  legal_response_for_event
    st0
    st1
    resp
    (received_message_event msg)
    B.empty
    raw_received
    network_out
    app_out

let server_network_event_end_to_end_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  server_end_to_end_invariant st0 /\
  server_end_to_end_invariant st1 /\
  legal_network_response st0 st1 resp msg raw_received network_out app_out

let server_local_event_end_to_end_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  server_end_to_end_invariant st0 /\
  server_end_to_end_invariant st1 /\
  legal_handled_local_response st0 st1 resp kind payload network_out app_out /\
  (resp.network_out_len == 0sz \/
   exists ev raw_sent raw_received.
     legal_local_response
       st0 st1 resp kind payload ev raw_sent raw_received network_out app_out /\
     CS.event_protected_raw_segmented_success ev raw_sent raw_received /\
     CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent /\
     (match ev with
      | CS.ConnNetworkEvent msg ->
         if msg.CL.message_direction == CL.Sent &&
           CS.network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false
        then CS.record_write_key_schedule_projection_for_role
               CS.ServerEndpoint
               st0.CS.cs_model
        else True
      | CS.ConnLocalEvent _ -> True))

let lemma_legal_local_response_select_payload_irrelevant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (payload0 payload1:B.bytes)
  (ev:CS.conn_event)
  (raw_sent raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_local_response
                 st0 st1 resp LocalSelectServerParameters payload0 ev
                 raw_sent raw_received network_out app_out)
      (ensures legal_local_response
                st0 st1 resp LocalSelectServerParameters payload1 ev
                raw_sent raw_received network_out app_out)
=
  ()

let lemma_legal_local_response_send_server_hello_payload_irrelevant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (payload0 payload1:B.bytes)
  (ev:CS.conn_event)
  (raw_sent raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_local_response
                 st0 st1 resp LocalSendServerHello payload0 ev
                 raw_sent raw_received network_out app_out)
      (ensures legal_local_response
                st0 st1 resp LocalSendServerHello payload1 ev
                raw_sent raw_received network_out app_out)
=
  ()

let lemma_local_select_server_parameters_payload_irrelevant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (payload0 payload1:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires server_local_event_end_to_end_correct
                        st0 st1 resp LocalSelectServerParameters payload0 network_out app_out)
      (ensures server_local_event_end_to_end_correct
                       st0 st1 resp LocalSelectServerParameters payload1 network_out app_out)
=
  let goal (_:unit) =
    server_local_event_end_to_end_correct
      st0 st1 resp LocalSelectServerParameters payload1 network_out app_out in
  FStar.Classical.or_elim
    #(exists ev raw_sent raw_received.
        legal_local_response
          st0 st1 resp LocalSelectServerParameters payload0 ev
          raw_sent raw_received network_out app_out)
    #(unexpected_message_response st0 st1 resp network_out app_out)
    #goal
    (fun h ->
      FStar.Classical.exists_elim (goal ())
        #CS.conn_event
        #(fun ev -> exists raw_sent raw_received.
          legal_local_response
            st0 st1 resp LocalSelectServerParameters payload0 ev
            raw_sent raw_received network_out app_out)
        h
        (fun ev ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_sent -> exists raw_received.
          legal_local_response
            st0 st1 resp LocalSelectServerParameters payload0 ev
            raw_sent raw_received network_out app_out)
        ()
        (fun raw_sent ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_received ->
          legal_local_response
            st0 st1 resp LocalSelectServerParameters payload0 ev
            raw_sent raw_received network_out app_out)
        ()
        (fun raw_received ->
        lemma_legal_local_response_select_payload_irrelevant
          st0 st1 resp payload0 payload1 ev raw_sent raw_received network_out app_out;
        FStar.Classical.exists_intro
          (fun raw_received' ->
            legal_local_response
              st0 st1 resp LocalSelectServerParameters payload1 ev
              raw_sent raw_received' network_out app_out)
          raw_received;
        FStar.Classical.exists_intro
          (fun raw_sent' ->
            exists raw_received'.
              legal_local_response
                st0 st1 resp LocalSelectServerParameters payload1 ev
                raw_sent' raw_received' network_out app_out)
          raw_sent;
        FStar.Classical.exists_intro
          (fun ev' ->
            exists raw_sent' raw_received'.
              legal_local_response
                st0 st1 resp LocalSelectServerParameters payload1 ev'
                raw_sent' raw_received' network_out app_out)
          ev))))
    (fun _ -> ())

let lemma_local_send_server_hello_payload_irrelevant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (payload0 payload1:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires server_local_event_end_to_end_correct
                        st0 st1 resp LocalSendServerHello payload0 network_out app_out)
      (ensures server_local_event_end_to_end_correct
                       st0 st1 resp LocalSendServerHello payload1 network_out app_out)
=
  let goal (_:unit) =
    server_local_event_end_to_end_correct
      st0 st1 resp LocalSendServerHello payload1 network_out app_out in
  FStar.Classical.or_elim
    #(exists ev raw_sent raw_received.
        legal_local_response
          st0 st1 resp LocalSendServerHello payload0 ev
          raw_sent raw_received network_out app_out)
    #(unexpected_message_response st0 st1 resp network_out app_out)
    #goal
    (fun h ->
      FStar.Classical.exists_elim (goal ())
        #CS.conn_event
        #(fun ev -> exists raw_sent raw_received.
          legal_local_response
            st0 st1 resp LocalSendServerHello payload0 ev
            raw_sent raw_received network_out app_out)
        h
        (fun ev ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_sent -> exists raw_received.
          legal_local_response
            st0 st1 resp LocalSendServerHello payload0 ev
            raw_sent raw_received network_out app_out)
        ()
        (fun raw_sent ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_received ->
          legal_local_response
            st0 st1 resp LocalSendServerHello payload0 ev
            raw_sent raw_received network_out app_out)
        ()
        (fun raw_received ->
        lemma_legal_local_response_send_server_hello_payload_irrelevant
          st0 st1 resp payload0 payload1 ev raw_sent raw_received network_out app_out;
        FStar.Classical.exists_intro
          (fun raw_received' ->
            legal_local_response
              st0 st1 resp LocalSendServerHello payload1 ev
              raw_sent raw_received' network_out app_out)
          raw_received;
        FStar.Classical.exists_intro
          (fun raw_sent' ->
            exists raw_received'.
              legal_local_response
                st0 st1 resp LocalSendServerHello payload1 ev
                raw_sent' raw_received' network_out app_out)
          raw_sent;
        FStar.Classical.exists_intro
          (fun ev' ->
            exists raw_sent' raw_received'.
              legal_local_response
                st0 st1 resp LocalSendServerHello payload1 ev'
                raw_sent' raw_received' network_out app_out)
          ev))))
    (fun _ -> ())

let server_network_bytes_end_to_end_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  server_end_to_end_invariant st0 /\
  server_end_to_end_invariant st1 /\
  SZ.v resp.consumed_len <= B.length input /\
  (resp.response.network_out_len == 0sz \/
   exists ev raw_sent raw_received.
     legal_response_for_event
       st0
       st1
       resp.response
       ev
       raw_sent
       raw_received
       network_out
       app_out /\
     CS.event_protected_raw_segmented_success ev raw_sent raw_received /\
     (match ev with
      | CS.ConnNetworkEvent msg ->
         if msg.CL.message_direction == CL.Sent &&
           CS.network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false
        then CS.record_write_key_schedule_projection_for_role
               CS.ServerEndpoint
               st0.CS.cs_model
        else True
      | CS.ConnLocalEvent _ -> True))

noextract
let server_network_consumed_prefix
  (resp:server_buffer_response)
  (input:B.bytes)
  : B.bytes =
  if SZ.v resp.consumed_len <= B.length input
  then Seq.slice input 0 (SZ.v resp.consumed_len)
  else B.empty

let server_network_step_ok_consumed_prefix
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  : prop =
  resp.response.status == StepOk ==>
    (exists ch raw_received.
      st1 ==
       CM.received_client_hello_state
         st0
         ch
         raw_received /\
      Seq.equal
       raw_received
       (server_network_consumed_prefix resp input)) \/
    (exists fin raw_received.
      st1 ==
       CM.received_client_finished_state
         st0
         fin
         raw_received /\
      Seq.equal
       raw_received
       (server_network_consumed_prefix resp input)) \/
    (exists bytes raw_received.
      st1 ==
       CM.received_application_data_state
         st0
         bytes
         raw_received /\
      Seq.equal
       raw_received
       (server_network_consumed_prefix resp input)) \/
    (exists raw_received.
      st1 ==
       CM.received_close_notify_state
         st0
         raw_received /\
      Seq.equal
       raw_received
       (server_network_consumed_prefix resp input)) \/
    (exists raw_received.
      st1 ==
       CM.received_change_cipher_spec_state
         st0
         raw_received /\
      Seq.equal
       raw_received
       (server_network_consumed_prefix resp input))

let server_decoded_message_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_network_response st0 st1 resp msg raw_received network_out app_out \/
  (CT.received_tls_raw_delta_legal st0 msg raw_received /\
   unexpected_message_response st0 st1 resp network_out app_out)

let server_protected_record_decode_uses_scheduled_read_key
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened.
    WS.parse_record raw_received ==
      Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
    CT.protected_record_opened st0 raw_received outer_fragment opened /\
    CS.record_read_key_schedule_projection_for_role
      CS.ServerEndpoint
      st0.CS.cs_model

let server_protected_record_decode_correct
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  (msg:M.tls_message)
  : prop =
  CT.protected_record_decodes_to_message st0 raw_received msg /\
  server_protected_record_decode_uses_scheduled_read_key st0 raw_received

let server_network_step_ok_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.response.status == StepOk ==>
    exists msg.
      CT.received_tls_raw_delta_legal
        st0
        msg
        (server_network_consumed_prefix resp input) /\
      server_decoded_message_event_projection
        st0
        st1
        resp.response
        msg
        (server_network_consumed_prefix resp input)
        network_out
        app_out /\
      (if CS.network_message_is_cleartext CL.Received msg
       then True
       else
         server_protected_record_decode_correct
           st0
           (server_network_consumed_prefix resp input)
           msg)

let server_network_consumed_input_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  server_network_step_ok_consumed_prefix st0 st1 resp input /\
  server_network_step_ok_received_decode_projection
    st0 st1 resp input network_out app_out /\
  (resp.response.status == NeedMoreInput ==> resp.consumed_len == 0sz)
