module TLS13.Impl.Client.Types

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Sem = TLS13.Wire.Semantics
module ID = FStar.IndefiniteDescription
module Seq = FStar.Seq
module SM = TLS13.StateMachine
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module X = TLS13.X509.Spec

(**
  Extraction-facing client step shapes.  The concrete driver supplies buffers
  and machine-sized lengths; the TLS connection delta remains a ghost proof
  artifact connecting a concrete response to the rich specification state.
**)

include TLS13.Impl.Endpoint.Types

type client_status = endpoint_status

type client_response = endpoint_response

type client_buffer_response = endpoint_buffer_response

let client_state_core_correct
  (st:CS.connection_state)
  : prop =
  CS.connection_state_consistent st /\
  CS.connection_state_full_log_consistent st /\
  CS.connection_state_sent_seal_replay_consistent st /\
  CS.connection_state_sent_seal_key_schedule_replay_consistent st

let client_state_correct
  (st:CS.connection_state)
  : prop =
  client_state_core_correct st /\
  CS.connection_state_received_decode_replay_consistent st /\
  CS.connection_state_received_decode_key_schedule_replay_consistent st

let client_end_to_end_invariant
  (st:CS.connection_state)
  : prop =
  client_state_correct st /\
  CS.connection_state_raw_to_message_replay_consistent st

let lemma_initial_client_state_correct
  (cfg:CS.connection_config)
  : Lemma
      (requires cfg.CS.config_role == CS.ClientEndpoint)
      (ensures client_state_correct (CS.initial cfg))
=
  CSL.lemma_initial_full_log_consistent cfg;
  CSL.lemma_initial_sent_seal_replay_consistent cfg;
  CSL.lemma_initial_sent_seal_key_schedule_replay_consistent cfg;
  CSL.lemma_initial_received_decode_replay_consistent cfg;
  CSL.lemma_initial_received_decode_key_schedule_replay_consistent cfg;
  assert (CS.connection_state_evolves (CS.initial cfg) (CS.initial cfg))

let lemma_initial_client_end_to_end_invariant
  (cfg:CS.connection_config)
  : Lemma
      (requires cfg.CS.config_role == CS.ClientEndpoint)
      (ensures client_end_to_end_invariant (CS.initial cfg))
=
  lemma_initial_client_state_correct cfg;
  CSL.lemma_initial_raw_to_message_replay_consistent cfg

let lemma_client_state_correct_sent_seal_key_schedule_replay
  (st:CS.connection_state)
  : Lemma
      (requires client_state_correct st)
      (ensures CS.connection_state_sent_seal_key_schedule_replay_consistent st)
=
  CSL.lemma_connection_state_sent_seal_key_schedule_replay st

let lemma_client_state_correct_received_decode_key_schedule_replay
  (st:CS.connection_state)
  : Lemma
      (requires client_state_correct st)
      (ensures CS.connection_state_received_decode_key_schedule_replay_consistent st)
=
  CSL.lemma_connection_state_received_decode_key_schedule_replay st

let lemma_client_state_correct_protected_raw_segmented_replay
  (st:CS.connection_state)
  : Lemma
      (requires client_state_correct st)
      (ensures CS.connection_state_protected_raw_segmented_replay_consistent st)
=
  CSL.lemma_connection_state_protected_raw_segmented_replay st

let lemma_client_state_correct_raw_to_message_replay
  (st:CS.connection_state)
  : Lemma
      (requires client_state_correct st)
      (ensures CS.connection_state_raw_to_message_replay_consistent st)
=
  CSL.lemma_connection_state_raw_to_message_replay st

let tls_decode_error : T.tls_error = T.AlertError T.Decode_error

let tls_unexpected_message_error : T.tls_error = T.AlertError T.Unexpected_message

let tls_bad_finished_error : T.tls_error = T.BadFinished

type local_event_kind =
  | LocalStartHandshake
  | LocalDeriveSharedSecret
  | LocalInstallClientHandshakeTrafficKeys
  | LocalInstallServerHandshakeTrafficKeys
  | LocalInstallClientApplicationTrafficKeys
  | LocalInstallServerApplicationTrafficKeys
  | LocalValidateCertificate
  | LocalVerifyCertificateSignature
  | LocalVerifyFinished
  | LocalDeliverApplicationData
  | LocalSendClientHello
  | LocalSendClientFinished
  | LocalSendApplicationData
  | LocalSendKeyUpdate
  | LocalSendCloseNotify
  | LocalFail

type local_payload_kind =
  | LocalPayloadNone
  | LocalPayloadCertificatePublicKey

type next_local_action = {
  next_local_ready: bool;
  next_local_kind: local_event_kind;
  next_local_payload: local_payload_kind;
}

noextract
let local_validation_peer
  (st:CS.connection_state)
  (payload:B.bytes)
  : X.peer_identity =
  {
    X.validated_hostname = st.CS.cs_model.CS.model_config.CS.config_server_name;
    X.leaf_public_key = payload;
    X.permitted_signature_schemes = [];
  }

let local_input_wf
  (st:CS.connection_state)
  (kind:local_event_kind)
  (payload:B.bytes)
  : prop =
  match kind with
  | LocalDeliverApplicationData ->
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData ==>
    CS.legal_event
      st.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalDeliverApplicationData payload))
  | LocalValidateCertificate ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateReceived ==>
    (match st.CS.cs_model.CS.model_handshake.CS.hs_certificate with
     | Some cert ->
       X.validate_chain
         st.CS.cs_model.CS.model_config.CS.config_server_name
         st.CS.cs_model.CS.model_config.CS.config_validation_time
         st.CS.cs_model.CS.model_config.CS.config_trust_store
         (Sem.certificate_entries cert) ==
           Some (local_validation_peer st payload) /\
       CS.legal_event
         st.CS.cs_model
         (CS.ConnLocalEvent
           (CS.LocalValidateCertificate (local_validation_peer st payload)))
     | None -> False)
  | LocalVerifyCertificateSignature ->
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyReceived ==>
    (match st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
           st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer,
           st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
     | Some cv, Some peer, Some verify_input ->
       C.verify_signature
         (Sem.certificateVerify_scheme cv)
         peer.X.leaf_public_key
         verify_input
         (Sem.certificateVerify_signature_bytes cv) == true /\
       CS.legal_event
         st.CS.cs_model
         (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv))
     | _, _, _ -> False)
  | LocalVerifyFinished ->
    Seq.equal payload B.empty
  | _ -> True

let local_auth_tcb_projection
  (st:CS.connection_state)
  (kind:local_event_kind)
  (payload:B.bytes)
  : prop =
  match kind with
  | LocalValidateCertificate
  | LocalVerifyCertificateSignature ->
    local_input_wf st kind payload
  | _ ->
    True

let lemma_local_input_wf_auth_tcb_projection
  (st:CS.connection_state)
  (kind:local_event_kind)
  (payload:B.bytes)
  : Lemma
      (requires local_input_wf st kind payload)
      (ensures local_auth_tcb_projection st kind payload)
=
  match kind with
  | LocalValidateCertificate -> ()
  | LocalVerifyCertificateSignature -> ()
  | _ -> ()

let response_wf
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  SZ.v resp.network_out_len <= B.length network_out /\
  SZ.v resp.app_out_len <= B.length app_out

noextract
let response_network_out (resp:client_response) (network_out:B.bytes) : B.bytes =
  if SZ.v resp.network_out_len <= B.length network_out
  then Seq.slice network_out 0 (SZ.v resp.network_out_len)
  else B.empty

noextract
let response_app_out (resp:client_response) (app_out:B.bytes) : B.bytes =
  if SZ.v resp.app_out_len <= B.length app_out
  then Seq.slice app_out 0 (SZ.v resp.app_out_len)
  else B.empty

noextract
let event_api_app_out
  (ev:CS.conn_event)
  : B.bytes =
  CL.concat_bytes (CS.conn_event_app_received_delta ev)

noextract
let event_api_app_sent
  (ev:CS.conn_event)
  : B.bytes =
  CL.concat_bytes (CS.conn_event_app_sent_delta ev)

noextract
let response_app_out_matches_event
  (resp:client_response)
  (ev:CS.conn_event)
  (app_out:B.bytes)
  : prop =
  Seq.equal (response_app_out resp app_out) (event_api_app_out ev)

let legal_delta
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : prop =
  CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let legal_response_for_event
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  response_wf resp network_out app_out /\
  Seq.equal raw_sent (response_network_out resp network_out) /\
  response_app_out_matches_event resp ev app_out /\
  legal_delta st0 st1 ev raw_sent raw_received

let lemma_legal_response_for_event_app_log_delta
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures CS.model_app_log_delta st0.CS.cs_model ev st1.CS.cs_model)
=
  CSL.lemma_legal_connection_delta_app_log_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_app_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_app_log_consistent st0)
      (ensures CS.connection_state_app_log_consistent st1)
=
  CSL.lemma_legal_connection_delta_app_log_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_event_log_consistent_with
  (cfg:CS.connection_config)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_event_log_consistent_with cfg st0)
      (ensures CS.connection_state_event_log_consistent_with cfg st1)
=
  CSL.lemma_legal_connection_delta_event_log_consistent_with
    cfg
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_event_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_event_log_consistent st0)
      (ensures CS.connection_state_event_log_consistent st1)
=
  CSL.lemma_legal_connection_delta_event_log_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_transcript_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_transcript_consistent st0)
      (ensures CS.connection_state_transcript_consistent st1)
=
  CSL.lemma_legal_connection_delta_transcript_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_layered_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_layered_log_consistent st0)
      (ensures CS.connection_state_layered_log_consistent st1)
=
  CSL.lemma_legal_connection_delta_layered_log_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_client_state_core_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent /\
        client_state_core_correct st0)
      (ensures client_state_core_correct st1)
=
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = raw_received;
  } in
  CSL.lemma_legal_connection_delta_consistent st0 delta st1;
  CSL.lemma_legal_connection_delta_full_log_consistent st0 delta st1;
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent st0 delta st1;
  CSL.lemma_connection_state_sent_seal_key_schedule_replay st1

let lemma_legal_response_for_event_client_state_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received /\
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = raw_received;
  } in
  lemma_legal_response_for_event_client_state_core_correct
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out;
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent st0 delta st1;
  CSL.lemma_connection_state_received_decode_key_schedule_replay st1

let lemma_legal_response_for_event_protected_single_parse_record
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures CS.event_protected_single_raw_parse_success ev raw_sent raw_received)
=
  CSL.lemma_legal_connection_delta_protected_single_parse_record
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_protected_parse_prefix
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures CS.event_protected_raw_parse_prefix_success ev raw_sent raw_received)
=
  CSL.lemma_legal_connection_delta_protected_parse_prefix
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_protected_decompose_prefix
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures CS.event_protected_raw_decompose_prefix_success ev raw_sent raw_received)
=
  CSL.lemma_legal_connection_delta_protected_decompose_prefix
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_legal_response_for_event_protected_segmented
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures CS.event_protected_raw_segmented_success ev raw_sent raw_received)
=
  CSL.lemma_legal_connection_delta_protected_segmented
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let response_network_out_raw_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.network_out_len == 0sz \/
  (exists ev raw_sent raw_received.
    legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out /\
    CS.event_protected_raw_segmented_success ev raw_sent raw_received)

let sent_protected_event_write_key_schedule_projection
  (st0:CS.connection_state)
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnNetworkEvent msg ->
    if msg.CL.message_direction == CL.Sent &&
       CS.network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false
    then CS.record_write_key_schedule_projection st0.CS.cs_model
    else True
  | CS.ConnLocalEvent _ ->
    True

let response_network_out_write_key_schedule_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.network_out_len == 0sz \/
  (exists ev raw_sent raw_received.
    legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out /\
    sent_protected_event_write_key_schedule_projection st0 ev)

let response_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.network_out_len == 0sz \/
  (exists ev raw_sent raw_received.
    legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out /\
    CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent)

let response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists ev raw_sent raw_received.
    legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out /\
    CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      ev
      raw_received

let lemma_legal_response_for_event_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  assert (exists ev' raw_sent' raw_received'.
    legal_response_for_event
      st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
    CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      ev'
      raw_received')

let lemma_legal_response_for_event_network_out_raw_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures response_network_out_raw_projection st0 st1 resp network_out app_out)
=
  if resp.network_out_len = 0sz then ()
  else
    lemma_legal_response_for_event_protected_segmented
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out

let some_legal_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists ev raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out

let lemma_some_legal_response_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires some_legal_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  assert (exists ev raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  assert (legal_response_for_event
    st0 st1 resp ev raw_sent raw_received network_out app_out);
  CSL.lemma_step_model_preserves_config
    st0.CS.cs_model
    ev
    st1.CS.cs_model

let lemma_some_legal_response_received_decode_replay_consistent_aux
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        response_received_decode_projection st0 st1 resp network_out app_out /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures CS.connection_state_received_decode_replay_consistent st1)
=
  assert (exists ev raw_sent raw_received.
    legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out /\
    CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      ev
      raw_received);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received) in
  assert (legal_response_for_event
    st0 st1 resp ev raw_sent raw_received network_out app_out);
  assert (CS.received_event_nonempty_decode_projection
    st0.CS.cs_model
    ev
    raw_received);
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = raw_received;
  } in
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent st0 delta st1

let lemma_some_legal_response_layered_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        CS.connection_state_layered_log_consistent st0)
      (ensures CS.connection_state_layered_log_consistent st1)
=
  assert (exists ev. exists raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
  lemma_legal_response_for_event_layered_log_consistent
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out

let lemma_some_legal_response_client_state_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        response_network_out_seal_projection st0 st1 resp network_out app_out /\
        response_received_decode_projection st0 st1 resp network_out app_out /\
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  if resp.network_out_len = 0sz then (
    assert (exists ev. exists raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (response_wf resp network_out app_out);
    assert (SZ.v resp.network_out_len == 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice network_out 0 0);
    assert (response_network_out resp network_out == Seq.slice network_out 0 0);
    assert (Seq.equal B.empty (response_network_out resp network_out));
    assert (Seq.equal raw_sent (response_network_out resp network_out));
    assert (Seq.equal raw_sent B.empty);
    Seq.lemma_eq_elim raw_sent B.empty;
    assert (B.length raw_sent == 0);
    assert (CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent);
    lemma_legal_response_for_event_client_state_core_correct
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )
  else (
    assert (exists ev raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent);
    assert (CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent);
    lemma_legal_response_for_event_client_state_core_correct
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  );
  lemma_some_legal_response_received_decode_replay_consistent_aux
    st0
    st1
    resp
    network_out
    app_out;
  CSL.lemma_connection_state_received_decode_key_schedule_replay st1

let lemma_legal_response_for_event_sent_seal_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_sent_seal_replay_consistent st0 /\
        CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent)
      (ensures CS.connection_state_sent_seal_replay_consistent st1)
=
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_some_legal_response_sent_seal_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        response_network_out_seal_projection st0 st1 resp network_out app_out /\
        CS.connection_state_sent_seal_replay_consistent st0)
      (ensures CS.connection_state_sent_seal_replay_consistent st1)
=
  if resp.network_out_len = 0sz then (
    assert (exists ev. exists raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (response_wf resp network_out app_out);
    assert (SZ.v resp.network_out_len == 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice network_out 0 0);
    assert (response_network_out resp network_out == Seq.slice network_out 0 0);
    assert (Seq.equal B.empty (response_network_out resp network_out));
    assert (Seq.equal raw_sent (response_network_out resp network_out));
    assert (Seq.equal raw_sent B.empty);
    Seq.lemma_eq_elim raw_sent B.empty;
    assert (B.length raw_sent == 0);
    assert (CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent);
    lemma_legal_response_for_event_sent_seal_replay_consistent
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )
  else (
    assert (exists ev raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent);
    assert (CS.sent_event_nonempty_seal_projection st0.CS.cs_model ev raw_sent);
    lemma_legal_response_for_event_sent_seal_replay_consistent
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )

let lemma_legal_response_for_event_received_decode_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CS.connection_state_received_decode_replay_consistent st0 /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model
          ev
          raw_received)
      (ensures CS.connection_state_received_decode_replay_consistent st1)
=
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let lemma_some_legal_response_received_decode_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        response_received_decode_projection st0 st1 resp network_out app_out /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures CS.connection_state_received_decode_replay_consistent st1)
=
  lemma_some_legal_response_received_decode_replay_consistent_aux
    st0
    st1
    resp
    network_out
    app_out

let lemma_some_legal_response_network_out_raw_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires some_legal_response st0 st1 resp network_out app_out)
      (ensures response_network_out_raw_projection st0 st1 resp network_out app_out)
=
  if resp.network_out_len = 0sz then ()
  else (
    assert (exists ev. exists raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    lemma_legal_response_for_event_network_out_raw_projection
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )

let lemma_legal_response_for_event_network_out_write_key_schedule_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        client_state_correct st0)
      (ensures
        response_network_out_write_key_schedule_projection
          st0 st1 resp network_out app_out)
=
  if resp.network_out_len = 0sz then ()
  else (
    assert (CS.connection_state_record_keys_consistent st0);
    CSL.lemma_model_record_keys_consistent_record_write_key_schedule_projection
      st0.CS.cs_model;
    assert (CS.record_write_key_schedule_projection st0.CS.cs_model);
    assert (sent_protected_event_write_key_schedule_projection st0 ev);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
        st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      sent_protected_event_write_key_schedule_projection st0 ev')
  )

let lemma_some_legal_response_network_out_write_key_schedule_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        some_legal_response st0 st1 resp network_out app_out /\
        client_state_correct st0)
      (ensures
        response_network_out_write_key_schedule_projection
          st0 st1 resp network_out app_out)
=
  if resp.network_out_len = 0sz then ()
  else (
    assert (exists ev. exists raw_sent raw_received.
      legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out) in
    lemma_legal_response_for_event_network_out_write_key_schedule_projection
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )

let raw_received_matches_network_input
  (raw_received:B.bytes)
  (network_input:B.bytes)
  : prop =
  Seq.equal raw_received B.empty \/
  Seq.equal raw_received network_input

let some_legal_response_for_network_input
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists ev raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
    raw_received_matches_network_input raw_received network_input

let lemma_some_legal_response_for_empty_network_input_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires some_legal_response_for_network_input
        st0 st1 resp B.empty network_out app_out)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  assert (exists ev raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
    raw_received_matches_network_input raw_received B.empty);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
        raw_received_matches_network_input raw_received B.empty) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
        raw_received_matches_network_input raw_received B.empty) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
        raw_received_matches_network_input raw_received B.empty) in
  assert (legal_response_for_event
    st0 st1 resp ev raw_sent raw_received network_out app_out);
  assert (raw_received_matches_network_input raw_received B.empty);
  if Seq.equal raw_received B.empty then ()
  else assert (Seq.equal raw_received B.empty);
  Seq.lemma_eq_elim raw_received B.empty;
  assert (B.length raw_received == 0);
  assert (CS.received_event_nonempty_decode_projection
    st0.CS.cs_model
    ev
    raw_received);
  lemma_legal_response_for_event_response_received_decode_projection
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out

noextract
let network_consumed_prefix
  (network_input:B.bytes)
  (consumed_len:SZ.t)
  : B.bytes =
  if SZ.v consumed_len <= B.length network_input then
    Seq.slice network_input 0 (SZ.v consumed_len)
  else
    B.empty

let some_legal_response_for_network_prefix
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input:B.bytes)
  (consumed_len:SZ.t)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  SZ.v consumed_len <= B.length network_input /\
  some_legal_response_for_network_input
    st0
    st1
    resp
    (network_consumed_prefix network_input consumed_len)
    network_out
    app_out

let legal_received_tls_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  (resp.status == DecodeError ==> False) /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg })
    B.empty
    raw_received
    network_out
    app_out

let received_tls_raw_delta_legal
  (st0:CS.connection_state)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = msg;
    })
    B.empty
    raw_received

let wire_parse_success
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  : prop =
  exists ct.
    L.content_type_matches content_type ct /\
    WS.parse_tls_message ct fragment == Some msg

let wire_parse_failure
  (content_type:U8.t)
  (fragment:B.bytes)
  : prop =
  forall ct.
    L.content_type_matches content_type ct ==>
    WS.parse_tls_message ct fragment == None

let decoder_fragment_matches_plaintext
  (content_type:U8.t)
  (fragment:B.bytes)
  (plaintext:M.plaintext)
  : prop =
  L.content_type_matches content_type plaintext.M.content_type /\
  Seq.equal fragment plaintext.M.fragment

let record_header_aad (raw_received:B.bytes) : GTot B.bytes =
  if B.length raw_received >= 5
  then Seq.slice raw_received 0 5
  else B.empty

let protected_record_opened
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  (outer_fragment:B.bytes)
  (opened:B.bytes)
  : prop =
  exists read_state'.
    R.open_record
      st0.CS.cs_model.CS.model_record.CS.record_read
      (record_header_aad raw_received)
      outer_fragment ==
      Some (opened, read_state')

let protected_decoder_fragment_relation
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment.
    WS.parse_record_wire raw_received ==
     Some (T.Application_data, outer_fragment, B.length raw_received) /\
    (exists opened.
     protected_record_opened st0 raw_received outer_fragment opened /\
     (exists plaintext.
       WS.parse_plaintext opened == Some plaintext /\
       decoder_fragment_matches_plaintext content_type fragment plaintext))

let protected_record_decodes_to_message
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  (msg:M.tls_message)
  : prop =
  exists outer_fragment opened plaintext.
    WS.parse_record_wire raw_received ==
       Some (T.Application_data, outer_fragment, B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment opened /\
    WS.parse_plaintext opened == Some plaintext /\
    WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg

let lemma_protected_decoder_fragment_relation_decodes_to_message
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : Lemma
       (requires
         protected_decoder_fragment_relation st0 content_type fragment raw_received /\
         wire_parse_success content_type fragment msg)
       (ensures protected_record_decodes_to_message st0 raw_received msg)
=
  assert (exists outer_fragment.
    WS.parse_record_wire raw_received ==
     Some (T.Application_data, outer_fragment, B.length raw_received) /\
    (exists opened.
     protected_record_opened st0 raw_received outer_fragment opened /\
     (exists plaintext.
       WS.parse_plaintext opened == Some plaintext /\
       decoder_fragment_matches_plaintext content_type fragment plaintext)));
  let outer_fragment =
    ID.indefinite_description_ghost
       B.bytes
       (fun outer_fragment ->
         WS.parse_record_wire raw_received ==
           Some (T.Application_data, outer_fragment, B.length raw_received) /\
         (exists opened.
           protected_record_opened st0 raw_received outer_fragment opened /\
           (exists plaintext.
             WS.parse_plaintext opened == Some plaintext /\
             decoder_fragment_matches_plaintext content_type fragment plaintext))) in
  assert (exists opened.
    protected_record_opened st0 raw_received outer_fragment opened /\
    (exists plaintext.
       WS.parse_plaintext opened == Some plaintext /\
       decoder_fragment_matches_plaintext content_type fragment plaintext));
  let opened =
    ID.indefinite_description_ghost
       B.bytes
       (fun opened ->
         protected_record_opened st0 raw_received outer_fragment opened /\
         (exists plaintext.
           WS.parse_plaintext opened == Some plaintext /\
           decoder_fragment_matches_plaintext content_type fragment plaintext)) in
  assert (exists plaintext.
    WS.parse_plaintext opened == Some plaintext /\
    decoder_fragment_matches_plaintext content_type fragment plaintext);
  let plaintext =
    ID.indefinite_description_ghost
       M.plaintext
       (fun plaintext ->
         WS.parse_plaintext opened == Some plaintext /\
         decoder_fragment_matches_plaintext content_type fragment plaintext) in
  assert (decoder_fragment_matches_plaintext content_type fragment plaintext);
  assert (exists ct.
    L.content_type_matches content_type ct /\
    WS.parse_tls_message ct fragment == Some msg);
  let ct =
    ID.indefinite_description_ghost
       T.content_type
       (fun ct ->
         L.content_type_matches content_type ct /\
         WS.parse_tls_message ct fragment == Some msg) in
  assert (L.content_type_matches content_type ct);
  assert (L.content_type_matches content_type plaintext.M.content_type);
  assert (ct == plaintext.M.content_type);
  assert (Seq.equal fragment plaintext.M.fragment);
  Seq.lemma_eq_elim fragment plaintext.M.fragment;
  assert (WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg);
  assert (exists outer_fragment' opened' plaintext'.
    WS.parse_record_wire raw_received ==
       Some (T.Application_data, outer_fragment', B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment' opened' /\
    WS.parse_plaintext opened' == Some plaintext' /\
    WS.parse_tls_message plaintext'.M.content_type plaintext'.M.fragment == Some msg)

let protected_record_decode_uses_scheduled_read_key
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened.
    WS.parse_record_wire raw_received ==
     Some (T.Application_data, outer_fragment, B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment opened /\
    CS.record_read_key_schedule_projection st0.CS.cs_model

let protected_record_decode_correct
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  (msg:M.tls_message)
  : prop =
  protected_record_decodes_to_message st0 raw_received msg /\
  protected_record_decode_uses_scheduled_read_key st0 raw_received

let lemma_protected_record_decodes_to_received_single_decode
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  (msg:M.tls_message)
  : Lemma
      (requires protected_record_decodes_to_message st0 raw_received msg)
      (ensures CS.received_single_protected_message_decode
        st0.CS.cs_model
        msg
        raw_received)
=
  assert (exists outer_fragment opened plaintext.
    WS.parse_record_wire raw_received ==
       Some (T.Application_data, outer_fragment, B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment opened /\
    WS.parse_plaintext opened == Some plaintext /\
    WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg);
  let outer_fragment =
    ID.indefinite_description_ghost
      B.bytes
      (fun outer_fragment -> exists opened plaintext.
        WS.parse_record_wire raw_received ==
          Some (T.Application_data, outer_fragment, B.length raw_received) /\
        protected_record_opened st0 raw_received outer_fragment opened /\
        WS.parse_plaintext opened == Some plaintext /\
        WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg) in
  let opened =
    ID.indefinite_description_ghost
      B.bytes
      (fun opened -> exists plaintext.
        WS.parse_record_wire raw_received ==
          Some (T.Application_data, outer_fragment, B.length raw_received) /\
        protected_record_opened st0 raw_received outer_fragment opened /\
        WS.parse_plaintext opened == Some plaintext /\
        WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg) in
  let plaintext =
    ID.indefinite_description_ghost
      M.plaintext
      (fun plaintext ->
        WS.parse_record_wire raw_received ==
          Some (T.Application_data, outer_fragment, B.length raw_received) /\
        protected_record_opened st0 raw_received outer_fragment opened /\
        WS.parse_plaintext opened == Some plaintext /\
        WS.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg) in
  assert (protected_record_opened st0 raw_received outer_fragment opened);
  assert (CS.received_record_opened
    st0.CS.cs_model
    raw_received
    outer_fragment
    opened);
  assert (CS.received_single_protected_message_decode
    st0.CS.cs_model
    msg
    raw_received)

let lemma_protected_decoder_fragment_relation_read_key_schedule_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
     (requires
       protected_decoder_fragment_relation st0 content_type fragment raw_received /\
       client_state_correct st0)
     (ensures protected_record_decode_uses_scheduled_read_key st0 raw_received)
=
  assert (exists outer_fragment.
    WS.parse_record_wire raw_received ==
     Some (T.Application_data, outer_fragment, B.length raw_received) /\
    (exists opened.
     protected_record_opened st0 raw_received outer_fragment opened /\
     (exists plaintext.
      WS.parse_plaintext opened == Some plaintext /\
      decoder_fragment_matches_plaintext content_type fragment plaintext)));
  let outer_fragment =
    ID.indefinite_description_ghost
     B.bytes
     (fun outer_fragment ->
       WS.parse_record_wire raw_received ==
         Some (T.Application_data, outer_fragment, B.length raw_received) /\
       (exists opened.
         protected_record_opened st0 raw_received outer_fragment opened /\
         (exists plaintext.
           WS.parse_plaintext opened == Some plaintext /\
           decoder_fragment_matches_plaintext content_type fragment plaintext))) in
  assert (exists opened.
    protected_record_opened st0 raw_received outer_fragment opened /\
    (exists plaintext.
     WS.parse_plaintext opened == Some plaintext /\
     decoder_fragment_matches_plaintext content_type fragment plaintext));
  let opened =
    ID.indefinite_description_ghost
     B.bytes
     (fun opened ->
       protected_record_opened st0 raw_received outer_fragment opened /\
       (exists plaintext.
         WS.parse_plaintext opened == Some plaintext /\
         decoder_fragment_matches_plaintext content_type fragment plaintext)) in
  assert (protected_record_opened st0 raw_received outer_fragment opened);
  assert (CS.connection_state_record_keys_consistent st0);
  CSL.lemma_model_record_keys_consistent_record_read_key_schedule_projection
    st0.CS.cs_model;
  assert (CS.record_read_key_schedule_projection st0.CS.cs_model);
  assert (exists outer_fragment' opened'.
    WS.parse_record_wire raw_received ==
     Some (T.Application_data, outer_fragment', B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment' opened' /\
    CS.record_read_key_schedule_projection st0.CS.cs_model)

let decoder_fragment_relation
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : prop =
  exists outer_ct outer_fragment.
    WS.parse_record_wire raw_received ==
      Some (outer_ct, outer_fragment, B.length raw_received) /\
    (if outer_ct == T.Application_data
     then protected_decoder_fragment_relation st0 content_type fragment raw_received
     else
       L.content_type_matches content_type outer_ct /\
       Seq.equal fragment outer_fragment)

let network_input_decoder_payload_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  if CS.network_message_is_cleartext CL.Received msg
  then
    decoder_fragment_relation st0 content_type fragment raw_received /\
    CS.received_cleartext_tls_message_raw msg raw_received
  else
    protected_decoder_fragment_relation st0 content_type fragment raw_received

let network_input_wf
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : prop =
  decoder_fragment_relation st0 content_type fragment raw_received /\
  forall msg.
  wire_parse_success content_type fragment msg ==>
  received_tls_raw_delta_legal st0 msg raw_received

let raw_record_parse_success
  (raw_received:B.bytes)
  : prop =
  exists outer_ct outer_fragment.
    WS.parse_record_wire raw_received ==
      Some (outer_ct, outer_fragment, B.length raw_received)

let canonical_raw_record_parse_success
  (raw_received:B.bytes)
  : prop =
  exists outer_ct outer_fragment.
    WS.parse_record raw_received ==
      Some (outer_ct, outer_fragment, B.length raw_received)

let lemma_raw_record_parse_success_nonempty
  (raw_received:B.bytes)
  : Lemma
      (requires raw_record_parse_success raw_received)
      (ensures B.length raw_received > 0)
=
  match WS.parse_record_wire raw_received with
  | None -> assert False
  | Some (outer_ct, outer_fragment, consumed) ->
    assert (consumed == B.length raw_received);
    WS.lemma_parse_record_wire_some_consumed_positive
      raw_received
      outer_ct
      outer_fragment
      consumed;
    assert (B.length raw_received > 0)

let lemma_raw_record_parse_success_raw_records
  (raw_received:B.bytes)
  : Lemma
      (requires canonical_raw_record_parse_success raw_received)
      (ensures exists outer_ct.
        CS.raw_records_exactly raw_received outer_ct 1 /\
        CS.raw_records_segmented raw_received outer_ct 1)
=
  match WS.parse_record raw_received with
  | None ->
    assert False
  | Some (outer_ct, outer_fragment, consumed) ->
    assert (consumed == B.length raw_received);
    CSL.lemma_parse_record_full_raw_records_exactly
      raw_received
      outer_ct
      outer_fragment;
    assert (exists outer_ct'.
      CS.raw_records_exactly raw_received outer_ct' 1 /\
      CS.raw_records_segmented raw_received outer_ct' 1)

let lemma_network_input_wf_raw_record_parse_success
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires network_input_wf st0 content_type fragment raw_received)
      (ensures raw_record_parse_success raw_received)
=
  assert (decoder_fragment_relation st0 content_type fragment raw_received)

let lemma_decoder_fragment_relation_protected_from_raw_records
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        decoder_fragment_relation st0 content_type fragment raw_received /\
        CS.raw_records_exactly raw_received T.Application_data 1)
      (ensures protected_decoder_fragment_relation st0 content_type fragment raw_received)
=
  CSL.lemma_raw_records_exactly_one_parse_record raw_received T.Application_data;
  assert (exists app_fragment.
    WS.parse_record raw_received ==
      Some (T.Application_data, app_fragment, B.length raw_received));
  let app_fragment =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_fragment ->
        WS.parse_record raw_received ==
          Some (T.Application_data, app_fragment, B.length raw_received)) in
  WS.lemma_parse_record_implies_parse_record_wire raw_received;
  assert (WS.parse_record_wire raw_received ==
    Some (T.Application_data, app_fragment, B.length raw_received));
  let outer_ct =
    ID.indefinite_description_ghost
      T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record_wire raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.Application_data
         then protected_decoder_fragment_relation st0 content_type fragment raw_received
         else
           L.content_type_matches content_type outer_ct /\
           Seq.equal fragment outer_fragment)) in
  let outer_fragment =
    ID.indefinite_description_ghost
      B.bytes
      (fun outer_fragment ->
        WS.parse_record_wire raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.Application_data
         then protected_decoder_fragment_relation st0 content_type fragment raw_received
         else
           L.content_type_matches content_type outer_ct /\
           Seq.equal fragment outer_fragment)) in
  assert (WS.parse_record_wire raw_received ==
    Some (outer_ct, outer_fragment, B.length raw_received));
  assert (WS.parse_record_wire raw_received ==
    Some (T.Application_data, app_fragment, B.length raw_received));
  assert (outer_ct == T.Application_data);
  assert (protected_decoder_fragment_relation st0 content_type fragment raw_received)

let network_input_message_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  let received_msg = {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  decoder_fragment_relation st0 content_type fragment raw_received /\
  raw_record_parse_success raw_received /\
  wire_parse_success content_type fragment msg /\
  network_input_decoder_payload_projection st0 content_type fragment msg raw_received /\
  (if CS.network_message_is_cleartext CL.Received msg
   then True
   else protected_record_decodes_to_message st0 raw_received msg) /\
  received_tls_raw_delta_legal st0 msg raw_received /\
  CS.network_message_raw_delta_legal
    st0.CS.cs_model
    received_msg
    raw_received /\
  (if CS.network_message_is_cleartext CL.Received msg
   then CS.received_cleartext_tls_message_raw msg raw_received
   else
     CS.raw_records_exactly
       raw_received
       T.Application_data
       (CS.protected_record_count CL.Received msg) /\
     CS.raw_records_segmented
       raw_received
       T.Application_data
       (CS.protected_record_count CL.Received msg))

let lemma_network_input_wf_message_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : Lemma
      (requires
        network_input_wf st0 content_type fragment raw_received /\
        wire_parse_success content_type fragment msg)
      (ensures network_input_message_projection
        st0 content_type fragment msg raw_received)
=
  let received_msg = {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  } in
  assert (decoder_fragment_relation st0 content_type fragment raw_received);
  assert (raw_record_parse_success raw_received);
  assert (received_tls_raw_delta_legal st0 msg raw_received);
  assert (CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent received_msg)
    B.empty
    raw_received);
  assert (CS.network_message_raw_delta_legal
    st0.CS.cs_model
    received_msg
    raw_received);
  if CS.network_message_is_cleartext CL.Received msg
  then
    assert (CS.received_cleartext_tls_message_raw msg raw_received)
  else (
    assert (CS.raw_records_exactly
      raw_received
      T.Application_data
      (CS.protected_record_count CL.Received msg));
    assert (CS.protected_record_count CL.Received msg == 1);
    lemma_decoder_fragment_relation_protected_from_raw_records
      st0
      content_type
      fragment
      raw_received;
    assert (protected_decoder_fragment_relation st0 content_type fragment raw_received);
    lemma_protected_decoder_fragment_relation_decodes_to_message
      st0
      content_type
      fragment
      msg
      raw_received;
    CSL.lemma_event_raw_delta_legal_protected_segmented
      st0.CS.cs_model
      (CS.ConnNetworkEvent received_msg)
      B.empty
      raw_received;
    assert (CS.event_protected_raw_segmented_success
      (CS.ConnNetworkEvent received_msg)
      B.empty
      raw_received);
    assert (CS.raw_records_segmented
      raw_received
      T.Application_data
      (CS.protected_record_count CL.Received msg))
  )

let response_network_out_parse_success
  (resp:client_response)
  (network_out:B.bytes)
  : prop =
  resp.network_out_len == 0sz \/
  exists outer_ct outer_fragment.
    WS.parse_record (response_network_out resp network_out) ==
      Some (outer_ct, outer_fragment, SZ.v resp.network_out_len)

let parsed_message_wire_success
  (content_type:U8.t)
  (fragment:B.bytes)
  (l:L.tls_message)
  : prop =
  match l with
  | L.LTlsChangeCipherSpec ->
  wire_parse_success content_type fragment M.TlsChangeCipherSpec
  | L.LTlsAlert alert_wire ->
  forall alert.
    L.alert_description_matches alert_wire alert ==>
    wire_parse_success content_type fragment (M.TlsAlert alert)
  | L.LTlsHandshake L.LHelloRetryRequest ->
  wire_parse_success content_type fragment (M.TlsHandshake M.HelloRetryRequest)
  | _ ->
  exists msg. wire_parse_success content_type fragment msg

let parsed_message_wire_success_for
  (content_type:U8.t)
  (fragment:B.bytes)
  (l:L.tls_message)
  (msg:M.tls_message)
  : prop =
  wire_parse_success content_type fragment msg /\
  (match l, msg with
  | L.LTlsChangeCipherSpec, M.TlsChangeCipherSpec ->
    True
  | L.LTlsChangeCipherSpec, _ ->
    False
  | L.LTlsAlert alert_wire, M.TlsAlert alert ->
    L.alert_description_matches alert_wire alert
  | L.LTlsAlert _, _ ->
    False
  | L.LTlsHandshake L.LHelloRetryRequest, M.TlsHandshake M.HelloRetryRequest ->
    True
  | L.LTlsHandshake L.LHelloRetryRequest, _ ->
    False
  | L.LTlsHandshake (L.LServerHello _), M.TlsHandshake (M.ServerHello sh) ->
    Seq.equal fragment (WS.serialize_handshake (M.ServerHello sh))
  | L.LTlsHandshake (L.LServerHello _), _ ->
    False
  | L.LTlsHandshake (L.LClientHello _), M.TlsHandshake (M.ClientHello ch) ->
    Seq.equal fragment (WS.serialize_handshake (M.ClientHello ch))
  | L.LTlsHandshake (L.LClientHello _), _ ->
    False
  | L.LTlsHandshake (L.LEncryptedExtensions _), M.TlsHandshake (M.EncryptedExtensions ee) ->
    Seq.equal fragment (WS.serialize_handshake (M.EncryptedExtensions ee))
  | L.LTlsHandshake (L.LEncryptedExtensions _), _ ->
    False
  | L.LTlsHandshake (L.LCertificate _), M.TlsHandshake (M.Certificate cert) ->
    Seq.equal fragment (WS.serialize_handshake (M.Certificate cert))
  | L.LTlsHandshake (L.LCertificate _), _ ->
    False
  | L.LTlsHandshake (L.LCertificateVerify _), M.TlsHandshake (M.CertificateVerify cv) ->
    Seq.equal fragment (WS.serialize_handshake (M.CertificateVerify cv))
  | L.LTlsHandshake (L.LCertificateVerify _), _ ->
    False
  | L.LTlsHandshake (L.LFinished _), M.TlsHandshake (M.Finished _) ->
    True
  | L.LTlsHandshake (L.LFinished _), _ ->
    False
  | L.LTlsIgnoredPostHandshake _, M.TlsIgnoredPostHandshake _ ->
    True
  | L.LTlsIgnoredPostHandshake _, _ ->
    False
  | L.LTlsKeyUpdate req_wire, M.TlsKeyUpdate req ->
    L.key_update_request_matches req_wire req
  | L.LTlsKeyUpdate _, _ ->
    False
  | L.LTlsApplicationData _, M.TlsApplicationData _ ->
    True
  | L.LTlsApplicationData _, _ ->
    False)

let lemma_parsed_message_network_input_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (l:L.tls_message)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : Lemma
     (requires
       network_input_wf st0 content_type fragment raw_received /\
       parsed_message_wire_success_for content_type fragment l msg)
     (ensures network_input_message_projection
       st0 content_type fragment msg raw_received)
=
  lemma_network_input_wf_message_projection
    st0
    content_type
    fragment
    msg
    raw_received

let local_event_kind_matches
  (st:CS.connection_state)
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
  | LocalSendClientHello, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.ClientHello _) -> True
     | _ -> False)
  | LocalSendClientFinished, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.Finished _) -> True
     | _ -> False)
  | LocalSendCloseNotify, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    msg.CL.message_value == M.TlsAlert T.Close_notify
  | LocalSendKeyUpdate, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    msg.CL.message_value == M.TlsKeyUpdate M.UpdateNotRequested
  | LocalStartHandshake, CS.ConnLocalEvent (CS.LocalStartHandshake _) -> True
  | LocalDeriveSharedSecret, CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) -> True
  | LocalInstallClientHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficWrite
  | LocalInstallServerHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficRead
  | LocalInstallClientApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficWrite
  | LocalInstallServerApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficRead
  | LocalValidateCertificate, CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ->
    peer == local_validation_peer st payload
  | LocalVerifyCertificateSignature, CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ->
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv
  | LocalVerifyFinished, CS.ConnLocalEvent (CS.LocalVerifyFinished _) -> True
  | LocalFail, CS.ConnLocalEvent (CS.LocalFail _) -> True
  | _, _ -> False

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

let legal_local_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  local_event_kind_matches st0 kind payload ev /\
  local_payload_matches_app_sent_delta kind payload ev /\
  local_event_supported_profile kind payload ev /\
  CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent /\
  legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out

let decode_error_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == DecodeError /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_decode_error))
    B.empty
    B.empty
    network_out
    app_out

let unexpected_message_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == IllegalTransition /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
    B.empty
    B.empty
    network_out
    app_out

let bad_finished_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == ConnectionFailed /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_bad_finished_error))
    B.empty
    B.empty
    network_out
    app_out

let lemma_decode_error_response_control_failed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires decode_error_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlFailed tls_decode_error)
=
  CSL.lemma_legal_connection_delta_local_fail_control_failed
    st0
    st1
    tls_decode_error
    B.empty
    B.empty

let lemma_unexpected_message_response_control_failed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires unexpected_message_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlFailed tls_unexpected_message_error)
=
  CSL.lemma_legal_connection_delta_local_fail_control_failed
    st0
    st1
    tls_unexpected_message_error
    B.empty
    B.empty

let lemma_bad_finished_response_control_failed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires bad_finished_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlFailed tls_bad_finished_error)
=
  CSL.lemma_legal_connection_delta_local_fail_control_failed
    st0
    st1
    tls_bad_finished_error
    B.empty
    B.empty

let legal_handled_local_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
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
  unexpected_message_response st0 st1 resp network_out app_out \/
  bad_finished_response st0 st1 resp network_out app_out

let local_send_application_data_supported_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  kind == LocalSendApplicationData /\ resp.status == StepOk ==>
    B.length payload <= SM.max_application_data_fragment_len /\
    CS.protected_record_count CL.Sent (M.TlsApplicationData payload) == 1

let legal_handled_tls_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_received_tls_response st0 st1 resp msg raw_received network_out app_out \/
  unexpected_message_response st0 st1 resp network_out app_out

let decoded_message_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_received_tls_response st0 st1 resp msg raw_received network_out app_out \/
  (received_tls_raw_delta_legal st0 msg raw_received /\
   unexpected_message_response st0 st1 resp network_out app_out)

let lemma_legal_handled_tls_response_decoded_message_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_input_message_projection
          st0 content_type fragment msg raw_received /\
        legal_handled_tls_response
          st0 st1 resp msg raw_received network_out app_out)
      (ensures
        decoded_message_event_projection
          st0 st1 resp msg raw_received network_out app_out)
=
  if legal_received_tls_response st0 st1 resp msg raw_received network_out app_out
  then ()
  else (
    assert (unexpected_message_response st0 st1 resp network_out app_out);
    assert (received_tls_raw_delta_legal st0 msg raw_received)
  )

let legal_network_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  ((exists msg.
      wire_parse_success content_type fragment msg /\
      legal_handled_tls_response st0 st1 resp msg raw_received network_out app_out) \/
   (wire_parse_failure content_type fragment /\
    decode_error_response st0 st1 resp network_out app_out)) /\
  some_legal_response_for_network_input
    st0
    st1
    resp
    raw_received
    network_out
    app_out

let legal_network_response_handled_exists
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists msg.
    wire_parse_success content_type fragment msg /\
    legal_handled_tls_response st0 st1 resp msg raw_received network_out app_out

let lemma_legal_network_response_decode_error_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_network_response
          st0 st1 resp content_type fragment raw_received network_out app_out /\
        resp.status == DecodeError)
      (ensures
        wire_parse_failure content_type fragment /\
        decode_error_response st0 st1 resp network_out app_out)
=
  if wire_parse_failure content_type fragment /\
     decode_error_response st0 st1 resp network_out app_out
  then ()
  else (
    assert (legal_network_response_handled_exists
      st0 st1 resp content_type fragment raw_received network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          wire_parse_success content_type fragment msg /\
          legal_handled_tls_response
            st0 st1 resp msg raw_received network_out app_out) in
    assert (legal_handled_tls_response
      st0 st1 resp msg raw_received network_out app_out);
    if legal_received_tls_response st0 st1 resp msg raw_received network_out app_out
    then assert False
    else (
      assert (unexpected_message_response st0 st1 resp network_out app_out);
      assert (resp.status == IllegalTransition);
      assert False
    )
  )

let lemma_legal_network_response_handled_of_non_decode_error
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_network_response
          st0 st1 resp content_type fragment raw_received network_out app_out /\
        (resp.status == DecodeError ==> False))
      (ensures
        legal_network_response_handled_exists
          st0 st1 resp content_type fragment raw_received network_out app_out)
=
  if legal_network_response_handled_exists
       st0 st1 resp content_type fragment raw_received network_out app_out
  then ()
  else (
    assert (wire_parse_failure content_type fragment /\
      decode_error_response st0 st1 resp network_out app_out);
    assert (resp.status == DecodeError);
    assert False
  )

let lemma_legal_network_response_message_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_input_wf st0 content_type fragment raw_received /\
        legal_network_response
          st0 st1 resp content_type fragment raw_received network_out app_out /\
        wire_parse_success content_type fragment msg)
      (ensures network_input_message_projection
        st0 content_type fragment msg raw_received)
=
  lemma_network_input_wf_message_projection
    st0
    content_type
    fragment
    msg
    raw_received

let response_stuttered
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == NeedMoreInput /\
  resp.network_out_len == 0sz /\
  resp.app_out_len == 0sz /\
  st1 == st0 /\
  Seq.equal network_out old_network_out /\
  Seq.equal app_out old_app_out

let network_event_step_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_network_response
    st0
    st1
    resp
    content_type
    fragment
    raw_received
    network_out
    app_out /\
  some_legal_response st0 st1 resp network_out app_out

let lemma_network_event_step_correct_message_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_input_wf st0 content_type fragment raw_received /\
        network_event_step_correct
          st0
          st1
          resp
          content_type
          fragment
          raw_received
          network_out
          app_out /\
        wire_parse_success content_type fragment msg)
      (ensures network_input_message_projection
        st0 content_type fragment msg raw_received)
=
  lemma_legal_network_response_message_projection
    st0
    st1
    resp
    content_type
    fragment
    msg
    raw_received
    network_out
    app_out

let tls_record_step_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out \/
  ((resp.status == DecodeError \/ raw_record_parse_success network_input) /\
   some_legal_response st0 st1 resp network_out app_out /\
   some_legal_response_for_network_input st0 st1 resp network_input network_out app_out)

let network_bytes_step_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  let resp = buffer_resp.response in
  (buffer_resp.consumed_len == 0sz /\
   response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out) \/
  (SZ.v buffer_resp.consumed_len <= B.length network_input /\
   ((resp.status == DecodeError /\ buffer_resp.consumed_len == 0sz) \/
    (resp.status == IllegalTransition /\ buffer_resp.consumed_len == 0sz) \/
    raw_record_parse_success
     (network_consumed_prefix network_input buffer_resp.consumed_len)) /\
   (resp.status == DecodeError ==>
    decode_error_response st0 st1 resp network_out app_out) /\
   (resp.status == IllegalTransition /\ buffer_resp.consumed_len == 0sz ==>
    unexpected_message_response st0 st1 resp network_out app_out) /\
   some_legal_response st0 st1 resp network_out app_out /\
   some_legal_response_for_network_prefix
    st0
    st1
    resp
    network_input
    buffer_resp.consumed_len
    network_out
    app_out)

let network_consumed_raw_record_projection
  (network_input:B.bytes)
  (buffer_resp:client_buffer_response)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  raw_record_parse_success
    (network_consumed_prefix network_input buffer_resp.consumed_len)

let network_bytes_decoded_message_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  buffer_resp.response.status == DecodeError \/
  (exists content_type fragment msg.
    network_input_message_projection
      st0
      content_type
      fragment
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out)

let network_bytes_received_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  buffer_resp.response.status == DecodeError \/
  (exists msg.
    received_tls_raw_delta_legal
      st0
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out)

let network_bytes_protected_record_key_schedule_projection
  (st0:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  buffer_resp.response.status == DecodeError \/
  (exists msg.
    (exists content_type fragment.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len)) /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       protected_record_decode_correct
         st0
         (network_consumed_prefix network_input buffer_resp.consumed_len)
         msg))

let network_bytes_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  buffer_resp.response.status == DecodeError \/
  (exists msg.
    received_tls_raw_delta_legal
      st0
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       protected_record_decode_correct
        st0
        (network_consumed_prefix network_input buffer_resp.consumed_len)
        msg))

let network_bytes_decode_error_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.response.status == DecodeError ==>
    decode_error_response st0 st1 buffer_resp.response network_out app_out /\
    (buffer_resp.consumed_len == 0sz \/
     (SZ.v buffer_resp.consumed_len <= B.length network_input /\
      (exists content_type fragment raw_received.
       Seq.equal raw_received
         (network_consumed_prefix network_input buffer_resp.consumed_len) /\
       network_input_wf st0 content_type fragment raw_received /\
       wire_parse_failure content_type fragment /\
       raw_record_parse_success raw_received)))

let network_bytes_consumed_input_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  (buffer_resp.response.status == DecodeError /\
   network_bytes_decode_error_projection st0 st1 buffer_resp network_input network_out app_out) \/
  (exists msg.
    received_tls_raw_delta_legal
      st0
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out)

let network_bytes_consumed_input_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.consumed_len == 0sz \/
  (buffer_resp.response.status == DecodeError /\
   network_bytes_decode_error_projection st0 st1 buffer_resp network_input network_out app_out) \/
  (exists msg.
    received_tls_raw_delta_legal
      st0
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out /\
    (if CS.network_message_is_cleartext CL.Received msg
     then True
     else
       protected_record_decode_correct
       st0
       (network_consumed_prefix network_input buffer_resp.consumed_len)
       msg))

let connection_control_not_failed
  (st:CS.connection_state)
  : prop =
  match st.CS.cs_model.CS.model_control with
  | CS.ControlFailed _ -> False
  | _ -> True

let lemma_connection_control_not_failed_contradicts_failed
  (st:CS.connection_state)
  (err:T.tls_error)
  : Lemma
      (requires
       connection_control_not_failed st /\
       st.CS.cs_model.CS.model_control == CS.ControlFailed err)
      (ensures False)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlFailed _ -> assert False
  | _ -> assert False

let lemma_legal_response_for_event_nonfailed_previous
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_response_for_event
          st0
          st1
          resp
          ev
          raw_sent
          raw_received
          network_out
          app_out /\
        connection_control_not_failed st1)
      (ensures connection_control_not_failed st0)
=
  if connection_control_not_failed st0 then ()
  else (
    match st0.CS.cs_model.CS.model_control with
    | CS.ControlFailed _ ->
      assert (CS.legal_connection_delta
        st0
        {
          CS.delta_event = ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = raw_received;
        }
        st1);
      assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
      CSL.lemma_step_model_from_failed_results_failed
        st0.CS.cs_model
        ev
        st1.CS.cs_model;
      match st1.CS.cs_model.CS.model_control with
      | CS.ControlFailed err ->
        assert False
      | _ ->
        assert False
    | _ ->
      assert False
  )

let network_bytes_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  connection_control_not_failed st1 ==>
    (buffer_resp.consumed_len == 0sz \/
     exists msg.
       legal_received_tls_response
        st0
        st1
        buffer_resp.response
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len)
        network_out
        app_out)

let lemma_network_bytes_consumed_input_event_projection_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
       network_bytes_consumed_input_event_projection
         st0
         st1
         buffer_resp
         network_input
         network_out
         app_out)
      (ensures
       network_bytes_nonfailed_received_prefix_accepted
         st0
         st1
         buffer_resp
         network_input
         network_out
         app_out)
=
  if connection_control_not_failed st1 then (
    if buffer_resp.consumed_len == 0sz then ()
    else if buffer_resp.response.status == DecodeError then (
      assert (network_bytes_decode_error_projection
       st0
       st1
       buffer_resp
       network_input
       network_out
       app_out);
      assert (decode_error_response st0 st1 buffer_resp.response network_out app_out);
      lemma_decode_error_response_control_failed
       st0
       st1
       buffer_resp.response
       network_out
       app_out;
      lemma_connection_control_not_failed_contradicts_failed
       st1
       tls_decode_error
    ) else (
      assert (exists msg.
       received_tls_raw_delta_legal
         st0
         msg
         (network_consumed_prefix network_input buffer_resp.consumed_len) /\
       decoded_message_event_projection
         st0
         st1
         buffer_resp.response
         msg
         (network_consumed_prefix network_input buffer_resp.consumed_len)
         network_out
         app_out);
      let msg =
       ID.indefinite_description_ghost
         M.tls_message
         (fun msg ->
           received_tls_raw_delta_legal
             st0
             msg
             (network_consumed_prefix network_input buffer_resp.consumed_len) /\
           decoded_message_event_projection
             st0
             st1
             buffer_resp.response
             msg
             (network_consumed_prefix network_input buffer_resp.consumed_len)
             network_out
             app_out) in
      assert (decoded_message_event_projection
       st0
       st1
       buffer_resp.response
       msg
       (network_consumed_prefix network_input buffer_resp.consumed_len)
       network_out
       app_out);
      if legal_received_tls_response
       st0
       st1
       buffer_resp.response
       msg
       (network_consumed_prefix network_input buffer_resp.consumed_len)
       network_out
       app_out
      then (
       assert (exists msg'.
         legal_received_tls_response
           st0
           st1
           buffer_resp.response
           msg'
           (network_consumed_prefix network_input buffer_resp.consumed_len)
           network_out
           app_out)
      ) else (
       assert (unexpected_message_response
         st0
         st1
         buffer_resp.response
         network_out
         app_out);
       lemma_unexpected_message_response_control_failed
         st0
         st1
         buffer_resp.response
         network_out
         app_out;
       lemma_connection_control_not_failed_contradicts_failed
         st1
         tls_unexpected_message_error
      )
    )
  )

let network_bytes_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  response_network_out_seal_projection st0 st1 buffer_resp.response network_out app_out

let local_event_step_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  some_legal_response st0 st1 resp network_out app_out /\
  legal_handled_local_response st0 st1 resp kind payload network_out app_out /\
  response_network_out_parse_success resp network_out

let lemma_legal_handled_local_response_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_handled_local_response st0 st1 resp kind payload network_out app_out)
      (ensures response_network_out_seal_projection st0 st1 resp network_out app_out)
=
  if resp.network_out_len = 0sz then ()
  else if (exists ev raw_sent raw_received.
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
        app_out) then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CS.sent_event_seal_projection st0.CS.cs_model ev raw_sent);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
        st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')
  )
  else if unexpected_message_response st0 st1 resp network_out app_out then (
    assert (CS.sent_event_seal_projection
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
      B.empty);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
        st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')
  )
  else (
    assert (bad_finished_response st0 st1 resp network_out app_out);
    assert (CS.sent_event_seal_projection
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalFail tls_bad_finished_error))
      B.empty);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
        st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')
  )

let lemma_local_event_step_correct_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures response_network_out_seal_projection st0 st1 resp network_out app_out)
=
  lemma_legal_handled_local_response_network_out_seal_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out

let network_bytes_end_to_end_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
  network_consumed_raw_record_projection network_input buffer_resp /\
  network_bytes_decoded_message_projection st0 st1 buffer_resp network_input network_out app_out /\
  network_bytes_received_event_projection st0 st1 buffer_resp network_input network_out app_out /\
  network_bytes_decode_error_projection st0 st1 buffer_resp network_input network_out app_out /\
  network_bytes_consumed_input_event_projection st0 st1 buffer_resp network_input network_out app_out /\
  response_network_out_raw_projection st0 st1 buffer_resp.response network_out app_out /\
  network_bytes_network_out_seal_projection st0 st1 buffer_resp network_input network_out app_out /\
  (client_state_correct st0 ==> client_state_correct st1) /\
  (client_state_correct st0 ==>
    network_bytes_protected_record_key_schedule_projection st0 buffer_resp network_input) /\
  (client_state_correct st0 ==>
    network_bytes_received_decode_projection
      st0 st1 buffer_resp network_input network_out app_out) /\
  (client_state_correct st0 ==>
    network_bytes_consumed_input_projection
      st0 st1 buffer_resp network_input network_out app_out) /\
  (client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection
      st0 st1 buffer_resp.response network_out app_out) /\
  (client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1) /\
  (client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1) /\
  (client_state_correct st0 ==>
   CS.connection_state_sent_seal_key_schedule_replay_consistent st1) /\
  (client_state_correct st0 ==>
   CS.connection_state_received_decode_key_schedule_replay_consistent st1) /\
  (client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1) /\
  (CS.connection_state_sent_seal_replay_consistent st0 ==>
   CS.connection_state_sent_seal_replay_consistent st1) /\
  (CS.connection_state_received_decode_replay_consistent st0 ==>
   CS.connection_state_received_decode_replay_consistent st1)

let lemma_network_bytes_end_to_end_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
      (ensures st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  assert (network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out);
  if response_stuttered
      st0
      st1
      buffer_resp.response
      old_network_out
      network_out
      old_app_out
      app_out
  then
    assert (st1 == st0)
  else (
    assert (some_legal_response st0 st1 buffer_resp.response network_out app_out);
    lemma_some_legal_response_preserves_config
      st0
      st1
      buffer_resp.response
      network_out
      app_out
  )

let lemma_network_bytes_end_to_end_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          network_input
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures
        network_bytes_nonfailed_received_prefix_accepted
          st0
          st1
          buffer_resp
          network_input
          network_out
          app_out)
=
  lemma_network_bytes_consumed_input_event_projection_nonfailed_received_prefix_accepted
    st0
    st1
    buffer_resp
    network_input
    network_out
    app_out

let lemma_network_bytes_end_to_end_nonfailed_previous
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          network_input
          old_network_out
          network_out
          old_app_out
          app_out /\
        connection_control_not_failed st1)
      (ensures connection_control_not_failed st0)
=
  let resp = buffer_resp.response in
  assert (network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out);
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out then (
    assert (st1 == st0)
  ) else (
    assert (some_legal_response_for_network_prefix
      st0 st1 resp network_input buffer_resp.consumed_len network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          raw_received_matches_network_input
            raw_received
            (network_consumed_prefix network_input buffer_resp.consumed_len)) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          raw_received_matches_network_input
            raw_received
            (network_consumed_prefix network_input buffer_resp.consumed_len)) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          raw_received_matches_network_input
            raw_received
            (network_consumed_prefix network_input buffer_resp.consumed_len)) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    lemma_legal_response_for_event_nonfailed_previous
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )

let local_event_end_to_end_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  local_event_step_correct st0 st1 resp kind payload network_out app_out /\
  local_auth_tcb_projection st0 kind payload /\
  local_send_application_data_supported_projection
    st0 st1 resp kind payload network_out app_out /\
  response_network_out_raw_projection st0 st1 resp network_out app_out /\
  response_network_out_seal_projection st0 st1 resp network_out app_out /\
  (client_state_correct st0 ==> client_state_correct st1) /\
  (client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection st0 st1 resp network_out app_out) /\
  (client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1) /\
  (client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1) /\
  (client_state_correct st0 ==>
   CS.connection_state_sent_seal_key_schedule_replay_consistent st1) /\
  (client_state_correct st0 ==>
   CS.connection_state_received_decode_key_schedule_replay_consistent st1) /\
  (client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1) /\
  (CS.connection_state_sent_seal_replay_consistent st0 ==>
   CS.connection_state_sent_seal_replay_consistent st1) /\
  (CS.connection_state_received_decode_replay_consistent st0 ==>
   CS.connection_state_received_decode_replay_consistent st1)

let lemma_local_event_end_to_end_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (_auth:unit{local_auth_tcb_projection st0 kind payload})
  (_app_data:unit{
    local_send_application_data_supported_projection
      st0 st1 resp kind payload network_out app_out})
  (_raw:unit{response_network_out_raw_projection st0 st1 resp network_out app_out})
  (_seal:unit{response_network_out_seal_projection st0 st1 resp network_out app_out})
  (_state:unit{client_state_correct st0 ==> client_state_correct st1})
  (_write_keys:unit{
    client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection st0 st1 resp network_out app_out})
  (_log_view:unit{
    client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1})
  (_raw_event:unit{
    client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1})
  (_sent_key_schedule:unit{
    client_state_correct st0 ==>
    CS.connection_state_sent_seal_key_schedule_replay_consistent st1})
  (_received_key_schedule:unit{
    client_state_correct st0 ==>
    CS.connection_state_received_decode_key_schedule_replay_consistent st1})
  (_end_to_end:unit{
    client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1})
  (_sent_seal:unit{
    CS.connection_state_sent_seal_replay_consistent st0 ==>
    CS.connection_state_sent_seal_replay_consistent st1})
  (_received_decode:unit{
    CS.connection_state_received_decode_replay_consistent st0 ==>
    CS.connection_state_received_decode_replay_consistent st1})
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures local_event_end_to_end_correct st0 st1 resp kind payload network_out app_out)
=
  ()

let lemma_local_event_end_to_end_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_end_to_end_correct st0 st1 resp kind payload network_out app_out)
      (ensures st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  assert (local_event_step_correct st0 st1 resp kind payload network_out app_out);
  assert (some_legal_response st0 st1 resp network_out app_out);
  lemma_some_legal_response_preserves_config st0 st1 resp network_out app_out

let lemma_network_bytes_end_to_end_correct_client_end_to_end_invariant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        client_end_to_end_invariant st0)
      (ensures client_end_to_end_invariant st1)
=
  assert (client_state_correct st0);
  assert (client_state_correct st1);
  lemma_client_state_correct_raw_to_message_replay st1

let lemma_local_event_end_to_end_correct_client_end_to_end_invariant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_event_end_to_end_correct st0 st1 resp kind payload network_out app_out /\
        client_end_to_end_invariant st0)
      (ensures client_end_to_end_invariant st1)
=
  assert (client_state_correct st0);
  assert (client_state_correct st1);
  lemma_client_state_correct_raw_to_message_replay st1

let lemma_network_bytes_step_correct_layered_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        CS.connection_state_layered_log_consistent st0)
      (ensures CS.connection_state_layered_log_consistent st1)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (st1 == st0)
  else lemma_some_legal_response_layered_log_consistent st0 st1 resp network_out app_out

let lemma_network_bytes_step_correct_consumed_raw_record_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
      (ensures network_consumed_raw_record_projection network_input buffer_resp)
=
  let resp = buffer_resp.response in
  if buffer_resp.consumed_len = 0sz then ()
  else (
    assert (raw_record_parse_success
      (network_consumed_prefix network_input buffer_resp.consumed_len));
    assert (network_consumed_raw_record_projection network_input buffer_resp)
  )

let lemma_network_bytes_step_correct_network_out_raw_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
      (ensures
        response_network_out_raw_projection
          st0 st1 buffer_resp.response network_out app_out)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (resp.network_out_len == 0sz)
  else lemma_some_legal_response_network_out_raw_projection st0 st1 resp network_out app_out

let lemma_network_bytes_decoded_message_projection_intro_consumed_zero
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires buffer_resp.consumed_len == 0sz)
      (ensures
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  ()

let lemma_network_bytes_decoded_message_projection_intro_decode_error
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires buffer_resp.response.status == DecodeError)
      (ensures
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  ()

let lemma_network_bytes_decode_error_projection_intro_non_decode_error
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires buffer_resp.response.status == DecodeError ==> False)
      (ensures
        network_bytes_decode_error_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  ()

let lemma_network_bytes_decode_error_projection_intro_consumed_zero
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        buffer_resp.consumed_len == 0sz /\
        (buffer_resp.response.status == DecodeError ==>
          decode_error_response st0 st1 buffer_resp.response network_out app_out))
      (ensures
        network_bytes_decode_error_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  ()

let lemma_network_bytes_decode_error_projection_intro_parse_failure
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        buffer_resp.response.status == DecodeError /\
        decode_error_response st0 st1 buffer_resp.response network_out app_out /\
        SZ.v buffer_resp.consumed_len <= B.length network_input /\
        Seq.equal
          raw_received
          (network_consumed_prefix network_input buffer_resp.consumed_len) /\
        network_input_wf st0 content_type fragment raw_received /\
        wire_parse_failure content_type fragment)
      (ensures
        network_bytes_decode_error_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  lemma_network_input_wf_raw_record_parse_success
    st0
    content_type
    fragment
    raw_received;
  assert (raw_record_parse_success raw_received);
  assert (exists content_type' fragment' raw_received'.
    Seq.equal raw_received'
      (network_consumed_prefix network_input buffer_resp.consumed_len) /\
    network_input_wf st0 content_type' fragment' raw_received' /\
    wire_parse_failure content_type' fragment' /\
    raw_record_parse_success raw_received')

let lemma_network_bytes_decoded_message_projection_intro_handled
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        SZ.v buffer_resp.consumed_len <= B.length network_input /\
        Seq.equal
          raw_received
          (network_consumed_prefix network_input buffer_resp.consumed_len) /\
        network_input_wf st0 content_type fragment raw_received /\
        wire_parse_success content_type fragment msg /\
        legal_handled_tls_response
          st0 st1 buffer_resp.response msg raw_received network_out app_out)
      (ensures
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    Seq.lemma_eq_elim
      raw_received
      (network_consumed_prefix network_input buffer_resp.consumed_len);
    lemma_network_input_wf_message_projection
      st0
      content_type
      fragment
      msg
      raw_received;
    assert (network_input_message_projection
      st0
      content_type
      fragment
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len));
    assert (legal_handled_tls_response
      st0
      st1
      buffer_resp.response
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out);
    lemma_legal_handled_tls_response_decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      content_type
      fragment
      msg
      (network_consumed_prefix network_input buffer_resp.consumed_len)
      network_out
      app_out
  )

let lemma_network_bytes_decoded_message_projection_intro_network_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        SZ.v buffer_resp.consumed_len <= B.length network_input /\
        Seq.equal
          raw_received
          (network_consumed_prefix network_input buffer_resp.consumed_len) /\
        network_input_wf st0 content_type fragment raw_received /\
        legal_network_response
          st0
          st1
          buffer_resp.response
          content_type
          fragment
          raw_received
          network_out
          app_out /\
        (buffer_resp.response.status == DecodeError ==> False))
      (ensures
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  lemma_legal_network_response_handled_of_non_decode_error
    st0
    st1
    buffer_resp.response
    content_type
    fragment
    raw_received
    network_out
    app_out;
  let msg =
    ID.indefinite_description_ghost
      M.tls_message
      (fun msg ->
        wire_parse_success content_type fragment msg /\
        legal_handled_tls_response
          st0 st1 buffer_resp.response msg raw_received network_out app_out) in
  lemma_network_bytes_decoded_message_projection_intro_handled
    st0
    st1
    buffer_resp
    network_input
    content_type
    fragment
    msg
    raw_received
    network_out
    app_out

let lemma_network_bytes_received_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
      (ensures
        network_bytes_received_event_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    let raw_received = network_consumed_prefix network_input buffer_resp.consumed_len in
    assert (exists content_type fragment msg.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        raw_received
        network_out
        app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg -> exists content_type fragment.
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    assert (exists content_type fragment.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        raw_received
        network_out
        app_out);
    let content_type =
      ID.indefinite_description_ghost
        U8.t
        (fun content_type -> exists fragment.
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    let fragment =
      ID.indefinite_description_ghost
        B.bytes
        (fun fragment ->
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    assert (network_input_message_projection
      st0
      content_type
      fragment
      msg
      raw_received);
    assert (received_tls_raw_delta_legal st0 msg raw_received);
    assert (decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      raw_received
      network_out
      app_out);
    assert (exists msg'.
      received_tls_raw_delta_legal st0 msg' raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg'
        raw_received
        network_out
        app_out)
  )

let lemma_network_bytes_consumed_input_event_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_received_event_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        network_bytes_decode_error_projection
          st0 st1 buffer_resp network_input network_out app_out)
      (ensures
        network_bytes_consumed_input_event_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    assert (exists msg.
      received_tls_raw_delta_legal
        st0
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len) /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len)
        network_out
        app_out)
  )

#push-options "--split_queries always --z3refresh"
let lemma_network_bytes_protected_record_key_schedule_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        client_state_correct st0)
      (ensures
        network_bytes_protected_record_key_schedule_projection
          st0 buffer_resp network_input)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    let raw_received = network_consumed_prefix network_input buffer_resp.consumed_len in
    assert (exists content_type fragment msg.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        raw_received
        network_out
        app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg -> exists content_type fragment.
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    assert (exists content_type fragment.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        raw_received
        network_out
        app_out);
    let content_type =
      ID.indefinite_description_ghost
        U8.t
        (fun content_type -> exists fragment.
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    let fragment =
      ID.indefinite_description_ghost
        B.bytes
        (fun fragment ->
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    assert (network_input_message_projection
      st0
      content_type
      fragment
      msg
      raw_received);
    if CS.network_message_is_cleartext CL.Received msg
    then ()
    else (
      assert (protected_decoder_fragment_relation st0 content_type fragment raw_received);
      assert (protected_record_decodes_to_message st0 raw_received msg);
      lemma_protected_decoder_fragment_relation_read_key_schedule_projection
        st0
        content_type
        fragment
        raw_received;
      assert (protected_record_decode_uses_scheduled_read_key st0 raw_received);
      assert (protected_record_decode_correct st0 raw_received msg)
    );
    assert (exists msg'.
      (exists content_type' fragment'.
        network_input_message_projection
          st0
          content_type'
          fragment'
          msg'
          raw_received) /\
      (if CS.network_message_is_cleartext CL.Received msg'
       then True
       else protected_record_decode_correct st0 raw_received msg'))
  )
#pop-options


#push-options "--split_queries always --z3refresh"
let lemma_network_bytes_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
       network_bytes_decoded_message_projection
         st0 st1 buffer_resp network_input network_out app_out /\
       client_state_correct st0)
      (ensures
       network_bytes_received_decode_projection
         st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    let raw_received = network_consumed_prefix network_input buffer_resp.consumed_len in
    assert (exists content_type fragment msg.
      network_input_message_projection
       st0
       content_type
       fragment
       msg
       raw_received /\
      decoded_message_event_projection
       st0
       st1
       buffer_resp.response
       msg
       raw_received
       network_out
       app_out);
    let msg =
      ID.indefinite_description_ghost
       M.tls_message
       (fun msg -> exists content_type fragment.
         network_input_message_projection
           st0
           content_type
           fragment
           msg
           raw_received /\
         decoded_message_event_projection
           st0
           st1
           buffer_resp.response
           msg
           raw_received
           network_out
           app_out) in
    assert (exists content_type fragment.
      network_input_message_projection
       st0
       content_type
       fragment
       msg
       raw_received /\
      decoded_message_event_projection
       st0
       st1
       buffer_resp.response
       msg
       raw_received
       network_out
       app_out);
    let content_type =
      ID.indefinite_description_ghost
       U8.t
       (fun content_type -> exists fragment.
         network_input_message_projection
           st0
           content_type
           fragment
           msg
           raw_received /\
         decoded_message_event_projection
           st0
           st1
           buffer_resp.response
           msg
           raw_received
           network_out
           app_out) in
    let fragment =
      ID.indefinite_description_ghost
       B.bytes
       (fun fragment ->
         network_input_message_projection
           st0
           content_type
           fragment
           msg
           raw_received /\
         decoded_message_event_projection
           st0
           st1
           buffer_resp.response
           msg
           raw_received
           network_out
           app_out) in
    assert (network_input_message_projection
      st0
      content_type
      fragment
      msg
      raw_received);
    assert (received_tls_raw_delta_legal st0 msg raw_received);
    assert (decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      raw_received
      network_out
      app_out);
    if CS.network_message_is_cleartext CL.Received msg
    then ()
    else (
      assert (protected_decoder_fragment_relation st0 content_type fragment raw_received);
      assert (protected_record_decodes_to_message st0 raw_received msg);
      lemma_protected_decoder_fragment_relation_read_key_schedule_projection
       st0
       content_type
       fragment
       raw_received;
      assert (protected_record_decode_uses_scheduled_read_key st0 raw_received);
      assert (protected_record_decode_correct st0 raw_received msg)
    );
    assert (exists msg'.
      received_tls_raw_delta_legal st0 msg' raw_received /\
      decoded_message_event_projection
       st0
       st1
       buffer_resp.response
       msg'
       raw_received
       network_out
       app_out /\
      (if CS.network_message_is_cleartext CL.Received msg'
       then True
       else protected_record_decode_correct st0 raw_received msg'))
  )
#pop-options

let lemma_network_bytes_consumed_input_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
       network_bytes_received_decode_projection
         st0 st1 buffer_resp network_input network_out app_out /\
       network_bytes_decode_error_projection
         st0 st1 buffer_resp network_input network_out app_out)
      (ensures
       network_bytes_consumed_input_projection
         st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.consumed_len = 0sz then ()
  else if buffer_resp.response.status == DecodeError then ()
  else (
    assert (exists msg.
      received_tls_raw_delta_legal
       st0
       msg
       (network_consumed_prefix network_input buffer_resp.consumed_len) /\
      decoded_message_event_projection
       st0
       st1
       buffer_resp.response
       msg
       (network_consumed_prefix network_input buffer_resp.consumed_len)
       network_out
       app_out /\
      (if CS.network_message_is_cleartext CL.Received msg
       then True
       else
       protected_record_decode_correct
         st0
         (network_consumed_prefix network_input buffer_resp.consumed_len)
         msg))
  )

let lemma_decode_error_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires decode_error_response st0 st1 resp network_out app_out)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  let ev = CS.ConnLocalEvent (CS.LocalFail tls_decode_error) in
  assert (legal_response_for_event
    st0 st1 resp ev B.empty B.empty network_out app_out);
  assert (B.length B.empty == 0);
  assert (CS.received_event_nonempty_decode_projection st0.CS.cs_model ev B.empty);
  lemma_legal_response_for_event_response_received_decode_projection
    st0
    st1
    resp
    ev
    B.empty
    B.empty
    network_out
    app_out

let lemma_unexpected_message_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires unexpected_message_response st0 st1 resp network_out app_out)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  let ev = CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error) in
  assert (legal_response_for_event
    st0 st1 resp ev B.empty B.empty network_out app_out);
  assert (B.length B.empty == 0);
  assert (CS.received_event_nonempty_decode_projection st0.CS.cs_model ev B.empty);
  lemma_legal_response_for_event_response_received_decode_projection
    st0
    st1
    resp
    ev
    B.empty
    B.empty
    network_out
    app_out

let lemma_bad_finished_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires bad_finished_response st0 st1 resp network_out app_out)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  let ev = CS.ConnLocalEvent (CS.LocalFail tls_bad_finished_error) in
  assert (legal_response_for_event
    st0 st1 resp ev B.empty B.empty network_out app_out);
  assert (B.length B.empty == 0);
  assert (CS.received_event_nonempty_decode_projection st0.CS.cs_model ev B.empty);
  lemma_legal_response_for_event_response_received_decode_projection
    st0
    st1
    resp
    ev
    B.empty
    B.empty
    network_out
    app_out

let lemma_decoded_message_event_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        decoded_message_event_projection
          st0 st1 resp msg raw_received network_out app_out /\
        (if CS.network_message_is_cleartext CL.Received msg
         then True
         else protected_record_decodes_to_message st0 raw_received msg))
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  if legal_received_tls_response st0 st1 resp msg raw_received network_out app_out
  then (
    let ev = CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = msg;
    } in
    assert (legal_response_for_event
      st0 st1 resp ev B.empty raw_received network_out app_out);
    if CS.network_message_is_cleartext CL.Received msg
    then (
      assert (CS.received_event_decode_projection st0.CS.cs_model ev raw_received);
      assert (CS.received_event_nonempty_decode_projection st0.CS.cs_model ev raw_received)
    )
    else (
      assert (CS.protected_record_count CL.Received msg == 1);
      lemma_protected_record_decodes_to_received_single_decode st0 raw_received msg;
      assert (CS.received_single_protected_message_decode st0.CS.cs_model msg raw_received);
      assert (CS.received_event_decode_projection st0.CS.cs_model ev raw_received);
      assert (CS.received_event_nonempty_decode_projection st0.CS.cs_model ev raw_received)
    );
    lemma_legal_response_for_event_response_received_decode_projection
      st0
      st1
      resp
      ev
      B.empty
      raw_received
      network_out
      app_out
  )
  else (
    assert (received_tls_raw_delta_legal st0 msg raw_received /\
      unexpected_message_response st0 st1 resp network_out app_out);
    lemma_unexpected_message_response_received_decode_projection
      st0
      st1
      resp
      network_out
      app_out
  )

let lemma_legal_handled_local_response_received_decode_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_handled_local_response st0 st1 resp kind payload network_out app_out)
      (ensures response_received_decode_projection st0 st1 resp network_out app_out)
=
  if (exists ev raw_sent raw_received.
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
        app_out) then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (legal_delta st0 st1 ev raw_sent raw_received);
    match ev with
    | CS.ConnLocalEvent _ ->
      assert (Seq.equal raw_received B.empty);
      Seq.lemma_eq_elim raw_received B.empty
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction with
       | CL.Sent ->
         assert (Seq.equal raw_received B.empty);
         Seq.lemma_eq_elim raw_received B.empty
       | CL.Received ->
         assert (local_event_kind_matches st0 kind payload ev);
         assert False);
    assert (B.length raw_received == 0);
    assert (CS.received_event_nonempty_decode_projection
      st0.CS.cs_model
      ev
      raw_received);
    lemma_legal_response_for_event_response_received_decode_projection
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out
  )
  else if unexpected_message_response st0 st1 resp network_out app_out then (
    lemma_unexpected_message_response_received_decode_projection
      st0
      st1
      resp
      network_out
      app_out
  )
  else (
    assert (bad_finished_response st0 st1 resp network_out app_out);
    lemma_bad_finished_response_received_decode_projection
      st0
      st1
      resp
      network_out
      app_out
  )

let lemma_legal_handled_local_response_app_data_supported_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_handled_local_response st0 st1 resp kind payload network_out app_out)
      (ensures local_send_application_data_supported_projection
        st0 st1 resp kind payload network_out app_out)
=
  if kind == LocalSendApplicationData && resp.status == StepOk then (
    if (exists ev raw_sent raw_received.
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
          app_out) then (
      let ev =
        ID.indefinite_description_ghost
          CS.conn_event
          (fun ev -> exists raw_sent raw_received.
            legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_sent =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_sent -> exists raw_received.
            legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_received =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_received ->
            legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      assert (local_event_kind_matches st0 kind payload ev);
      assert (local_event_supported_profile kind payload ev);
      match ev with
      | CS.ConnNetworkEvent msg ->
        assert (msg.CL.message_direction == CL.Sent);
        (match msg.CL.message_value with
         | M.TlsApplicationData bytes ->
           assert (Seq.equal bytes payload);
           Seq.lemma_eq_elim bytes payload;
           assert (B.length payload <= SM.max_application_data_fragment_len);
           assert (CS.protected_record_count CL.Sent (M.TlsApplicationData payload) == 1)
         | _ -> assert False)
      | CS.ConnLocalEvent _ ->
        assert False
    )
    else if unexpected_message_response st0 st1 resp network_out app_out then (
      assert (resp.status == IllegalTransition);
      assert False
    )
    else (
      assert (bad_finished_response st0 st1 resp network_out app_out);
      assert (resp.status == ConnectionFailed);
      assert False
    )
  )

let lemma_network_bytes_step_correct_received_decode_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures
        CS.connection_state_received_decode_replay_consistent st1 /\
        (response_stuttered
          st0
          st1
          buffer_resp.response
          old_network_out
          network_out
          old_app_out
          app_out \/
         response_received_decode_projection
          st0
          st1
          buffer_resp.response
          network_out
          app_out))
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (st1 == st0)
  else (
    assert (some_legal_response st0 st1 resp network_out app_out);
    if buffer_resp.consumed_len = 0sz then (
      Seq.lemma_len_slice network_input 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice network_input 0 0);
      assert (Seq.equal
        (network_consumed_prefix network_input buffer_resp.consumed_len)
        B.empty);
      assert (some_legal_response_for_network_input
        st0 st1 resp B.empty network_out app_out);
      lemma_some_legal_response_for_empty_network_input_received_decode_projection
        st0
        st1
        resp
        network_out
        app_out
    )
    else if resp.status == DecodeError then (
      assert (decode_error_response st0 st1 resp network_out app_out);
      lemma_decode_error_response_received_decode_projection
        st0
        st1
        resp
        network_out
        app_out
    )
    else (
      let raw_received =
        network_consumed_prefix network_input buffer_resp.consumed_len in
      assert (exists content_type fragment msg.
        network_input_message_projection
          st0
          content_type
          fragment
          msg
          raw_received /\
        decoded_message_event_projection
          st0
          st1
          resp
          msg
          raw_received
          network_out
          app_out);
      let msg =
        ID.indefinite_description_ghost
          M.tls_message
          (fun msg -> exists content_type fragment.
            network_input_message_projection
              st0
              content_type
              fragment
              msg
              raw_received /\
            decoded_message_event_projection
              st0
              st1
              resp
              msg
              raw_received
              network_out
              app_out) in
      assert (exists content_type fragment.
        network_input_message_projection
          st0
          content_type
          fragment
          msg
          raw_received /\
        decoded_message_event_projection
          st0
          st1
          resp
          msg
          raw_received
          network_out
          app_out);
      let content_type =
        ID.indefinite_description_ghost
          U8.t
          (fun content_type -> exists fragment.
            network_input_message_projection
              st0
              content_type
              fragment
              msg
              raw_received /\
            decoded_message_event_projection
              st0
              st1
              resp
              msg
              raw_received
              network_out
              app_out) in
      let fragment =
        ID.indefinite_description_ghost
          B.bytes
          (fun fragment ->
            network_input_message_projection
              st0
              content_type
              fragment
              msg
              raw_received /\
            decoded_message_event_projection
              st0
              st1
              resp
              msg
              raw_received
              network_out
              app_out) in
      assert (network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received);
      assert (decoded_message_event_projection
        st0
        st1
        resp
        msg
        raw_received
        network_out
        app_out);
      if CS.network_message_is_cleartext CL.Received msg
      then ()
      else assert (protected_record_decodes_to_message st0 raw_received msg);
      lemma_decoded_message_event_response_received_decode_projection
        st0
        st1
        resp
        msg
        raw_received
        network_out
        app_out
    );
    assert (response_received_decode_projection st0 st1 resp network_out app_out);
    lemma_some_legal_response_received_decode_replay_consistent
      st0
      st1
      resp
      network_out
      app_out
  )

let lemma_decode_error_response_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires decode_error_response st0 st1 resp network_out app_out)
      (ensures response_network_out_seal_projection st0 st1 resp network_out app_out)
=
  assert (legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_decode_error))
    B.empty
    B.empty
    network_out
    app_out);
  assert (CS.sent_event_seal_projection
    st0.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalFail tls_decode_error))
    B.empty);
  assert (exists ev' raw_sent' raw_received'.
    legal_response_for_event
      st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
    CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')

let lemma_unexpected_message_response_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires unexpected_message_response st0 st1 resp network_out app_out)
      (ensures response_network_out_seal_projection st0 st1 resp network_out app_out)
=
  assert (legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
    B.empty
    B.empty
    network_out
    app_out);
  assert (CS.sent_event_seal_projection
    st0.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
    B.empty);
  assert (exists ev' raw_sent' raw_received'.
    legal_response_for_event
      st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
    CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')

let lemma_decoded_message_event_response_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
       decoded_message_event_projection
         st0 st1 resp msg raw_received network_out app_out)
      (ensures response_network_out_seal_projection st0 st1 resp network_out app_out)
=
  if legal_received_tls_response st0 st1 resp msg raw_received network_out app_out
  then (
    assert (legal_response_for_event
      st0
      st1
      resp
      (CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = msg;
      })
      B.empty
      raw_received
      network_out
      app_out);
    assert (CS.sent_event_seal_projection
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = msg;
      })
      B.empty);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
       st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')
  )
  else (
    assert (unexpected_message_response st0 st1 resp network_out app_out);
    assert (legal_response_for_event
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out);
    assert (CS.sent_event_seal_projection
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
      B.empty);
    assert (exists ev' raw_sent' raw_received'.
      legal_response_for_event
       st0 st1 resp ev' raw_sent' raw_received' network_out app_out /\
      CS.sent_event_seal_projection st0.CS.cs_model ev' raw_sent')
  )

#push-options "--split_queries always"
let lemma_network_bytes_decoded_message_network_out_seal_projection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out)
      (ensures
        network_bytes_network_out_seal_projection
          st0 st1 buffer_resp network_input network_out app_out)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then (
    assert (resp.network_out_len == 0sz);
    assert (response_network_out_seal_projection st0 st1 resp network_out app_out);
    assert (network_bytes_network_out_seal_projection
      st0 st1 buffer_resp network_input network_out app_out)
  )
  else if resp.status == DecodeError then (
    assert (response_stuttered
      st0 st1 resp old_network_out network_out old_app_out app_out ==> False);
    assert (SZ.v buffer_resp.consumed_len <= B.length network_input /\
      ((resp.status == DecodeError /\ buffer_resp.consumed_len == 0sz) \/
       raw_record_parse_success
        (network_consumed_prefix network_input buffer_resp.consumed_len)) /\
      (resp.status == DecodeError ==>
       decode_error_response st0 st1 resp network_out app_out) /\
      some_legal_response st0 st1 resp network_out app_out /\
      some_legal_response_for_network_prefix
        st0
        st1
        resp
        network_input
        buffer_resp.consumed_len
        network_out
        app_out);
    assert (decode_error_response st0 st1 resp network_out app_out);
    lemma_decode_error_response_network_out_seal_projection
      st0
      st1
      resp
      network_out
      app_out;
    assert (network_bytes_network_out_seal_projection
      st0 st1 buffer_resp network_input network_out app_out)
  )
  else (
    assert (response_stuttered
      st0 st1 resp old_network_out network_out old_app_out app_out ==> False);
    assert (resp.status == DecodeError ==> False);
    assert (SZ.v buffer_resp.consumed_len <= B.length network_input /\
      ((resp.status == DecodeError /\ buffer_resp.consumed_len == 0sz) \/
       (resp.status == IllegalTransition /\ buffer_resp.consumed_len == 0sz) \/
       raw_record_parse_success
        (network_consumed_prefix network_input buffer_resp.consumed_len)) /\
      (resp.status == DecodeError ==>
       decode_error_response st0 st1 resp network_out app_out) /\
      (resp.status == IllegalTransition /\ buffer_resp.consumed_len == 0sz ==>
       unexpected_message_response st0 st1 resp network_out app_out) /\
      some_legal_response st0 st1 resp network_out app_out /\
      some_legal_response_for_network_prefix
        st0
        st1
        resp
        network_input
        buffer_resp.consumed_len
        network_out
        app_out);
    if resp.status == IllegalTransition && buffer_resp.consumed_len = 0sz then (
      assert (unexpected_message_response st0 st1 resp network_out app_out);
      lemma_unexpected_message_response_network_out_seal_projection
        st0
        st1
        resp
        network_out
        app_out;
      assert (network_bytes_network_out_seal_projection
        st0 st1 buffer_resp network_input network_out app_out)
    ) else (
    assert (raw_record_parse_success
      (network_consumed_prefix network_input buffer_resp.consumed_len));
    if buffer_resp.consumed_len = 0sz then (
      let raw_received = network_consumed_prefix network_input buffer_resp.consumed_len in
      lemma_raw_record_parse_success_nonempty raw_received;
      assert (SZ.v buffer_resp.consumed_len == 0);
      assert (network_consumed_prefix network_input buffer_resp.consumed_len ==
        Seq.slice network_input 0 0);
      Seq.lemma_len_slice network_input 0 0;
      assert (B.length raw_received == 0);
      assert False
    );
    let raw_received = network_consumed_prefix network_input buffer_resp.consumed_len in
    assert (exists content_type fragment msg.
      network_input_message_projection
        st0
        content_type
        fragment
        msg
        raw_received /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        raw_received
        network_out
        app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg -> exists content_type fragment.
          network_input_message_projection
            st0
            content_type
            fragment
            msg
            raw_received /\
          decoded_message_event_projection
            st0
            st1
            buffer_resp.response
            msg
            raw_received
            network_out
            app_out) in
    assert (decoded_message_event_projection
      st0
      st1
      buffer_resp.response
      msg
      raw_received
      network_out
      app_out);
    lemma_decoded_message_event_response_network_out_seal_projection
      st0
      st1
      buffer_resp.response
      msg
      raw_received
      network_out
      app_out;
    assert (network_bytes_network_out_seal_projection
      st0 st1 buffer_resp network_input network_out app_out)
    )
  )
#pop-options

let lemma_network_bytes_step_correct_client_state_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (st1 == st0)
  else (
    lemma_network_bytes_decoded_message_network_out_seal_projection
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out;
    lemma_network_bytes_step_correct_received_decode_replay_consistent
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out;
    assert (response_received_decode_projection
      st0
      st1
      resp
      network_out
      app_out);
    lemma_some_legal_response_client_state_correct st0 st1 resp network_out app_out
  )

let lemma_network_bytes_step_correct_sent_seal_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        network_bytes_network_out_seal_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        CS.connection_state_sent_seal_replay_consistent st0)
      (ensures CS.connection_state_sent_seal_replay_consistent st1)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (st1 == st0)
  else (
    assert (some_legal_response st0 st1 resp network_out app_out);
    assert (response_network_out_seal_projection st0 st1 resp network_out app_out);
    lemma_some_legal_response_sent_seal_replay_consistent
      st0
      st1
      resp
      network_out
      app_out
  )

#push-options "--split_queries always --z3refresh --z3rlimit_factor 4"
let lemma_network_bytes_step_correct_end_to_end
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_step_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        network_bytes_decoded_message_projection
          st0 st1 buffer_resp network_input network_out app_out /\
        network_bytes_decode_error_projection
          st0 st1 buffer_resp network_input network_out app_out)
      (ensures
        network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
=
  lemma_network_bytes_step_correct_consumed_raw_record_projection
    st0
    st1
    buffer_resp
    network_input
    old_network_out
    network_out
    old_app_out
    app_out;
  lemma_network_bytes_received_event_projection
    st0
    st1
    buffer_resp
    network_input
    network_out
    app_out;
  lemma_network_bytes_consumed_input_event_projection
    st0
    st1
    buffer_resp
    network_input
    network_out
    app_out;
  lemma_network_bytes_step_correct_network_out_raw_projection
    st0
    st1
    buffer_resp
    network_input
    old_network_out
    network_out
    old_app_out
    app_out;
  lemma_network_bytes_decoded_message_network_out_seal_projection
    st0
    st1
    buffer_resp
    network_input
    old_network_out
    network_out
    old_app_out
    app_out;
  if CS.connection_state_sent_seal_replay_consistent st0 then (
    if response_stuttered st0 st1 buffer_resp.response old_network_out network_out old_app_out app_out
    then assert (st1 == st0)
    else (
      assert (some_legal_response st0 st1 buffer_resp.response network_out app_out);
      assert (response_network_out_seal_projection st0 st1 buffer_resp.response network_out app_out);
      lemma_some_legal_response_sent_seal_replay_consistent
        st0
        st1
        buffer_resp.response
        network_out
        app_out)
  );
  if CS.connection_state_received_decode_replay_consistent st0 then (
    lemma_network_bytes_step_correct_received_decode_replay_consistent
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out
  );
  if client_state_correct st0 then (
    if response_stuttered st0 st1 buffer_resp.response old_network_out network_out old_app_out app_out
    then assert (buffer_resp.response.network_out_len == 0sz)
    else lemma_some_legal_response_network_out_write_key_schedule_projection
      st0
      st1
      buffer_resp.response
      network_out
      app_out;
    lemma_network_bytes_protected_record_key_schedule_projection
      st0
      st1
      buffer_resp
      network_input
      network_out
      app_out;
    lemma_network_bytes_received_decode_projection
      st0
      st1
      buffer_resp
      network_input
      network_out
      app_out;
    lemma_network_bytes_consumed_input_projection
      st0
      st1
      buffer_resp
      network_input
      network_out
      app_out;
    lemma_network_bytes_step_correct_client_state_correct
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out
  );
  if client_end_to_end_invariant st0 then (
    assert (client_state_correct st0);
    assert (client_state_correct st1);
    lemma_client_state_correct_raw_to_message_replay st1
  )
#pop-options 

let lemma_local_event_step_correct_layered_log_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_event_step_correct st0 st1 resp kind payload network_out app_out /\
        CS.connection_state_layered_log_consistent st0)
      (ensures CS.connection_state_layered_log_consistent st1)
=
  lemma_some_legal_response_layered_log_consistent st0 st1 resp network_out app_out

let lemma_local_event_step_correct_client_state_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_event_step_correct st0 st1 resp kind payload network_out app_out /\
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  lemma_local_event_step_correct_network_out_seal_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_legal_handled_local_response_received_decode_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_some_legal_response_client_state_correct st0 st1 resp network_out app_out

let lemma_local_event_step_correct_client_state_correct_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures client_state_correct st0 ==> client_state_correct st1)
=
  if client_state_correct st0 then
    lemma_local_event_step_correct_client_state_correct
      st0
      st1
      resp
      kind
      payload
      network_out
      app_out

let lemma_local_event_step_correct_write_key_schedule_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        client_state_correct st0 ==>
        response_network_out_write_key_schedule_projection st0 st1 resp network_out app_out)
=
  assert (some_legal_response st0 st1 resp network_out app_out);
  if client_state_correct st0 then
    lemma_some_legal_response_network_out_write_key_schedule_projection
      st0
      st1
      resp
      network_out
      app_out

let lemma_local_event_step_correct_connection_log_view_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        client_state_correct st0 ==>
        CS.connection_state_connection_log_view_consistent st1)
=
  lemma_local_event_step_correct_client_state_correct_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_state_correct st0 then (
    assert (client_state_correct st1);
    assert (CS.connection_state_connection_log_view_consistent st1)
  )

let lemma_local_event_step_correct_raw_event_replay_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        client_state_correct st0 ==>
        CS.connection_state_raw_event_replay_consistent st1)
=
  lemma_local_event_step_correct_client_state_correct_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_state_correct st0 then (
    assert (client_state_correct st1);
    assert (CS.connection_state_raw_event_replay_consistent st1)
  )

let lemma_local_event_step_correct_sent_key_schedule_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        client_state_correct st0 ==>
        CS.connection_state_sent_seal_key_schedule_replay_consistent st1)
=
  lemma_local_event_step_correct_client_state_correct_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_state_correct st0 then (
    assert (client_state_correct st1);
    assert (CS.connection_state_sent_seal_key_schedule_replay_consistent st1)
  )

let lemma_local_event_step_correct_received_key_schedule_imp
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        client_state_correct st0 ==>
        CS.connection_state_received_decode_key_schedule_replay_consistent st1)
=
  lemma_local_event_step_correct_client_state_correct_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_state_correct st0 then (
    assert (client_state_correct st1);
    assert (CS.connection_state_received_decode_key_schedule_replay_consistent st1)
  )

let lemma_local_event_step_correct_received_decode_replay_consistent
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_event_step_correct st0 st1 resp kind payload network_out app_out /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures CS.connection_state_received_decode_replay_consistent st1)
=
  lemma_legal_handled_local_response_received_decode_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_some_legal_response_received_decode_replay_consistent
    st0
    st1
    resp
    network_out
    app_out

let lemma_local_event_step_correct_client_end_to_end_invariant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_event_step_correct st0 st1 resp kind payload network_out app_out /\
        client_end_to_end_invariant st0)
      (ensures client_end_to_end_invariant st1)
=
  assert (client_state_correct st0);
  lemma_local_event_step_correct_client_state_correct
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  assert (client_state_correct st1);
  lemma_client_state_correct_raw_to_message_replay st1

#push-options "--split_queries always --z3refresh --z3rlimit 10"
let lemma_local_event_step_correct_end_to_end
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        local_input_wf st0 kind payload /\
        local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        local_event_end_to_end_correct st0 st1 resp kind payload network_out app_out)
=
  lemma_local_input_wf_auth_tcb_projection st0 kind payload;
  assert (local_auth_tcb_projection st0 kind payload);
  lemma_legal_handled_local_response_app_data_supported_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  assert (local_send_application_data_supported_projection
    st0 st1 resp kind payload network_out app_out);
  assert (some_legal_response st0 st1 resp network_out app_out);
  lemma_some_legal_response_network_out_raw_projection st0 st1 resp network_out app_out;
  assert (response_network_out_raw_projection st0 st1 resp network_out app_out);
  lemma_local_event_step_correct_network_out_seal_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  assert (response_network_out_seal_projection st0 st1 resp network_out app_out);
  lemma_local_event_step_correct_client_state_correct_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_local_event_step_correct_write_key_schedule_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_local_event_step_correct_connection_log_view_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_local_event_step_correct_raw_event_replay_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_local_event_step_correct_sent_key_schedule_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  lemma_local_event_step_correct_received_key_schedule_imp
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_end_to_end_invariant st0 then (
    lemma_local_event_step_correct_client_end_to_end_invariant
      st0
      st1
      resp
      kind
      payload
      network_out
      app_out;
    assert (client_end_to_end_invariant st1)
  );
  assert (client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1);
  if CS.connection_state_sent_seal_replay_consistent st0 then (
    lemma_some_legal_response_sent_seal_replay_consistent
      st0
      st1
      resp
      network_out
      app_out;
    assert (CS.connection_state_sent_seal_replay_consistent st1)
  );
  assert (CS.connection_state_sent_seal_replay_consistent st0 ==>
    CS.connection_state_sent_seal_replay_consistent st1);
  if CS.connection_state_received_decode_replay_consistent st0 then (
    lemma_local_event_step_correct_received_decode_replay_consistent
      st0
      st1
      resp
      kind
      payload
      network_out
      app_out;
    assert (CS.connection_state_received_decode_replay_consistent st1)
  );
  assert (CS.connection_state_received_decode_replay_consistent st0 ==>
    CS.connection_state_received_decode_replay_consistent st1);
  let p_auth = (() <: (_:unit{local_auth_tcb_projection st0 kind payload})) in
  let p_app_data = (() <: (_:unit{
    local_send_application_data_supported_projection
      st0 st1 resp kind payload network_out app_out})) in
  let p_raw = (() <: (_:unit{response_network_out_raw_projection st0 st1 resp network_out app_out})) in
  let p_seal = (() <: (_:unit{response_network_out_seal_projection st0 st1 resp network_out app_out})) in
  let p_state = (() <: (_:unit{client_state_correct st0 ==> client_state_correct st1})) in
  let p_write_keys = (() <: (_:unit{
    client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection st0 st1 resp network_out app_out})) in
  let p_log_view = (() <: (_:unit{
    client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1})) in
  let p_raw_event = (() <: (_:unit{
    client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1})) in
  let p_sent_key_schedule = (() <: (_:unit{
    client_state_correct st0 ==>
    CS.connection_state_sent_seal_key_schedule_replay_consistent st1})) in
  let p_received_key_schedule = (() <: (_:unit{
    client_state_correct st0 ==>
    CS.connection_state_received_decode_key_schedule_replay_consistent st1})) in
  let p_end_to_end = (() <: (_:unit{
    client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1})) in
  let p_sent_seal = (() <: (_:unit{
    CS.connection_state_sent_seal_replay_consistent st0 ==>
    CS.connection_state_sent_seal_replay_consistent st1})) in
  let p_received_decode = (() <: (_:unit{
    CS.connection_state_received_decode_replay_consistent st0 ==>
    CS.connection_state_received_decode_replay_consistent st1})) in
  lemma_local_event_end_to_end_correct_intro
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out
    p_auth
    p_app_data
    p_raw
    p_seal
    p_state
    p_write_keys
    p_log_view
    p_raw_event
    p_sent_key_schedule
    p_received_key_schedule
    p_end_to_end
    p_sent_seal
    p_received_decode
#pop-options

let lemma_legal_network_response_decode_error
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires wire_parse_failure content_type fragment /\
                decode_error_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_unexpected
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (ct:T.content_type)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg /\
                unexpected_message_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_unexpected_from_parse_success
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires (exists ct msg.
                  L.content_type_matches content_type ct /\
                  WS.parse_tls_message ct fragment == Some msg) /\
                unexpected_message_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_handled
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (ct:T.content_type)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg /\
                legal_handled_tls_response
                  st0
                  st1
                  resp
                  msg
                  raw_received
                  network_out
                  app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_handled_from_parse_success
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires wire_parse_success content_type fragment msg /\
                legal_handled_tls_response
                  st0
                  st1
                  resp
                  msg
                  raw_received
                  network_out
                  app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_decode_error_response_for_network_input
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires decode_error_response st0 st1 resp network_out app_out)
      (ensures some_legal_response_for_network_input
        st0 st1 resp network_input network_out app_out)
=
  ()

let lemma_unexpected_message_response_for_network_input
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires unexpected_message_response st0 st1 resp network_out app_out)
      (ensures some_legal_response_for_network_input
        st0 st1 resp network_input network_out app_out)
=
  ()

let lemma_legal_network_response_for_network_input
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
      (ensures some_legal_response_for_network_input
        st0 st1 resp raw_received network_out app_out)
=
  ()

let lemma_some_legal_response_for_equal_network_input
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_input0:B.bytes)
  (network_input1:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires some_legal_response_for_network_input
        st0 st1 resp network_input0 network_out app_out /\
        Seq.equal network_input0 network_input1)
      (ensures some_legal_response_for_network_input
        st0 st1 resp network_input1 network_out app_out)
=
  Seq.lemma_eq_elim network_input0 network_input1

(**
  Ghost-only driver traces for the exported buffer/event API.

  The cumulative `connection_state` raw log remains an accepted-event log:
  every non-stuttering step below contributes exactly the raw delta of a
  `legal_response_for_event`.  Rejected consumed network input is not added to
  that cumulative log; instead, the per-step theorem derives a local witness
  classifying the consumed prefix.
**)

noextract
type network_driver_step = {
  network_driver_st0: CS.connection_state;
  network_driver_st1: CS.connection_state;
  network_driver_buffer_resp: client_buffer_response;
  network_driver_input: B.bytes;
  network_driver_old_network_out: B.bytes;
  network_driver_network_out: B.bytes;
  network_driver_old_app_out: B.bytes;
  network_driver_app_out: B.bytes;
}

noextract
type local_driver_step = {
  local_driver_st0: CS.connection_state;
  local_driver_st1: CS.connection_state;
  local_driver_resp: client_response;
  local_driver_kind: local_event_kind;
  local_driver_payload: B.bytes;
  local_driver_network_out: B.bytes;
  local_driver_app_out: B.bytes;
}

noextract
type driver_step =
  | DriverNetworkStep of network_driver_step
  | DriverLocalStep of local_driver_step

noextract
let driver_step_st0 (step:driver_step) : CS.connection_state =
  match step with
  | DriverNetworkStep n -> n.network_driver_st0
  | DriverLocalStep l -> l.local_driver_st0

noextract
let driver_step_st1 (step:driver_step) : CS.connection_state =
  match step with
  | DriverNetworkStep n -> n.network_driver_st1
  | DriverLocalStep l -> l.local_driver_st1

noextract
let driver_step_correct (step:driver_step) : prop =
  match step with
  | DriverNetworkStep n ->
    network_bytes_end_to_end_correct
      n.network_driver_st0
      n.network_driver_st1
      n.network_driver_buffer_resp
      n.network_driver_input
      n.network_driver_old_network_out
      n.network_driver_network_out
      n.network_driver_old_app_out
      n.network_driver_app_out
  | DriverLocalStep l ->
    local_event_end_to_end_correct
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      l.local_driver_kind
      l.local_driver_payload
      l.local_driver_network_out
      l.local_driver_app_out

noextract
let network_decode_error_rejected_input_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.response.status == DecodeError ==>
    buffer_resp.consumed_len == 0sz \/
    (SZ.v buffer_resp.consumed_len <= B.length network_input /\
     (exists content_type fragment raw_received.
       Seq.equal raw_received
         (network_consumed_prefix network_input buffer_resp.consumed_len) /\
       network_input_wf st0 content_type fragment raw_received /\
       wire_parse_failure content_type fragment /\
       raw_record_parse_success raw_received))

noextract
let network_unexpected_message_rejected_input_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  buffer_resp.response.status == IllegalTransition ==>
    buffer_resp.consumed_len == 0sz \/
    (exists msg.
      received_tls_raw_delta_legal
        st0
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len) /\
      decoded_message_event_projection
        st0
        st1
        buffer_resp.response
        msg
        (network_consumed_prefix network_input buffer_resp.consumed_len)
        network_out
        app_out)

noextract
let network_rejected_input_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  network_decode_error_rejected_input_witness
    st0
    st1
    buffer_resp
    network_input
    network_out
    app_out /\
  network_unexpected_message_rejected_input_witness
    st0
    st1
    buffer_resp
    network_input
    network_out
    app_out

noextract
let driver_step_rejected_input_witness (step:driver_step) : prop =
  match step with
  | DriverNetworkStep n ->
    network_rejected_input_witness
      n.network_driver_st0
      n.network_driver_st1
      n.network_driver_buffer_resp
      n.network_driver_input
      n.network_driver_network_out
      n.network_driver_app_out
  | DriverLocalStep _ ->
    True

noextract
let driver_step_legal_wire_delta
  (step:driver_step)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : prop =
  match step with
  | DriverNetworkStep n ->
    exists ev.
      legal_response_for_event
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp.response
        ev
        raw_sent
        raw_received
        n.network_driver_network_out
        n.network_driver_app_out
  | DriverLocalStep l ->
    exists ev.
      legal_response_for_event
        l.local_driver_st0
        l.local_driver_st1
        l.local_driver_resp
        ev
        raw_sent
        raw_received
        l.local_driver_network_out
        l.local_driver_app_out

noextract
let driver_step_accepted_wire_delta
  (step:driver_step)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : prop =
  driver_step_legal_wire_delta step raw_sent raw_received \/
  (driver_step_st1 step == driver_step_st0 step /\
   Seq.equal raw_sent B.empty /\
   Seq.equal raw_received B.empty)

noextract
let rec driver_trace_accepted_wire_delta
  (steps:list driver_step)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Tot prop
        (decreases steps)
=
  match steps with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty
  | step :: rest ->
    exists step_sent step_received rest_sent rest_received.
      driver_step_accepted_wire_delta step step_sent step_received /\
      driver_trace_accepted_wire_delta rest rest_sent rest_received /\
      Seq.equal raw_sent (B.append step_sent rest_sent) /\
      Seq.equal raw_received (B.append step_received rest_received)

noextract
let driver_trace_accepted_wire_log_delta
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : prop =
  exists raw_sent raw_received.
    driver_trace_accepted_wire_delta steps raw_sent raw_received /\
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent) /\
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received raw_received)

noextract
let rec driver_trace_chained
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Tot prop
        (decreases steps)
=
  match steps with
  | [] ->
    st1 == st0
  | step :: rest ->
    driver_step_st0 step == st0 /\
    driver_step_correct step /\
    driver_trace_chained (driver_step_st1 step) st1 rest

noextract
let rec driver_trace_rejected_input_witnesses
  (steps:list driver_step)
  : Tot prop
        (decreases steps)
=
  match steps with
  | [] -> True
  | step :: rest ->
    driver_step_rejected_input_witness step /\
    driver_trace_rejected_input_witnesses rest

noextract
let driver_trace_end_to_end
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : prop =
  driver_trace_chained st0 st1 steps /\
  (client_end_to_end_invariant st0 ==> client_end_to_end_invariant st1) /\
  driver_trace_accepted_wire_log_delta st0 st1 steps /\
  driver_trace_rejected_input_witnesses steps

#push-options "--split_queries always --z3refresh"
let lemma_network_bytes_end_to_end_correct_rejected_input_witness
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
      (ensures
        network_rejected_input_witness
          st0 st1 buffer_resp network_input network_out app_out)
=
  if buffer_resp.response.status = DecodeError then (
    assert (network_bytes_decode_error_projection
      st0 st1 buffer_resp network_input network_out app_out);
    assert (network_decode_error_rejected_input_witness
      st0 st1 buffer_resp network_input network_out app_out)
  );
  if buffer_resp.response.status = IllegalTransition then (
    assert (network_bytes_consumed_input_event_projection
      st0 st1 buffer_resp network_input network_out app_out);
    if buffer_resp.consumed_len = 0sz then ()
    else (
      assert (buffer_resp.response.status == DecodeError ==> False);
      assert (exists msg.
        received_tls_raw_delta_legal
          st0
          msg
          (network_consumed_prefix network_input buffer_resp.consumed_len) /\
        decoded_message_event_projection
          st0
          st1
          buffer_resp.response
          msg
          (network_consumed_prefix network_input buffer_resp.consumed_len)
          network_out
          app_out)
    );
    assert (network_unexpected_message_rejected_input_witness
      st0 st1 buffer_resp network_input network_out app_out)
  )
#pop-options

let lemma_driver_step_correct_rejected_input_witness
  (step:driver_step)
  : Lemma
      (requires driver_step_correct step)
      (ensures driver_step_rejected_input_witness step)
=
  match step with
  | DriverNetworkStep n ->
    lemma_network_bytes_end_to_end_correct_rejected_input_witness
      n.network_driver_st0
      n.network_driver_st1
      n.network_driver_buffer_resp
      n.network_driver_input
      n.network_driver_old_network_out
      n.network_driver_network_out
      n.network_driver_old_app_out
      n.network_driver_app_out
  | DriverLocalStep _ ->
    ()

let lemma_driver_step_correct_client_end_to_end_invariant
  (step:driver_step)
  : Lemma
      (requires driver_step_correct step /\ client_end_to_end_invariant (driver_step_st0 step))
      (ensures client_end_to_end_invariant (driver_step_st1 step))
=
  match step with
  | DriverNetworkStep n ->
    lemma_network_bytes_end_to_end_correct_client_end_to_end_invariant
      n.network_driver_st0
      n.network_driver_st1
      n.network_driver_buffer_resp
      n.network_driver_input
      n.network_driver_old_network_out
      n.network_driver_network_out
      n.network_driver_old_app_out
      n.network_driver_app_out
  | DriverLocalStep l ->
    lemma_local_event_end_to_end_correct_client_end_to_end_invariant
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      l.local_driver_kind
      l.local_driver_payload
      l.local_driver_network_out
      l.local_driver_app_out

noextract
let driver_step_some_legal_response (step:driver_step) : prop =
  match step with
  | DriverNetworkStep n ->
    some_legal_response
      n.network_driver_st0
      n.network_driver_st1
      n.network_driver_buffer_resp.response
      n.network_driver_network_out
      n.network_driver_app_out
  | DriverLocalStep l ->
    some_legal_response
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      l.local_driver_network_out
      l.local_driver_app_out

let lemma_some_legal_response_driver_step_legal_wire_delta
  (step:driver_step)
  : Lemma
      (requires driver_step_some_legal_response step)
      (ensures exists raw_sent raw_received.
        driver_step_legal_wire_delta step raw_sent raw_received)
=
  match step with
  | DriverNetworkStep n ->
    assert (exists ev raw_sent raw_received.
      legal_response_for_event
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp.response
        ev
        raw_sent
        raw_received
        n.network_driver_network_out
        n.network_driver_app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event
            n.network_driver_st0
            n.network_driver_st1
            n.network_driver_buffer_resp.response
            ev
            raw_sent
            raw_received
            n.network_driver_network_out
            n.network_driver_app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event
            n.network_driver_st0
            n.network_driver_st1
            n.network_driver_buffer_resp.response
            ev
            raw_sent
            raw_received
            n.network_driver_network_out
            n.network_driver_app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event
            n.network_driver_st0
            n.network_driver_st1
            n.network_driver_buffer_resp.response
            ev
            raw_sent
            raw_received
            n.network_driver_network_out
            n.network_driver_app_out) in
    assert (driver_step_legal_wire_delta step raw_sent raw_received)
  | DriverLocalStep l ->
    assert (exists ev raw_sent raw_received.
      legal_response_for_event
        l.local_driver_st0
        l.local_driver_st1
        l.local_driver_resp
        ev
        raw_sent
        raw_received
        l.local_driver_network_out
        l.local_driver_app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          legal_response_for_event
            l.local_driver_st0
            l.local_driver_st1
            l.local_driver_resp
            ev
            raw_sent
            raw_received
            l.local_driver_network_out
            l.local_driver_app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          legal_response_for_event
            l.local_driver_st0
            l.local_driver_st1
            l.local_driver_resp
            ev
            raw_sent
            raw_received
            l.local_driver_network_out
            l.local_driver_app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          legal_response_for_event
            l.local_driver_st0
            l.local_driver_st1
            l.local_driver_resp
            ev
            raw_sent
            raw_received
            l.local_driver_network_out
            l.local_driver_app_out) in
    assert (driver_step_legal_wire_delta step raw_sent raw_received)

let lemma_driver_step_correct_accepted_wire_delta
  (step:driver_step)
  : Lemma
      (requires driver_step_correct step)
      (ensures exists raw_sent raw_received.
        driver_step_accepted_wire_delta step raw_sent raw_received /\
        Seq.equal
          (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
          (B.append (driver_step_st0 step).CS.cs_wire_log.CL.raw_sent raw_sent) /\
        Seq.equal
          (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
          (B.append (driver_step_st0 step).CS.cs_wire_log.CL.raw_received raw_received))
=
  match step with
  | DriverNetworkStep n ->
    if response_stuttered
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp.response
        n.network_driver_old_network_out
        n.network_driver_network_out
        n.network_driver_old_app_out
        n.network_driver_app_out
    then (
      assert (n.network_driver_st1 == n.network_driver_st0);
      CL.lemma_append_empty_right n.network_driver_st0.CS.cs_wire_log.CL.raw_sent;
      CL.lemma_append_empty_right n.network_driver_st0.CS.cs_wire_log.CL.raw_received;
      assert (driver_step_accepted_wire_delta step B.empty B.empty)
    )
    else (
      assert (network_bytes_step_correct
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp
        n.network_driver_input
        n.network_driver_old_network_out
        n.network_driver_network_out
        n.network_driver_old_app_out
        n.network_driver_app_out);
      assert (some_legal_response
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp.response
        n.network_driver_network_out
        n.network_driver_app_out);
      lemma_some_legal_response_driver_step_legal_wire_delta step;
      assert (exists raw_sent raw_received.
        driver_step_legal_wire_delta step raw_sent raw_received);
      let raw_sent =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_sent -> exists raw_received.
            driver_step_legal_wire_delta step raw_sent raw_received) in
      let raw_received =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_received ->
            driver_step_legal_wire_delta step raw_sent raw_received) in
      assert (exists ev.
        legal_response_for_event
          n.network_driver_st0
          n.network_driver_st1
          n.network_driver_buffer_resp.response
          ev
          raw_sent
          raw_received
          n.network_driver_network_out
          n.network_driver_app_out);
      let ev =
        ID.indefinite_description_ghost
          CS.conn_event
          (fun ev ->
            legal_response_for_event
              n.network_driver_st0
              n.network_driver_st1
              n.network_driver_buffer_resp.response
              ev
              raw_sent
              raw_received
              n.network_driver_network_out
              n.network_driver_app_out) in
      assert (legal_response_for_event
        n.network_driver_st0
        n.network_driver_st1
        n.network_driver_buffer_resp.response
        ev
        raw_sent
        raw_received
        n.network_driver_network_out
        n.network_driver_app_out);
      assert (legal_delta
        n.network_driver_st0
        n.network_driver_st1
        ev
        raw_sent
        raw_received);
      assert (driver_step_accepted_wire_delta step raw_sent raw_received)
    )
  | DriverLocalStep l ->
    assert (local_event_step_correct
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      l.local_driver_kind
      l.local_driver_payload
      l.local_driver_network_out
      l.local_driver_app_out);
    assert (some_legal_response
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      l.local_driver_network_out
      l.local_driver_app_out);
    lemma_some_legal_response_driver_step_legal_wire_delta step;
    assert (exists raw_sent raw_received.
      driver_step_legal_wire_delta step raw_sent raw_received);
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          driver_step_legal_wire_delta step raw_sent raw_received) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          driver_step_legal_wire_delta step raw_sent raw_received) in
    assert (exists ev.
      legal_response_for_event
        l.local_driver_st0
        l.local_driver_st1
        l.local_driver_resp
        ev
        raw_sent
        raw_received
        l.local_driver_network_out
        l.local_driver_app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev ->
          legal_response_for_event
            l.local_driver_st0
            l.local_driver_st1
            l.local_driver_resp
            ev
            raw_sent
            raw_received
            l.local_driver_network_out
            l.local_driver_app_out) in
    assert (legal_response_for_event
      l.local_driver_st0
      l.local_driver_st1
      l.local_driver_resp
      ev
      raw_sent
      raw_received
      l.local_driver_network_out
      l.local_driver_app_out);
    assert (legal_delta
      l.local_driver_st0
      l.local_driver_st1
      ev
      raw_sent
      raw_received);
    assert (driver_step_accepted_wire_delta step raw_sent raw_received)

let rec lemma_driver_trace_rejected_input_witnesses
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Lemma
      (requires driver_trace_chained st0 st1 steps)
      (ensures driver_trace_rejected_input_witnesses steps)
      (decreases steps)
=
  match steps with
  | [] -> ()
  | step :: rest ->
    assert (driver_step_correct step);
    lemma_driver_step_correct_rejected_input_witness step;
    lemma_driver_trace_rejected_input_witnesses (driver_step_st1 step) st1 rest

let rec lemma_driver_trace_preserves_client_end_to_end_invariant
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Lemma
      (requires
        driver_trace_chained st0 st1 steps /\
        client_end_to_end_invariant st0)
      (ensures client_end_to_end_invariant st1)
      (decreases steps)
=
  match steps with
  | [] ->
    assert (st1 == st0)
  | step :: rest ->
    assert (driver_step_st0 step == st0);
    assert (driver_step_correct step);
    lemma_driver_step_correct_client_end_to_end_invariant step;
    lemma_driver_trace_preserves_client_end_to_end_invariant
      (driver_step_st1 step)
      st1
      rest

let rec lemma_driver_trace_accepted_wire_log_delta
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Lemma
      (requires driver_trace_chained st0 st1 steps)
      (ensures driver_trace_accepted_wire_log_delta st0 st1 steps)
      (decreases steps)
=
  match steps with
  | [] ->
    assert (st1 == st0);
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_sent;
    CL.lemma_append_empty_right st0.CS.cs_wire_log.CL.raw_received;
    assert (driver_trace_accepted_wire_delta [] B.empty B.empty)
  | step :: rest ->
    assert (driver_step_st0 step == st0);
    assert (driver_step_correct step);
    lemma_driver_step_correct_accepted_wire_delta step;
    assert (exists step_sent step_received.
      driver_step_accepted_wire_delta step step_sent step_received /\
      Seq.equal
        (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
        (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent) /\
      Seq.equal
        (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
        (B.append st0.CS.cs_wire_log.CL.raw_received step_received));
    let step_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun step_sent -> exists step_received.
          driver_step_accepted_wire_delta step step_sent step_received /\
          Seq.equal
            (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
            (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent) /\
          Seq.equal
            (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
            (B.append st0.CS.cs_wire_log.CL.raw_received step_received)) in
    let step_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun step_received ->
          driver_step_accepted_wire_delta step step_sent step_received /\
          Seq.equal
            (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
            (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent) /\
          Seq.equal
            (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
            (B.append st0.CS.cs_wire_log.CL.raw_received step_received)) in
    assert (driver_step_accepted_wire_delta step step_sent step_received);
    assert (Seq.equal
      (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent));
    assert (Seq.equal
      (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received step_received));
    lemma_driver_trace_accepted_wire_log_delta (driver_step_st1 step) st1 rest;
    assert (exists rest_sent rest_received.
      driver_trace_accepted_wire_delta rest rest_sent rest_received /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent rest_sent) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_received rest_received));
    let rest_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun rest_sent -> exists rest_received.
          driver_trace_accepted_wire_delta rest rest_sent rest_received /\
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_sent
            (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent rest_sent) /\
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_received rest_received)) in
    let rest_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun rest_received ->
          driver_trace_accepted_wire_delta rest rest_sent rest_received /\
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_sent
            (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent rest_sent) /\
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_received rest_received)) in
    assert (driver_trace_accepted_wire_delta rest rest_sent rest_received);
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent rest_sent));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append (driver_step_st1 step).CS.cs_wire_log.CL.raw_received rest_received));
    Seq.lemma_eq_elim
      (driver_step_st1 step).CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent);
    Seq.lemma_eq_elim
      (driver_step_st1 step).CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received step_received);
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_sent step_sent rest_sent;
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_received step_received rest_received;
    assert (Seq.equal
      (B.append step_sent rest_sent)
      (B.append step_sent rest_sent));
    assert (Seq.equal
      (B.append step_received rest_received)
      (B.append step_received rest_received));
    assert (exists step_sent' step_received' rest_sent' rest_received'.
      driver_step_accepted_wire_delta step step_sent' step_received' /\
      driver_trace_accepted_wire_delta rest rest_sent' rest_received' /\
      Seq.equal (B.append step_sent rest_sent) (B.append step_sent' rest_sent') /\
      Seq.equal
        (B.append step_received rest_received)
        (B.append step_received' rest_received'));
    assert (driver_trace_accepted_wire_delta
      (step :: rest)
      (B.append step_sent rest_sent)
      (B.append step_received rest_received));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent (B.append step_sent rest_sent)));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received (B.append step_received rest_received)))

let lemma_driver_trace_end_to_end
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Lemma
      (requires driver_trace_chained st0 st1 steps)
      (ensures driver_trace_end_to_end st0 st1 steps)
=
  if client_end_to_end_invariant st0 then
    lemma_driver_trace_preserves_client_end_to_end_invariant st0 st1 steps;
  lemma_driver_trace_accepted_wire_log_delta st0 st1 steps;
  lemma_driver_trace_rejected_input_witnesses st0 st1 steps

let lemma_driver_trace_from_initial_end_to_end
  (cfg:CS.connection_config)
  (st1:CS.connection_state)
  (steps:list driver_step)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        driver_trace_chained (CS.initial cfg) st1 steps)
      (ensures
        client_end_to_end_invariant st1 /\
        driver_trace_end_to_end (CS.initial cfg) st1 steps)
=
  lemma_initial_client_end_to_end_invariant cfg;
  lemma_driver_trace_end_to_end (CS.initial cfg) st1 steps;
  lemma_driver_trace_preserves_client_end_to_end_invariant
    (CS.initial cfg)
    st1
    steps
