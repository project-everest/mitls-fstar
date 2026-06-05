module TLS13.Impl.Client.Types

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module ID = FStar.IndefiniteDescription
module Seq = FStar.Seq
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

type client_status =
  | StepOk
  | NeedMoreInput
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed

type client_response = {
  network_out_len: SZ.t;
  app_out_len: SZ.t;
  status: client_status;
}

type client_buffer_response = {
  response: client_response;
  consumed_len: SZ.t;
}

let client_state_correct
  (st:CS.connection_state)
  : prop =
  CS.connection_state_consistent st /\
  CS.connection_state_full_log_consistent st

let lemma_initial_client_state_correct
  (cfg:CS.connection_config)
  : Lemma (client_state_correct (CS.initial cfg))
=
  CS.lemma_initial_full_log_consistent cfg;
  assert (CS.connection_state_evolves (CS.initial cfg) (CS.initial cfg))

let tls_decode_error : T.tls_error = T.AlertError T.DecodeError

let tls_unexpected_message_error : T.tls_error = T.AlertError T.UnexpectedMessage

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
         cert.M.chain ==
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
         cv.M.scheme
         peer.X.leaf_public_key
         verify_input
         cv.M.signature == true /\
       CS.legal_event
         st.CS.cs_model
         (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv))
     | _, _, _ -> False)
  | LocalVerifyFinished ->
    Seq.equal payload B.empty
  | _ -> True

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
  CS.lemma_legal_connection_delta_app_log_delta
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
  CS.lemma_legal_connection_delta_app_log_consistent
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
  CS.lemma_legal_connection_delta_event_log_consistent_with
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
  CS.lemma_legal_connection_delta_event_log_consistent
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
  CS.lemma_legal_connection_delta_transcript_consistent
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
  CS.lemma_legal_connection_delta_layered_log_consistent
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

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
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = raw_received;
  } in
  CS.lemma_legal_connection_delta_consistent st0 delta st1;
  CS.lemma_legal_connection_delta_full_log_consistent st0 delta st1

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
  CS.lemma_legal_connection_delta_protected_single_parse_record
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
  CS.lemma_legal_connection_delta_protected_parse_prefix
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
  CS.lemma_legal_connection_delta_protected_decompose_prefix
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
  CS.lemma_legal_connection_delta_protected_segmented
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
        client_state_correct st0)
      (ensures client_state_correct st1)
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
  lemma_legal_response_for_event_client_state_correct
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
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
    CS.lemma_model_record_keys_consistent_record_write_key_schedule_projection
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
    WS.parse_record raw_received ==
     Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
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
    WS.parse_record raw_received ==
       Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
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
    WS.parse_record raw_received ==
     Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
    (exists opened.
     protected_record_opened st0 raw_received outer_fragment opened /\
     (exists plaintext.
       WS.parse_plaintext opened == Some plaintext /\
       decoder_fragment_matches_plaintext content_type fragment plaintext)));
  let outer_fragment =
    ID.indefinite_description_ghost
       B.bytes
       (fun outer_fragment ->
         WS.parse_record raw_received ==
           Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
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
    WS.parse_record raw_received ==
       Some (T.ApplicationData, outer_fragment', B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment' opened' /\
    WS.parse_plaintext opened' == Some plaintext' /\
    WS.parse_tls_message plaintext'.M.content_type plaintext'.M.fragment == Some msg)

let protected_record_decode_uses_scheduled_read_key
  (st0:CS.connection_state)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened.
    WS.parse_record raw_received ==
     Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment opened /\
    CS.record_read_key_schedule_projection st0.CS.cs_model

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
    WS.parse_record raw_received ==
     Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
    (exists opened.
     protected_record_opened st0 raw_received outer_fragment opened /\
     (exists plaintext.
      WS.parse_plaintext opened == Some plaintext /\
      decoder_fragment_matches_plaintext content_type fragment plaintext)));
  let outer_fragment =
    ID.indefinite_description_ghost
     B.bytes
     (fun outer_fragment ->
       WS.parse_record raw_received ==
         Some (T.ApplicationData, outer_fragment, B.length raw_received) /\
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
  CS.lemma_model_record_keys_consistent_record_read_key_schedule_projection
    st0.CS.cs_model;
  assert (CS.record_read_key_schedule_projection st0.CS.cs_model);
  assert (exists outer_fragment' opened'.
    WS.parse_record raw_received ==
     Some (T.ApplicationData, outer_fragment', B.length raw_received) /\
    protected_record_opened st0 raw_received outer_fragment' opened' /\
    CS.record_read_key_schedule_projection st0.CS.cs_model)

let decoder_fragment_relation
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : prop =
  exists outer_ct outer_fragment.
    WS.parse_record raw_received ==
      Some (outer_ct, outer_fragment, B.length raw_received) /\
    (if outer_ct == T.ApplicationData
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
    CS.cleartext_tls_message_raw msg raw_received
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
    WS.parse_record raw_received ==
      Some (outer_ct, outer_fragment, B.length raw_received)

let lemma_raw_record_parse_success_raw_records
  (raw_received:B.bytes)
  : Lemma
      (requires raw_record_parse_success raw_received)
      (ensures exists outer_ct.
        CS.raw_records_exactly raw_received outer_ct 1 /\
        CS.raw_records_segmented raw_received outer_ct 1)
=
  match WS.parse_record raw_received with
  | None ->
    assert False
  | Some (outer_ct, outer_fragment, consumed) ->
    assert (consumed == B.length raw_received);
    CS.lemma_parse_record_full_raw_records_exactly
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
        CS.raw_records_exactly raw_received T.ApplicationData 1)
      (ensures protected_decoder_fragment_relation st0 content_type fragment raw_received)
=
  CS.lemma_raw_records_exactly_one_parse_record raw_received T.ApplicationData;
  assert (exists app_fragment.
    WS.parse_record raw_received ==
      Some (T.ApplicationData, app_fragment, B.length raw_received));
  let app_fragment =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_fragment ->
        WS.parse_record raw_received ==
          Some (T.ApplicationData, app_fragment, B.length raw_received)) in
  let outer_ct =
    ID.indefinite_description_ghost
      T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.ApplicationData
         then protected_decoder_fragment_relation st0 content_type fragment raw_received
         else
           L.content_type_matches content_type outer_ct /\
           Seq.equal fragment outer_fragment)) in
  let outer_fragment =
    ID.indefinite_description_ghost
      B.bytes
      (fun outer_fragment ->
        WS.parse_record raw_received ==
          Some (outer_ct, outer_fragment, B.length raw_received) /\
        (if outer_ct == T.ApplicationData
         then protected_decoder_fragment_relation st0 content_type fragment raw_received
         else
           L.content_type_matches content_type outer_ct /\
           Seq.equal fragment outer_fragment)) in
  assert (WS.parse_record raw_received ==
    Some (outer_ct, outer_fragment, B.length raw_received));
  assert (WS.parse_record raw_received ==
    Some (T.ApplicationData, app_fragment, B.length raw_received));
  assert (outer_ct == T.ApplicationData);
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
   then CS.cleartext_tls_message_raw msg raw_received
   else
     CS.raw_records_exactly
       raw_received
       T.ApplicationData
       (CS.protected_record_count CL.Received msg) /\
     CS.raw_records_segmented
       raw_received
       T.ApplicationData
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
    assert (CS.cleartext_tls_message_raw msg raw_received)
  else (
    assert (CS.raw_records_exactly
      raw_received
      T.ApplicationData
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
    CS.lemma_event_raw_delta_legal_protected_segmented
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
      T.ApplicationData
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
  | L.LTlsHandshake (L.LClientHello _), M.TlsHandshake (M.ClientHello _) ->
    True
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
    msg.CL.message_value == M.TlsAlert T.CloseNotify
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
  | LocalValidateCertificate, CS.ConnLocalEvent (CS.LocalValidateCertificate _) -> True
  | LocalVerifyCertificateSignature, CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature _) -> True
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
  local_event_kind_matches kind payload ev /\
  local_payload_matches_app_sent_delta kind payload ev /\
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
   (resp.status == DecodeError \/
    raw_record_parse_success
     (network_consumed_prefix network_input buffer_resp.consumed_len)) /\
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
  buffer_resp.response.status == DecodeError \/
  (exists outer_ct.
    CS.raw_records_exactly
     (network_consumed_prefix network_input buffer_resp.consumed_len)
     outer_ct
     1 /\
    CS.raw_records_segmented
     (network_consumed_prefix network_input buffer_resp.consumed_len)
     outer_ct
     1)

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
       protected_record_decode_uses_scheduled_read_key
         st0
         (network_consumed_prefix network_input buffer_resp.consumed_len)))

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
  response_network_out_raw_projection st0 st1 buffer_resp.response network_out app_out /\
  (client_state_correct st0 ==> client_state_correct st1) /\
  (client_state_correct st0 ==>
    network_bytes_protected_record_key_schedule_projection st0 buffer_resp network_input) /\
  (client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection
      st0 st1 buffer_resp.response network_out app_out) /\
  (client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1) /\
  (client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1)

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
  response_network_out_raw_projection st0 st1 resp network_out app_out /\
  response_network_out_seal_projection st0 st1 resp network_out app_out /\
  (client_state_correct st0 ==> client_state_correct st1) /\
  (client_state_correct st0 ==>
    response_network_out_write_key_schedule_projection st0 st1 resp network_out app_out) /\
  (client_state_correct st0 ==> CS.connection_state_connection_log_view_consistent st1) /\
  (client_state_correct st0 ==> CS.connection_state_raw_event_replay_consistent st1)

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
  else if resp.status == DecodeError then ()
  else (
    assert (raw_record_parse_success
      (network_consumed_prefix network_input buffer_resp.consumed_len));
    lemma_raw_record_parse_success_raw_records
      (network_consumed_prefix network_input buffer_resp.consumed_len)
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
      lemma_protected_decoder_fragment_relation_read_key_schedule_projection
        st0
        content_type
        fragment
        raw_received;
      assert (protected_record_decode_uses_scheduled_read_key st0 raw_received)
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
       else protected_record_decode_uses_scheduled_read_key st0 raw_received))
  )

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
        client_state_correct st0)
      (ensures client_state_correct st1)
=
  let resp = buffer_resp.response in
  if response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out
  then assert (st1 == st0)
  else lemma_some_legal_response_client_state_correct st0 st1 resp network_out app_out

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
  lemma_network_bytes_step_correct_network_out_raw_projection
    st0
    st1
    buffer_resp
    network_input
    old_network_out
    network_out
    old_app_out
    app_out;
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
    lemma_network_bytes_step_correct_client_state_correct
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out
  )

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
  lemma_some_legal_response_client_state_correct st0 st1 resp network_out app_out

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
        local_event_step_correct st0 st1 resp kind payload network_out app_out)
      (ensures
        local_event_end_to_end_correct st0 st1 resp kind payload network_out app_out)
=
  lemma_some_legal_response_network_out_raw_projection st0 st1 resp network_out app_out;
  lemma_local_event_step_correct_network_out_seal_projection
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out;
  if client_state_correct st0 then (
    lemma_some_legal_response_network_out_write_key_schedule_projection
      st0
      st1
      resp
      network_out
      app_out;
    lemma_local_event_step_correct_client_state_correct
      st0
      st1
      resp
      kind
      payload
      network_out
      app_out
  )

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
