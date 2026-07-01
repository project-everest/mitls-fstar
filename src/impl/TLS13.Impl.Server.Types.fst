module TLS13.Impl.Server.Types

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module H = TLS13.Handshake.Spec
module Tr = TLS13.Transcript
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module R = TLS13.Record.Spec
module SM = TLS13.StateMachine
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U64 = FStar.UInt64
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
  | LocalPayloadServerPrivateKey
  | LocalPayloadServerRandomAndPrivateKey
  | LocalPayloadCertificateVerifySignature
  | LocalPayloadApplicationData

type next_local_action = {
  next_local_ready: bool;
  next_local_kind: local_event_kind;
  next_local_payload: local_payload_kind;
}

noextract
let next_local_action_sound
  (st:CS.connection_state)
  (action:next_local_action)
  : prop =
  if action.next_local_ready then
    match action.next_local_kind with
    | LocalStartServer ->
      action.next_local_payload == LocalPayloadNone /\
      CM.can_start_server st
    | LocalSelectServerParameters ->
      action.next_local_payload == LocalPayloadServerRandomAndPrivateKey /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      CR.server_selection_absent st.CS.cs_model.CS.model_handshake /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
      Some? st.CS.cs_model.CS.model_config.CS.config_server
    | LocalDeriveSharedSecret ->
      action.next_local_payload == LocalPayloadServerPrivateKey /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
      (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
       | Some selection ->
         CS.server_selection_key_share_consistent selection /\
         st.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
           Some selection.CS.server_selected_client_hello /\
         Some? selection.CS.server_key_share_private
       | None -> False)
    | LocalSendServerHello ->
      action.next_local_payload == LocalPayloadServerRandomAndPrivateKey /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
      st.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
      (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
       | Some selection ->
         CS.server_selection_key_share_consistent selection /\
         Some? selection.CS.server_key_share_private
       | None -> False)
    | LocalInstallServerHandshakeTrafficKeys ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
    | LocalInstallClientHandshakeTrafficKeys ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
    | LocalInstallServerApplicationTrafficKeys ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | LocalInstallClientApplicationTrafficKeys ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientFinishedReceived /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
    | LocalSendEncryptedExtensions ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      U64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
        Bounds.max_transcript_len /\
      CS.legal_event
        st.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value =
            M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
        })
    | LocalSendCertificate ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      st.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      U64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      (match st.CS.cs_model.CS.model_config.CS.config_server with
       | Some cfg ->
         B.length cfg.CS.server_certificate_chain <=
           Bounds.max_server_certificate_chain_len /\
         // Transcript-length bound for the Certificate flight: the handshake
         // message serializes to exactly 13 + |chain| bytes
         // (TLS13.Impl.Server.Send.lemma_mk_cert_witness_bytesize).  The
         // legal_event (M.Certificate cert) obligation stays a caller obligation
         // discharged with the build-direction witness at the send site.
         B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 13 +
           B.length cfg.CS.server_certificate_chain <= Bounds.max_transcript_len
       | None -> False)
    | LocalSignCertificateVerify ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None
    | LocalSendCertificateVerify ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      U64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      (let cv = Some?.v
         st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
       // Transcript-length bound for the CertificateVerify flight: the handshake
       // message serializes to exactly 8 + |signature| bytes
       // (TLS13.Impl.Server.Send.lemma_serialize_handshake_certificate_verify_len).
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 8 +
         B.length (Sem.certificateVerify_signature_bytes cv) <= Bounds.max_transcript_len /\
       CS.legal_event
         st.CS.cs_model
         (CS.ConnNetworkEvent {
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
         }))
    | LocalSendServerFinished ->
      action.next_local_payload == LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      U64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
        Bounds.max_transcript_len
    | LocalVerifyClientFinished ->
      action.next_local_payload == LocalPayloadNone /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
      // TODO-A1: CM.can_verify_client_finished bundles a transcript-length conjunct
      // `B.length transcript + B.length (WS.serialize_handshake (M.Finished fin)) <=
      // max_transcript_len` whose proof needed the Phase-4-deleted
      // WS.lemma_serialize_finished_len (which gave serialize_handshake (M.Finished fin)
      // == 36).  WS.serialize_handshake is abstract (val) and no surviving lemma exposes
      // its finished length, so that bound is not provable in any in-scope module; we
      // restate the remaining (provable) conjuncts of can_verify_client_finished here,
      // matching CQ.can_verify_client_finished_runtime's exposed postcondition.
      (let fin = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
       st.CS.cs_model.CS.model_control ==
         CS.ControlHandshaking CS.HsClientFinishedReceived /\
       st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model /\
       (match st.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
              st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
        | Some stored_fin, Some client_hs ->
          stored_fin == fin /\
          H.verify_finished
            client_hs.CS.traffic_secret
            (Tr.hash st.CS.cs_model.CS.model_handshake.CS.hs_transcript)
            fin
        | _, _ -> False) /\
       CS.legal_event
         st.CS.cs_model
         (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) /\
       // Transcript-length bound of CM.can_verify_client_finished: a Finished
       // handshake message serializes to exactly 36 bytes
       // (TLS13.Impl.Server.Send.lemma_serialize_handshake_finished_len).
       B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
         Bounds.max_transcript_len)
    | _ ->
      False
  else
    True

noextract
let server_local_event_input_ready
  (st:CS.connection_state)
  (kind:local_event_kind)
  (payload:B.bytes)
  : prop =
  match kind with
  | LocalStartServer ->
    Seq.equal payload B.empty /\
    CM.can_start_server st
  | LocalInstallServerHandshakeTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
  | LocalInstallClientHandshakeTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
  | LocalInstallServerApplicationTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
  | LocalInstallClientApplicationTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientFinishedReceived /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
  | LocalVerifyClientFinished ->
    Seq.equal payload B.empty /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
    // TODO-A1: see next_local_action_sound/LocalVerifyClientFinished above.  The
    // transcript/serialized-finished length bound of CM.can_verify_client_finished is not
    // provable in-scope (deleted WS.lemma_serialize_finished_len; WS.serialize_handshake
    // abstract).  We restate the provable conjuncts, matching
    // CQ.can_verify_client_finished_runtime's exposed postcondition.
    (let fin = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
     st.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsClientFinishedReceived /\
     st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model /\
     (match st.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
            st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
      | Some stored_fin, Some client_hs ->
        stored_fin == fin /\
        H.verify_finished
          client_hs.CS.traffic_secret
          (Tr.hash st.CS.cs_model.CS.model_handshake.CS.hs_transcript)
          fin
      | _, _ -> False) /\
     CS.legal_event
       st.CS.cs_model
       (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)))
  | LocalSelectServerParameters ->
    B.length payload == 64 /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived /\
    CR.server_selection_absent st.CS.cs_model.CS.model_handshake /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
    Some? st.CS.cs_model.CS.model_config.CS.config_server /\
    (let ch = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
     let cfg = Some?.v st.CS.cs_model.CS.model_config.CS.config_server in
     let server_random = CL.raw_slice payload 0 32 in
     let server_private_key = CL.raw_slice payload 32 64 in
     let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
       CS.server_selected_group = T.X25519;
       CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
       CS.server_random = server_random;
       CS.server_key_share_private = Some server_private_key;
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private server_private_key;
       CS.server_selected_credential = cfg.CS.server_credential_identity;
     } in
     CM.can_select_server_parameters st selection)
  | LocalSendServerHello ->
    B.length payload == 64 /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    (let server_random = CL.raw_slice payload 0 32 in
     let server_private_key = CL.raw_slice payload 32 64 in
     (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        Seq.equal selection.CS.server_random server_random /\
        Some? selection.CS.server_key_share_private /\
        Seq.equal
          (Some?.v selection.CS.server_key_share_private)
          server_private_key /\
        CS.server_selection_key_share_consistent selection
      | None -> False) /\
     // TODO-A1: build-direction can_send_server_hello needs a GSH.serverHello witness
     // (Model has no server_hello_of_selection builder yet; the deleted Reveal layer
     // provided it).  Weakened to True until build-direction support lands.
     True)
  | LocalSendEncryptedExtensions ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    U64.fits
      (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
    B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
      Bounds.max_transcript_len /\
    CS.legal_event
      st.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value =
          M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
      })
  | LocalSendServerFinished ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    U64.fits
      (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
    B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
      Bounds.max_transcript_len
  | LocalSendCertificateVerify ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    U64.fits
      (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
    (let cv = Some?.v
       st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
     // TODO-A1: Phase 4 deleted WS.serialize_certificate_verify_from_signature and the
     // M.certificate_verify `body` projection; the transcript-length bound is weakened to
     // True (recoverable from the serializer postcondition once build-direction lands).
     True /\
     CS.legal_event
       st.CS.cs_model
       (CS.ConnNetworkEvent {
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
       }))
  | LocalDeriveSharedSecret ->
    B.length payload == 32 /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
    (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
     | Some selection ->
       CS.server_selection_key_share_consistent selection /\
       st.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
         Some selection.CS.server_selected_client_hello /\
       Some? selection.CS.server_key_share_private /\
       Some?.v selection.CS.server_key_share_private == payload
     | None -> False)
  | LocalSendApplicationData ->
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
    B.length payload <= SM.max_application_data_fragment_len
  | LocalSendCloseNotify ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic
  | _ ->
    False

noextract
let server_local_event_input_ready_with_credentials
  (st:CS.connection_state)
  (kind:local_event_kind)
  (payload:B.bytes)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : prop =
  match kind with
  | LocalSendCertificate ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
    st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
    U64.fits
      (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
    13 + B.length certificate_chain + 17 <= 16640 /\
    (match st.CS.cs_model.CS.model_config.CS.config_server with
     | Some cfg -> cfg.CS.server_certificate_chain == certificate_chain
     | None -> False) /\
    B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      13 + B.length certificate_chain <= Bounds.max_transcript_len /\
    // TODO-A1: build-direction legal_event (M.Certificate cert) needs a GCert.certificate
    // witness with `Sem.certificate_entries cert == [certificate_chain]`; weakened to True.
    True
  | LocalSignCertificateVerify ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
    st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
    st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
    (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
     | Some selection ->
       selection.CS.server_selected_signature_scheme ==
         T.Rsa_pss_rsae_sha256 /\
       selection.CS.server_selected_credential == credential_identity /\
       CS.signature_scheme_offered
         st.CS.cs_model.CS.model_config.CS.config_signature_schemes
         T.Rsa_pss_rsae_sha256
     | None -> False)
  | _ ->
    server_local_event_input_ready st kind payload

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

noextract
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
    msg.CL.message_value == M.TlsAlert T.Close_notify
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

noextract
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

noextract
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

noextract
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

noextract
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
    (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
    B.empty
    B.empty
    network_out
    app_out

noextract
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

let lemma_unexpected_message_response_control_failed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires unexpected_message_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlFailed CM.tls_unexpected_message_error)
=
  CSL.lemma_legal_connection_delta_local_fail_control_failed
    st0
    st1
    CM.tls_unexpected_message_error
    B.empty
    B.empty

let lemma_decode_error_response_control_failed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires decode_error_response st0 st1 resp network_out app_out)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlFailed CM.tls_decode_error)
=
  CSL.lemma_legal_connection_delta_local_fail_control_failed
    st0
    st1
    CM.tls_decode_error
    B.empty
    B.empty

noextract
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

noextract
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

noextract
let received_message_event (msg:M.tls_message) : CS.conn_event =
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = msg;
  }

noextract
let received_message_delta
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : CS.connection_delta =
  {
    CS.delta_event = received_message_event msg;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  }

noextract
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
  (resp.status == IllegalTransition ==> False) /\
  (resp.status == OutputBufferTooSmall ==> False) /\
  (match msg with
   | M.TlsAlert T.Close_notify ->
     resp.status == StepOk
   | M.TlsAlert _ ->
     resp.status == ConnectionFailed
   | _ ->
     resp.status == StepOk) /\
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
    WS.parse_record_wire raw_received ==
      Some (T.Application_data, outer_fragment, B.length raw_received) /\
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

let server_network_connection_failed_consumed_prefix
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.response.status == ConnectionFailed ==>
    exists alert raw_received.
      st1 ==
        CM.received_alert_failure_state
         st0
         alert
         raw_received /\
      Seq.equal
        raw_received
        (server_network_consumed_prefix resp input) /\
      legal_network_response
        st0
        st1
        resp.response
        (M.TlsAlert alert)
        raw_received
        network_out
        app_out

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
  server_network_connection_failed_consumed_prefix
    st0 st1 resp input network_out app_out /\
  (resp.response.status == NeedMoreInput ==>
    st1 == st0 /\
    resp.consumed_len == 0sz /\
    resp.response.network_out_len == 0sz) /\
  (resp.response.status == IllegalTransition ==>
    st1 == st0 /\
    resp.consumed_len == 0sz /\
    resp.response.network_out_len == 0sz) /\
  (resp.response.status == DecodeError ==>
    decode_error_response st0 st1 resp.response network_out app_out) /\
  (resp.response.status == OutputBufferTooSmall ==> False)

let server_connection_control_not_failed
  (st:CS.connection_state)
  : prop =
  match st.CS.cs_model.CS.model_control with
  | CS.ControlFailed _ -> False
  | _ -> True

let lemma_server_connection_control_not_failed_contradicts_failed
  (st:CS.connection_state)
  (err:T.tls_error)
  : Lemma
      (requires
        server_connection_control_not_failed st /\
        st.CS.cs_model.CS.model_control == CS.ControlFailed err)
      (ensures False)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlFailed _ -> assert False
  | _ -> assert False

let lemma_legal_response_for_event_nonfailed_previous
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
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
        server_connection_control_not_failed st1)
      (ensures server_connection_control_not_failed st0)
=
  if server_connection_control_not_failed st0 then ()
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

let server_network_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  server_connection_control_not_failed st1 ==>
    (resp.consumed_len == 0sz \/
     exists msg.
       legal_network_response
         st0
         st1
         resp.response
         msg
         (server_network_consumed_prefix resp input)
         network_out
         app_out)

let lemma_server_network_consumed_input_projection_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out
          app_out)
      (ensures
        server_network_nonfailed_received_prefix_accepted
          st0
          st1
          resp
          input
          network_out
          app_out)
=
  if server_connection_control_not_failed st1 then (
    if resp.consumed_len == 0sz then ()
    else (
      match resp.response.status with
      | StepOk ->
        assert (server_network_step_ok_received_decode_projection
          st0
          st1
          resp
          input
          network_out
          app_out);
        assert (exists msg.
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
               msg));
        let msg =
          ID.indefinite_description_ghost
            M.tls_message
            (fun msg ->
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
                   msg)) in
        assert (server_decoded_message_event_projection
          st0
          st1
          resp.response
          msg
          (server_network_consumed_prefix resp input)
          network_out
          app_out);
        if legal_network_response
          st0
          st1
          resp.response
          msg
          (server_network_consumed_prefix resp input)
          network_out
          app_out
        then (
          assert (exists msg'.
            legal_network_response
              st0
              st1
              resp.response
              msg'
              (server_network_consumed_prefix resp input)
              network_out
              app_out)
        ) else (
          assert (unexpected_message_response
            st0
            st1
            resp.response
            network_out
            app_out);
          assert (resp.response.status == IllegalTransition);
          assert False
        )
      | ConnectionFailed ->
        assert (server_network_connection_failed_consumed_prefix
          st0
          st1
          resp
          input
          network_out
          app_out);
        assert (exists alert raw_received.
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (server_network_consumed_prefix resp input) /\
          legal_network_response
            st0
            st1
            resp.response
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out);
        let alert =
          ID.indefinite_description_ghost
            T.alert_description
            (fun alert -> exists raw_received.
              st1 ==
                CM.received_alert_failure_state
                  st0
                  alert
                  raw_received /\
              Seq.equal
                raw_received
                (server_network_consumed_prefix resp input) /\
              legal_network_response
                st0
                st1
                resp.response
                (M.TlsAlert alert)
                raw_received
                network_out
                app_out) in
        let raw_received =
          ID.indefinite_description_ghost
            B.bytes
            (fun raw_received ->
              st1 ==
                CM.received_alert_failure_state
                  st0
                  alert
                  raw_received /\
              Seq.equal
                raw_received
                (server_network_consumed_prefix resp input) /\
              legal_network_response
                st0
                st1
                resp.response
                (M.TlsAlert alert)
                raw_received
                network_out
                app_out) in
        assert (st1 ==
          CM.received_alert_failure_state
            st0
            alert
            raw_received);
        assert (st1.CS.cs_model.CS.model_control ==
          CS.ControlFailed (T.AlertError alert));
        lemma_server_connection_control_not_failed_contradicts_failed
          st1
          (T.AlertError alert)
      | DecodeError ->
        assert (decode_error_response st0 st1 resp.response network_out app_out);
        lemma_decode_error_response_control_failed
          st0
          st1
          resp.response
          network_out
          app_out;
        lemma_server_connection_control_not_failed_contradicts_failed
          st1
          CM.tls_decode_error
      | NeedMoreInput ->
        assert (resp.consumed_len == 0sz);
        assert False
      | IllegalTransition ->
        assert (resp.consumed_len == 0sz);
        assert False
      | OutputBufferTooSmall ->
        assert False
    )
  )

let lemma_server_network_bytes_end_to_end_nonfailed_received_prefix_accepted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        server_network_bytes_end_to_end_correct
          st0
          st1
          resp
          input
          network_out
          app_out /\
        server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out
          app_out)
      (ensures
        server_network_nonfailed_received_prefix_accepted
          st0
          st1
          resp
          input
          network_out
          app_out)
=
  lemma_server_network_consumed_input_projection_nonfailed_received_prefix_accepted
    st0
    st1
    resp
    input
    network_out
    app_out

let lemma_server_network_bytes_end_to_end_nonfailed_previous
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        server_network_bytes_end_to_end_correct
          st0
          st1
          resp
          input
          network_out
          app_out /\
        server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out
          app_out /\
        server_connection_control_not_failed st1)
      (ensures server_connection_control_not_failed st0)
=
  match resp.response.status with
  | NeedMoreInput ->
    assert (st1 == st0)
  | IllegalTransition ->
    assert (st1 == st0)
  | DecodeError ->
    assert (decode_error_response st0 st1 resp.response network_out app_out);
    lemma_decode_error_response_control_failed
      st0
      st1
      resp.response
      network_out
      app_out;
    lemma_server_connection_control_not_failed_contradicts_failed
      st1
      CM.tls_decode_error
  | OutputBufferTooSmall ->
    assert False
  | StepOk ->
    assert (server_network_step_ok_received_decode_projection
      st0
      st1
      resp
      input
      network_out
      app_out);
    assert (exists msg.
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
           msg));
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
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
               msg)) in
    assert (server_decoded_message_event_projection
      st0
      st1
      resp.response
      msg
      (server_network_consumed_prefix resp input)
      network_out
      app_out);
    if legal_network_response
      st0
      st1
      resp.response
      msg
      (server_network_consumed_prefix resp input)
      network_out
      app_out
    then (
      assert (legal_response_for_event
        st0
        st1
        resp.response
        (received_message_event msg)
        B.empty
        (server_network_consumed_prefix resp input)
        network_out
        app_out);
      lemma_legal_response_for_event_nonfailed_previous
        st0
        st1
        resp.response
        (received_message_event msg)
        B.empty
        (server_network_consumed_prefix resp input)
        network_out
        app_out
    ) else (
      assert (unexpected_message_response st0 st1 resp.response network_out app_out);
      assert (resp.response.status == IllegalTransition);
      assert False
    )
  | ConnectionFailed ->
    assert (server_network_connection_failed_consumed_prefix
      st0
      st1
      resp
      input
      network_out
      app_out);
    assert (exists alert raw_received.
      st1 ==
        CM.received_alert_failure_state
          st0
          alert
          raw_received /\
      Seq.equal
        raw_received
        (server_network_consumed_prefix resp input) /\
      legal_network_response
        st0
        st1
        resp.response
        (M.TlsAlert alert)
        raw_received
        network_out
        app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (server_network_consumed_prefix resp input) /\
          legal_network_response
            st0
            st1
            resp.response
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (server_network_consumed_prefix resp input) /\
          legal_network_response
            st0
            st1
            resp.response
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (st1 ==
      CM.received_alert_failure_state
        st0
        alert
        raw_received);
    assert (st1.CS.cs_model.CS.model_control ==
      CS.ControlFailed (T.AlertError alert));
    lemma_server_connection_control_not_failed_contradicts_failed
      st1
      (T.AlertError alert)

let lemma_legal_response_for_event_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
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
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
  CSL.lemma_step_model_preserves_config st0.CS.cs_model ev st1.CS.cs_model

let lemma_legal_network_response_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_network_response
          st0
          st1
          resp
          msg
          raw_received
          network_out
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  lemma_legal_response_for_event_preserves_config
    st0
    st1
    resp
    (received_message_event msg)
    B.empty
    raw_received
    network_out
    app_out

let lemma_legal_local_response_preserves_config
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
  : Lemma
      (requires
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
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  assert (legal_response_for_event
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out);
  lemma_legal_response_for_event_preserves_config
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out

let lemma_legal_handled_local_response_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        legal_handled_local_response
          st0
          st1
          resp
          kind
          payload
          network_out
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  let goal (_:unit) =
    st1.CS.cs_model.CS.model_config ==
      st0.CS.cs_model.CS.model_config in
  FStar.Classical.or_elim
    #(exists ev raw_sent raw_received.
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
         app_out)
    #(unexpected_message_response st0 st1 resp network_out app_out)
    #goal
    (fun h ->
      FStar.Classical.exists_elim (goal ())
        #CS.conn_event
        #(fun ev -> exists raw_sent raw_received.
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
            app_out)
        h
        (fun ev ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_sent -> exists raw_received.
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
            app_out)
        ()
        (fun raw_sent ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_received ->
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
            app_out)
        ()
        (fun raw_received ->
          lemma_legal_local_response_preserves_config
            st0
            st1
            resp
            kind
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out))))
    (fun _ ->
      lemma_legal_response_for_event_preserves_config
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
        B.empty
        B.empty
        network_out
        app_out)

let lemma_server_local_event_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  assert (legal_handled_local_response
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out);
  lemma_legal_handled_local_response_preserves_config
    st0
    st1
    resp
    kind
    payload
    network_out
    app_out

let lemma_server_network_bytes_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out
          app_out)
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  match resp.response.status with
  | NeedMoreInput ->
    assert (st1 == st0)
  | IllegalTransition ->
    assert (st1 == st0)
  | OutputBufferTooSmall ->
    assert False
  | DecodeError ->
    assert (decode_error_response
      st0
      st1
      resp.response
      network_out
      app_out);
    lemma_legal_response_for_event_preserves_config
      st0
      st1
      resp.response
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out
  | ConnectionFailed ->
    assert (server_network_connection_failed_consumed_prefix
      st0 st1 resp input network_out app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal
            raw_received
            (server_network_consumed_prefix resp input) /\
          legal_network_response
            st0
            st1
            resp.response
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal
            raw_received
            (server_network_consumed_prefix resp input) /\
          legal_network_response
            st0
            st1
            resp.response
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (legal_network_response
      st0
      st1
      resp.response
      (M.TlsAlert alert)
      raw_received
      network_out
      app_out);
    lemma_legal_network_response_preserves_config
      st0
      st1
      resp.response
      (M.TlsAlert alert)
      raw_received
      network_out
      app_out
  | StepOk ->
    assert (server_network_step_ok_received_decode_projection
      st0 st1 resp input network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
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
               msg)) in
    assert (server_decoded_message_event_projection
      st0
      st1
      resp.response
      msg
      (server_network_consumed_prefix resp input)
      network_out
      app_out);
    if legal_network_response
      st0
      st1
      resp.response
      msg
      (server_network_consumed_prefix resp input)
      network_out
      app_out
    then
      lemma_legal_network_response_preserves_config
        st0
        st1
        resp.response
        msg
        (server_network_consumed_prefix resp input)
        network_out
        app_out
    else (
      assert (unexpected_message_response
        st0
        st1
        resp.response
        network_out
        app_out);
      assert (resp.response.status == IllegalTransition);
      assert False
    )
