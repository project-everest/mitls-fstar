module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module SM = TLS13.StateMachine
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

noextract
let server_state_ref (s:server) : CR.state_ref =
  CR.connection_state_ref s

noextract
let next_local_action_sound
  (st:CS.connection_state)
  (action:ST.next_local_action)
  : prop =
  if action.ST.next_local_ready then
    match action.ST.next_local_kind with
    | ST.LocalStartServer ->
      action.ST.next_local_payload == ST.LocalPayloadNone /\
      CM.can_start_server st
    | ST.LocalInstallServerHandshakeTrafficKeys ->
      action.ST.next_local_payload == ST.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
    | ST.LocalInstallClientHandshakeTrafficKeys ->
      action.ST.next_local_payload == ST.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent /\
      st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
    | ST.LocalInstallServerApplicationTrafficKeys ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
     st.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsServerFinishedSent /\
     st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     Some?
       st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
     not (Some?
       st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | ST.LocalInstallClientApplicationTrafficKeys ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
     st.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsClientFinishedReceived /\
     st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     Some?
       st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
     not (Some?
       st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
    | ST.LocalSendEncryptedExtensions ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
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
           M.TlsHandshake (M.EncryptedExtensions { M.negotiated_alpn = None });
       })
    | ST.LocalSendCertificate ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
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
        B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
          B.length
            (TLS13.Wire.Spec.serialize_certificate_from_credential
              { M.chain = [cfg.CS.server_certificate_chain] }) <=
            Bounds.max_transcript_len /\
        CS.legal_event
          st.CS.cs_model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value =
              M.TlsHandshake
                (M.Certificate { M.chain = [cfg.CS.server_certificate_chain] });
          })
      | None -> False)
    | ST.LocalSignCertificateVerify ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
     st.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
     st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
     st.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
     st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
     st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None
    | ST.LocalSendCertificateVerify ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
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
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        B.length (TLS13.Wire.Spec.serialize_certificate_verify_from_signature cv) <=
          Bounds.max_transcript_len /\
      CS.legal_event
        st.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }))
    | ST.LocalSendServerFinished ->
     action.ST.next_local_payload == ST.LocalPayloadNone /\
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
    | _ ->
     False
  else
    True

noextract
let server_local_event_input_ready
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  : prop =
  match kind with
  | ST.LocalStartServer ->
    Seq.equal payload B.empty /\
    CM.can_start_server st
  | ST.LocalInstallServerHandshakeTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
  | ST.LocalInstallClientHandshakeTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
  | ST.LocalInstallServerApplicationTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedSent /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
  | ST.LocalInstallClientApplicationTrafficKeys ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientFinishedReceived /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
    not (Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
  | ST.LocalVerifyClientFinished ->
    Seq.equal payload B.empty /\
    Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
    CM.can_verify_client_finished
      st
      (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished)
  | ST.LocalSendEncryptedExtensions ->
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
          M.TlsHandshake (M.EncryptedExtensions { M.negotiated_alpn = None });
      })
  | ST.LocalSendServerFinished ->
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
  | ST.LocalSendCertificateVerify ->
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
     B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
       B.length (TLS13.Wire.Spec.serialize_certificate_verify_from_signature cv) <=
         Bounds.max_transcript_len /\
     CS.legal_event
       st.CS.cs_model
       (CS.ConnNetworkEvent {
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
       }))
  | ST.LocalDeriveSharedSecret ->
    B.length payload == 32 /\
    CS.legal_event
      st.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret payload))
  | ST.LocalSendApplicationData ->
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
    B.length payload <= SM.max_application_data_fragment_len
  | ST.LocalSendCloseNotify ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic
  | _ ->
    False

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (credential_identity:array U8.t)
  (credential_identity_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to credential_identity 'credential_identity_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'credential_identity_bytes == SZ.v credential_identity_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns s:server
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to credential_identity 'credential_identity_bytes **
          connection_exactly
            s
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal 'credential_identity_bytes)) **
          pure (ST.server_state_correct
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_end_to_end_invariant
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_raw_to_message_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_sent_seal_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_received_decode_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                CS.connection_state_protected_raw_segmented_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)))

fn next_local_action
  (s:server)
  requires connection_exactly s 'st0 **
           pure (ST.server_state_correct 'st0)
  returns action:ST.next_local_action
  ensures connection_exactly s 'st0 **
          pure (ST.server_state_correct 'st0 /\
                next_local_action_sound 'st0 action)

fn process_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_select_server_parameters
  (s:server)
  (#selection:erased CS.server_handshake_selection)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  ST.server_end_to_end_invariant 'st0 /\
                  CM.can_select_server_parameters 'st0 selection)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSelectServerParameters
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v raw_len <= SZ.v network_out_len /\
                 Seq.equal
                    (Seq.slice (Ghost.reveal 'old_network_out) 0 (SZ.v raw_len))
                    (Ghost.reveal 'raw_bytes) /\
                 Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh)) /\
                 SZ.v fragment_len <= Bounds.max_server_hello_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello 'st0 sh (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello_serialized
  (s:server)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_encrypted_extensions_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 28 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerHelloSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
                   Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake
                         (M.EncryptedExtensions { M.negotiated_alpn = None });
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendEncryptedExtensions
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_serialized
  (s:server)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_msg lcert cert **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_from_credential
                       (Ghost.reveal cert)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 (Ghost.reveal cert).M.chain <> [] /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_from_credentials
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 Some?
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                  ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640 /\
                 SZ.v network_out_len ==
                  13 + B.length (Ghost.reveal 'certificate_chain) + 22 /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> cfg.CS.server_certificate_chain == Ghost.reveal 'certificate_chain
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  13 + B.length (Ghost.reveal 'certificate_chain) <=
                    Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value =
                      M.TlsHandshake
                        (M.Certificate { M.chain = [Ghost.reveal 'certificate_chain] });
                  }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_verify_serialized
  (s:server)
  (lcv:IM.certificate_verify)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_verify lcv cv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                       (Ghost.reveal cv)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                  | Some stored_cv -> stored_cv == Ghost.reveal cv
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_stored_certificate_verify_serialized
  (s:server)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  SZ.v fragment_len ==
                    B.length
                      (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                        (Ghost.reveal cv)) /\
                  SZ.v fragment_len + 17 <= 16640 /\
                  SZ.v network_out_len == SZ.v fragment_len + 22 /\
                  ST.server_end_to_end_invariant 'st0 /\
                  'st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                  'st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                  Some?
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits
                    ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= Bounds.max_transcript_len /\
                  CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Sent;
                      CL.message_value =
                        M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendCertificateVerify
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_sign_certificate_verify
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    selection.CS.server_selected_signature_scheme ==
                      T.RsaPssRsaeSha256 /\
                    selection.CS.server_selected_credential ==
                      Ghost.reveal 'credential_identity /\
                    CS.signature_scheme_offered
                      'st0.CS.cs_model.CS.model_config.CS.config_signature_schemes
                      T.RsaPssRsaeSha256
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSignCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_server_finished_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 58 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerFinished
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_derive_shared_secret
  (s:server)
  (shared_src:array U8.t)
  (#shared:erased TLS13.Crypto.Spec.x25519_shared_secret)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to shared_src shared **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length (Ghost.reveal shared) == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalDeriveSharedSecret (Ghost.reveal shared))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to shared_src shared **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalDeriveSharedSecret
                   (Ghost.reveal shared)
                   network_out_bytes
                   app_out_bytes)

fn process_install_server_handshake_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalInstallTrafficKeysForRole {
                        CS.install_role = CS.ServerEndpoint;
                        CS.install_payload = {
                          CS.install_epoch = CS.TrafficHandshake;
                          CS.install_direction = CS.TrafficWrite;
                          CS.install_material = Ghost.reveal material;
                        };
                      })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalInstallServerHandshakeTrafficKeys
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_derive_and_install_server_handshake_write_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                   B.length 'old_app_out == SZ.v app_out_len /\
                   ST.server_end_to_end_invariant 'st0 /\
                   'st0.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsServerHelloSent /\
                   'st0.CS.cs_model.CS.model_config.CS.config_role ==
                     CS.ServerEndpoint /\
                   Some?
                     'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     st1
                     resp
                     ST.LocalInstallServerHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)

fn process_install_client_handshake_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                   B.length 'old_app_out == SZ.v app_out_len /\
                   ST.server_end_to_end_invariant 'st0 /\
                   CS.legal_event
                      'st0.CS.cs_model
                      (CS.ConnLocalEvent
                        (CS.LocalInstallTrafficKeysForRole {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficHandshake;
                            CS.install_direction = CS.TrafficRead;
                            CS.install_material = Ghost.reveal material;
                          };
                        })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     st1
                     resp
                     ST.LocalInstallClientHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)

fn process_derive_and_install_client_handshake_read_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                     B.length 'old_app_out == SZ.v app_out_len /\
                     ST.server_end_to_end_invariant 'st0 /\
                     'st0.CS.cs_model.CS.model_control ==
                       CS.ControlHandshaking CS.HsServerHelloSent /\
                     'st0.CS.cs_model.CS.model_config.CS.config_role ==
                       CS.ServerEndpoint /\
                     Some?
                       'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallClientHandshakeTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_install_server_application_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficWrite;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallServerApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_install_client_application_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src material.CS.traffic_key **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficRead;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src material.CS.traffic_key **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallClientApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_derive_and_install_server_application_write_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerFinishedSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        st1
                        resp
                        ST.LocalInstallServerApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_derive_and_install_client_application_read_keys
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientFinishedReceived /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        st1
                        resp
                        ST.LocalInstallClientApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_verify_client_finished
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                 CM.can_verify_client_finished
                   'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        st1
                        resp
                        ST.LocalVerifyClientFinished
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_client_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased M.client_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_client_hello lch ch **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 SZ.v fragment_len <= Bounds.max_client_hello_len /\
                 Seq.equal
                  (Ghost.reveal 'fragment_bytes)
                  (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) /\
                 lch.IM.client_hello_has_server_name == true /\
                 CM.client_hello_server_name_len_for ch ==
                  lch.IM.client_hello_server_name_len /\
                 CM.client_hello_cipher_suites_len_for ch ==
                  lch.IM.client_hello_cipher_suites_len /\
                 CM.client_hello_signature_schemes_len_for ch ==
                  lch.IM.client_hello_signature_schemes_len /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  B.length (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) <=
                  Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                 CS.event_raw_delta_legal
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.ClientHello ch))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
