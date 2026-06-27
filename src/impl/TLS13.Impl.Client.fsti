module TLS13.Impl.Client

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CR = TLS13.Impl.ConnectionState.Repr
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type client = CR.connection_state

let connection_exactly (c:client) (st:CS.connection_state) : slprop =
  CR.connection_exactly c st

noextract
let next_local_action_internal_input_ready
  (st:CS.connection_state)
  (action:CT.next_local_action)
  : prop =
  action.CT.next_local_ready ==> (
  match action.CT.next_local_kind with
  | CT.LocalValidateCertificate
  | CT.LocalVerifyCertificateSignature ->
    True
  | _ ->
    CT.local_input_wf st action.CT.next_local_kind B.empty)

noextract
let next_local_action_sound
  (st:CS.connection_state)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (action:CT.next_local_action)
  : prop =
  if action.CT.next_local_ready then
    next_local_action_internal_input_ready st action /\
    (match action.CT.next_local_kind with
    | CT.LocalStartHandshake ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control == CS.ControlNew /\
      st.CS.cs_model.CS.model_handshake.CS.hs_start == None
    | CT.LocalSendClientHello ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsStarted /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_start /\
      st.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript
        <= Bounds.max_transcript_len - Bounds.max_client_hello_len /\
      517 <= SZ.v network_out_len
    | CT.LocalDeriveSharedSecret ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloReceived /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
    | CT.LocalInstallClientHandshakeTrafficKeys ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloReceived /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
    | CT.LocalInstallServerHandshakeTrafficKeys ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloReceived /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
    | CT.LocalValidateCertificate ->
      action.CT.next_local_payload == CT.LocalPayloadCertificatePublicKey /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateReceived /\
      st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der /\
      SZ.v certificate_public_key_len <= Bounds.max_public_key_len
    | CT.LocalVerifyCertificateSignature ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
      st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false
    | CT.LocalVerifyFinished ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedReceived /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      st.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
        Bounds.max_transcript_len
    | CT.LocalInstallClientApplicationTrafficKeys ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedVerified /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
    | CT.LocalInstallServerApplicationTrafficKeys ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedVerified /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
      not (Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | CT.LocalSendClientFinished ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedVerified /\
      st.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
      FStar.UInt64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36
        <= Bounds.max_transcript_len /\
      58 <= SZ.v network_out_len
    | CT.LocalSendKeyUpdate ->
      action.CT.next_local_payload == CT.LocalPayloadNone /\
      st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
      st.CS.cs_model.CS.model_application.CS.app_key_update_response_pending /\
      Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
      FStar.UInt64.fits
        (st.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
      27 <= SZ.v network_out_len
    | _ ->
      False)
  else
    action.CT.next_local_kind == CT.LocalFail /\
    action.CT.next_local_payload == CT.LocalPayloadNone

noextract
let client_state_ref (c:client) : CR.state_ref =
  CR.connection_state_ref c

fn new_client_default ()
  returns c:client
  ensures CR.connection_exactly c CR.default_initial_state **
          pure (CT.client_state_correct CR.default_initial_state /\
                CT.client_end_to_end_invariant CR.default_initial_state /\
                CS.connection_state_raw_to_message_replay_consistent
                  CR.default_initial_state /\
                CS.connection_state_sent_seal_replay_consistent
                  CR.default_initial_state /\
                CS.connection_state_sent_seal_key_schedule_replay_consistent
                  CR.default_initial_state /\
                CS.connection_state_received_decode_replay_consistent
                  CR.default_initial_state /\
                CS.connection_state_received_decode_key_schedule_replay_consistent
                  CR.default_initial_state /\
                CS.connection_state_protected_raw_segmented_replay_consistent
                  CR.default_initial_state)

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <= Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <= Bounds.max_trust_anchors_len)
  returns c:client
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          CR.connection_exactly
            c
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_state_correct
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) /\
                CT.client_end_to_end_invariant
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_raw_to_message_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_sent_seal_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_sent_seal_key_schedule_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_received_decode_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_received_decode_key_schedule_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                CS.connection_state_protected_raw_segmented_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))

fn control_snapshot
  (c:client)
  requires CR.connection_exactly c 'st0
  returns snapshot:CR.control_snapshot
  ensures CR.connection_exactly c 'st0 **
          pure (CR.control_snapshot_matches snapshot 'st0)

fn next_local_action
  (c:client)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  requires CR.connection_exactly c 'st0
  returns action:CT.next_local_action
  ensures CR.connection_exactly c 'st0 **
          pure (next_local_action_sound
            'st0
            network_out_len
            certificate_public_key_len
            server_finished_payload_len
            action)

fn copy_certificate_leaf_der
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          CR.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                | Some leaf ->
                  SZ.v copied_len == B.length leaf /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                | None -> False))

fn copy_certificate_verify_input
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          CR.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                | Some input ->
                  SZ.v copied_len == B.length input /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                | None -> False))

fn copy_certificate_verify_signature
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          CR.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  L.signature_scheme_matches snapshot.CR.cv_signature_scheme cv.M.scheme /\
                  SZ.v snapshot.CR.cv_signature_len == B.length cv.M.signature /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                    cv.M.signature
                | None -> False))

fn process_network_bytes
  (c:client)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns buffer_resp: CT.client_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  network_out_bytes
                  'old_app_out
                  app_out_bytes /\
                (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
                 buffer_resp.CT.consumed_len == 0sz))

fn process_local_event
  (c:client)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                (resp.CT.status == CT.StepOk \/
                 resp.CT.status == CT.IllegalTransition \/
                 resp.CT.status == CT.ConnectionFailed))
