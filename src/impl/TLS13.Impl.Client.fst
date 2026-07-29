module TLS13.Impl.Client

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CM = TLS13.Impl.ConnectionState.Model
module CT = TLS13.Impl.Client.Types
module FB = TLS13.Impl.Client.FragmentBound
module HDispatch = TLS13.Impl.Handle.Dispatch
module HDecodeError = TLS13.Impl.Handle.DecodeError
module HLocal = TLS13.Impl.Handle.Local
module ID = FStar.IndefiniteDescription
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module P = TLS13.Impl.Parser
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec

let lemma_parse_record_wire_exact_positive
  (raw:B.bytes)
  : Lemma
      (requires
        exists outer_ct outer_fragment.
          WS.parse_record_wire raw ==
            Some (outer_ct, outer_fragment, B.length raw))
      (ensures 0 < B.length raw)
=
  let outer_ct =
    ID.indefinite_description_ghost
      T.content_type
      (fun outer_ct -> exists outer_fragment.
        WS.parse_record_wire raw ==
          Some (outer_ct, outer_fragment, B.length raw)) in
  let outer_fragment =
    ID.indefinite_description_ghost
      M.sealed_record
      (fun outer_fragment ->
        WS.parse_record_wire raw ==
          Some (outer_ct, outer_fragment, B.length raw)) in
  WS.lemma_parse_record_wire_some_consumed_positive
    raw
    outer_ct
    outer_fragment
    (B.length raw)

fn new_client_default ()
  returns c:client
  ensures CR.connection_exactly c CR.default_initial_state **
          pure (CT.client_state_correct CR.default_initial_state /\
                CT.client_end_to_end_invariant CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_raw_to_message_replay_consistent
                  CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent
                  CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_key_schedule_replay_consistent
                  CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent
                  CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_key_schedule_replay_consistent
                  CR.default_initial_state /\
                TLS13.Spec.StateMachine.Replay.connection_state_protected_raw_segmented_replay_consistent
                  CR.default_initial_state)
{
  let c = CR.new_client_default ();
  CT.lemma_initial_client_state_correct CR.default_connection_config;
  CT.lemma_initial_client_end_to_end_invariant CR.default_connection_config;
  CSL.lemma_initial_raw_to_message_replay_consistent CR.default_connection_config;
  CSL.lemma_initial_sent_seal_replay_consistent CR.default_connection_config;
  CSL.lemma_initial_sent_seal_key_schedule_replay_consistent CR.default_connection_config;
  CSL.lemma_initial_received_decode_replay_consistent CR.default_connection_config;
  CSL.lemma_initial_received_decode_key_schedule_replay_consistent CR.default_connection_config;
  CT.lemma_client_state_correct_protected_raw_segmented_replay CR.default_initial_state;
  c
}

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
                TLS13.Spec.StateMachine.Replay.connection_state_raw_to_message_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_key_schedule_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_key_schedule_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds) /\
                TLS13.Spec.StateMachine.Replay.connection_state_protected_raw_segmented_replay_consistent
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))
{
  let c =
    CR.new_client
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  CT.lemma_initial_client_state_correct
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CT.lemma_initial_client_end_to_end_invariant
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CSL.lemma_initial_raw_to_message_replay_consistent
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CSL.lemma_initial_sent_seal_replay_consistent
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CSL.lemma_initial_sent_seal_key_schedule_replay_consistent
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CSL.lemma_initial_received_decode_replay_consistent
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CSL.lemma_initial_received_decode_key_schedule_replay_consistent
    (CR.configured_connection_config
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  CT.lemma_client_state_correct_protected_raw_segmented_replay
    (CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  c
}

fn control_snapshot
  (c:client)
  requires CR.connection_exactly c 'st0
  returns snapshot:CR.control_snapshot
  ensures CR.connection_exactly c 'st0 **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  CQ.get_control_snapshot c
}

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
{
  let no_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let control = CQ.get_control_snapshot c;
  let keys = CQ.get_key_schedule_snapshot c;
  let start_ready = CQ.can_start_handshake_runtime c;
  let client_hello_ready = CQ.can_send_client_hello_runtime c network_out_len;
  let derive_ready =
    (control.CR.snapshot_control_tag = 1uy) &&
    (control.CR.snapshot_handshake_stage_tag = 3uy) &&
    not keys.CR.snapshot_handshake_secret_present;
  let handshake_keys_ready = CQ.can_install_handshake_traffic_keys c;
  let client_handshake_keys_ready =
    handshake_keys_ready &&
    not keys.CR.snapshot_client_handshake_traffic_present;
  let server_handshake_keys_ready =
    handshake_keys_ready &&
    not keys.CR.snapshot_server_handshake_traffic_present;
  let certificate_ready =
    CQ.can_validate_certificate c certificate_public_key_len;
  let certificate_signature_ready =
    CQ.can_verify_certificate_signature c;
  let finished_ready =
    CQ.can_verify_server_finished c 36sz;
  let application_keys_ready =
    CQ.can_install_application_traffic_keys c;
  let client_application_keys_ready =
    application_keys_ready &&
    not keys.CR.snapshot_client_application_traffic_present;
  let server_application_keys_ready =
    application_keys_ready &&
    not keys.CR.snapshot_server_application_traffic_present;
  let client_finished_ready =
    CQ.can_send_client_finished_runtime c network_out_len;
  let key_update_ready =
    CQ.can_send_key_update_runtime c network_out_len;

  if start_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalStartHandshake;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if client_hello_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalSendClientHello;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if derive_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalDeriveSharedSecret;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if client_handshake_keys_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalInstallClientHandshakeTrafficKeys;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if server_handshake_keys_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalInstallServerHandshakeTrafficKeys;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if certificate_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalValidateCertificate;
      CT.next_local_payload = CT.LocalPayloadCertificatePublicKey;
    }
  } else if certificate_signature_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalVerifyCertificateSignature;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if finished_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalVerifyFinished;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if client_application_keys_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalInstallClientApplicationTrafficKeys;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if server_application_keys_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalInstallServerApplicationTrafficKeys;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if client_finished_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalSendClientFinished;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else if key_update_ready {
    {
      CT.next_local_ready = true;
      CT.next_local_kind = CT.LocalSendKeyUpdate;
      CT.next_local_payload = CT.LocalPayloadNone;
    }
  } else {
    no_action
  }
}

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
{
  CQ.copy_certificate_leaf_der c out out_len
}

fn copy_certificate_chain
  (c:client)
  (chain_out:array U8.t)
  (chain_out_len:SZ.t)
  (offsets_out:array SZ.t)
  (offsets_out_len:SZ.t)
  (lens_out:array SZ.t)
  (lens_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to chain_out 'old_chain_out **
           pts_to offsets_out 'old_offsets_out **
           pts_to lens_out 'old_lens_out **
           pure (B.length 'old_chain_out == SZ.v chain_out_len /\
                 Seq.length 'old_offsets_out == SZ.v offsets_out_len /\
                 Seq.length 'old_lens_out == SZ.v lens_out_len /\
                 SZ.v chain_out_len == L.max_certificate_chain_bytes /\
                 SZ.v offsets_out_len == L.max_certificate_chain_entries /\
                 SZ.v lens_out_len == L.max_certificate_chain_entries /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate)
  returns snapshot:CR.certificate_chain_snapshot
  ensures exists* chain_bytes offsets lens.
          CR.connection_exactly c 'st0 **
          pts_to chain_out chain_bytes **
          pts_to offsets_out offsets **
          pts_to lens_out lens **
          pure (B.length chain_bytes == SZ.v chain_out_len /\
                Seq.length offsets == SZ.v offsets_out_len /\
                Seq.length lens == SZ.v lens_out_len /\
                SZ.v snapshot.CR.certificate_chain_bytes_len <=
                  B.length chain_bytes /\
                SZ.v snapshot.CR.certificate_chain_cert_count <=
                  Seq.length offsets /\
                SZ.v snapshot.CR.certificate_chain_cert_count <=
                  Seq.length lens /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate with
                 | Some cert ->
                   L.certificate_chain_matches
                     chain_bytes
                     (SZ.v snapshot.CR.certificate_chain_bytes_len)
                     offsets
                     lens
                     (SZ.v snapshot.CR.certificate_chain_cert_count)
                     (Sem.certificate_entries cert)
                 | None -> False))
{
  CQ.copy_certificate_chain
    c
    chain_out
    chain_out_len
    offsets_out
    offsets_out_len
    lens_out
    lens_out_len
}

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
{
  CQ.copy_certificate_verify_input c out out_len
}

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
                  L.signature_scheme_matches snapshot.CR.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                  SZ.v snapshot.CR.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                    (Sem.certificateVerify_signature_bytes cv)
                | None -> False))
{
  CQ.copy_certificate_verify_signature c out out_len
}

fn process_network_event
  (c:client)
  (content_type:U8.t)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len /\
                 CT.network_input_wf
                   'st0
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (Ghost.reveal 'raw_bytes))
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.network_event_step_correct
                  'st0
                  st1
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  FB.lemma_network_input_wf_fragment_bound
    'st0
    content_type
    (Ghost.reveal 'fragment_bytes)
    (Ghost.reveal 'raw_bytes);
  let parsed = P.parse_tls_message content_type fragment fragment_len;
  HDispatch.dispatch_network_event
    c
    content_type
    parsed
    raw
    raw_len
    fragment
    fragment_len
    network_out
    network_out_len
    app_out
    app_out_len
}

fn process_tls_record
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
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.tls_record_step_correct
                  'st0
                  st1
                  resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  network_out_bytes
                  'old_app_out
                  app_out_bytes)
{
  let decoded = P.decode_network_record c raw raw_len;
  match decoded {
    L.NetworkRecordNeedMoreInput -> {
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.NeedMoreInput;
      };
      resp
    }
    L.NetworkRecordDecodeError -> {
      let resp =
        HDecodeError.handle_decode_error
          c
          raw
          raw_len
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (CT.decode_error_response
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        resp
        'old_network_out
        'old_app_out));
      CT.lemma_decode_error_response_for_network_input
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      resp
    }
    L.NetworkRecordOk decoded_record -> {
      with fragment_bytes.
        assert (V.pts_to decoded_record.L.decoded_record_fragment fragment_bytes);
      V.to_array_pts_to decoded_record.L.decoded_record_fragment;
      let resp =
        HDispatch.dispatch_network_event
          c
          decoded_record.L.decoded_record_content_type
          decoded_record.L.decoded_record_parsed
          raw
          raw_len
          (V.vec_to_array decoded_record.L.decoded_record_fragment)
          decoded_record.L.decoded_record_fragment_len
          network_out
          network_out_len
          app_out
          app_out_len;
      V.to_vec_pts_to decoded_record.L.decoded_record_fragment;
      V.free decoded_record.L.decoded_record_fragment;
      resp
    }
  }
}

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
                 CT.response_stuttered
                   'st0
                   st1
                   buffer_resp.CT.response
                   'old_network_out
                   network_out_bytes
                   'old_app_out
                   app_out_bytes) /\
                (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
                 buffer_resp.CT.consumed_len == 0sz /\
                 WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
                 WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None) /\
                (buffer_resp.CT.response.CT.status == CT.StepOk ==>
                 0 < SZ.v buffer_resp.CT.consumed_len) /\
                (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (SZ.v buffer_resp.CT.response.CT.app_out_len > 0 ==>
                 buffer_resp.CT.response.CT.status == CT.StepOk /\
                 buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False))
{
  let decoded = P.decode_network_buffer c raw raw_len;
  match decoded {
    L.NetworkBufferNeedMoreInput -> {
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.NeedMoreInput;
      };
      let buffer_resp = {
        CT.response = resp;
        CT.consumed_len = 0sz;
      };
      CT.lemma_network_bytes_decoded_message_projection_intro_consumed_zero
        'st0
        'st0
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      CT.lemma_network_bytes_decode_error_projection_intro_non_decode_error
        'st0
        'st0
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      CT.lemma_network_bytes_step_correct_end_to_end
        'st0
        'st0
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_network_out
        'old_app_out
        'old_app_out;
      assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
        buffer_resp.CT.consumed_len == 0sz /\
        WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
        WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None));
      assert (pure (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
        buffer_resp.CT.consumed_len == 0sz));
      assert (pure (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
        buffer_resp.CT.consumed_len == 0sz));
      assert (pure (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
      buffer_resp
    }
    L.NetworkBufferDecodeError -> {
      let resp =
        HDecodeError.handle_decode_error
          c
          raw
          raw_len
          network_out
          network_out_len
          app_out
          app_out_len;
      assert (pure (CT.decode_error_response
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        resp
        'old_network_out
        'old_app_out));
      CT.lemma_decode_error_response_for_network_input
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        resp
        (Seq.slice (Ghost.reveal 'raw_bytes) 0 0)
        'old_network_out
        'old_app_out;
      let buffer_resp = {
        CT.response = resp;
        CT.consumed_len = 0sz;
      };
      CT.lemma_network_bytes_decode_error_projection_intro_consumed_zero
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      CT.lemma_network_bytes_decoded_message_projection_intro_consumed_zero
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      CT.lemma_network_bytes_step_correct_end_to_end
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        buffer_resp
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_network_out
        'old_app_out
        'old_app_out;
      assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
        buffer_resp.CT.consumed_len == 0sz));
      assert (pure (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
        buffer_resp.CT.consumed_len == 0sz));
      assert (pure (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
        buffer_resp.CT.consumed_len == 0sz));
      assert (pure (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
      buffer_resp
    }
    L.NetworkBufferOk decoded_buffer -> {
      with raw_record_bytes fragment_bytes.
        assert (V.pts_to decoded_buffer.L.decoded_buffer_raw_record raw_record_bytes **
                V.pts_to decoded_buffer.L.decoded_buffer_fragment fragment_bytes);
      V.to_array_pts_to decoded_buffer.L.decoded_buffer_raw_record;
      V.to_array_pts_to decoded_buffer.L.decoded_buffer_fragment;
      let resp =
        HDispatch.dispatch_network_event
          c
          decoded_buffer.L.decoded_buffer_content_type
          decoded_buffer.L.decoded_buffer_parsed
          (V.vec_to_array decoded_buffer.L.decoded_buffer_raw_record)
          decoded_buffer.L.decoded_buffer_raw_record_len
          (V.vec_to_array decoded_buffer.L.decoded_buffer_fragment)
          decoded_buffer.L.decoded_buffer_fragment_len
          network_out
          network_out_len
          app_out
          app_out_len;
      let buffer_resp = {
        CT.response = resp;
        CT.consumed_len = decoded_buffer.L.decoded_buffer_consumed_len;
      };
      with st1 network_out_bytes app_out_bytes.
        assert (CR.connection_exactly c st1 **
                pts_to (V.vec_to_array decoded_buffer.L.decoded_buffer_raw_record) raw_record_bytes **
                pts_to (V.vec_to_array decoded_buffer.L.decoded_buffer_fragment) fragment_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (SZ.v decoded_buffer.L.decoded_buffer_consumed_len <=
        B.length (Ghost.reveal 'raw_bytes)));
      assert (pure (resp.CT.status == CT.NeedMoreInput ==> False));
      assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
        buffer_resp.CT.consumed_len == 0sz));
      lemma_parse_record_wire_exact_positive raw_record_bytes;
      assert (pure (0 < SZ.v decoded_buffer.L.decoded_buffer_consumed_len));
      assert (pure (Seq.equal
        raw_record_bytes
        (CT.network_consumed_prefix
          (Ghost.reveal 'raw_bytes)
          decoded_buffer.L.decoded_buffer_consumed_len)));
      let decoded_error = resp.CT.status = CT.DecodeError;
      if decoded_error {
        // A content-level decode error carries the same "zero bytes
        // received" model event (CM.local_fail_state ... tls_decode_error,
        // via decode_error_response) as a framing-level decode error, even
        // though the underlying record itself was successfully framed
        // (nonzero decoded_buffer_consumed_len).  To keep the returned
        // buffer_resp consistent with network_process_correct's raw
        // received-log equation (received1 == received0 ++ consumed), we
        // report a zero-length consumption here too, exactly mirroring the
        // L.NetworkBufferDecodeError (framing-level) case above.
        CT.lemma_legal_network_response_decode_error_response
          'st0
          st1
          resp
          decoded_buffer.L.decoded_buffer_content_type
          fragment_bytes
          raw_record_bytes
          network_out_bytes
          app_out_bytes;
        assert (pure (CT.decode_error_response
          'st0
          st1
          resp
          network_out_bytes
          app_out_bytes));
        let buffer_resp0 = {
          CT.response = resp;
          CT.consumed_len = 0sz;
        };
        CT.lemma_decode_error_response_for_network_input
          'st0
          st1
          resp
          (CT.network_consumed_prefix (Ghost.reveal 'raw_bytes) 0sz)
          network_out_bytes
          app_out_bytes;
        CT.lemma_network_bytes_decode_error_projection_intro_consumed_zero
          'st0
          st1
          buffer_resp0
          (Ghost.reveal 'raw_bytes)
          network_out_bytes
          app_out_bytes;
        CT.lemma_network_bytes_decoded_message_projection_intro_consumed_zero
          'st0
          st1
          buffer_resp0
          (Ghost.reveal 'raw_bytes)
          network_out_bytes
          app_out_bytes;
        CT.lemma_network_bytes_step_correct_end_to_end
          'st0
          st1
          buffer_resp0
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes;
        assert (pure (buffer_resp0.CT.response.CT.status == CT.NeedMoreInput ==>
          buffer_resp0.CT.consumed_len == 0sz));
        assert (pure (buffer_resp0.CT.response.CT.status == CT.DecodeError ==>
          buffer_resp0.CT.consumed_len == 0sz));
        assert (pure (buffer_resp0.CT.response.CT.status == CT.IllegalTransition ==>
          buffer_resp0.CT.consumed_len == 0sz));
        assert (pure (buffer_resp0.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
        V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
        V.free decoded_buffer.L.decoded_buffer_fragment;
        V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
        V.free decoded_buffer.L.decoded_buffer_raw_record;
        buffer_resp0
      } else {
        assert (pure (decoded_error == false));
        assert (pure (resp.CT.status == CT.DecodeError ==> False));
        let illegal_transition = resp.CT.status = CT.IllegalTransition;
        if illegal_transition {
          assert (pure (resp.CT.status == CT.IllegalTransition));
          assert (pure (CT.unexpected_message_response
            'st0
            st1
            resp
            network_out_bytes
            app_out_bytes));
          let buffer_resp0 = {
            CT.response = resp;
            CT.consumed_len = 0sz;
          };
          CT.lemma_unexpected_message_response_for_network_input
            'st0
            st1
            resp
            (CT.network_consumed_prefix (Ghost.reveal 'raw_bytes) 0sz)
            network_out_bytes
            app_out_bytes;
          CT.lemma_network_bytes_decode_error_projection_intro_consumed_zero
            'st0
            st1
            buffer_resp0
            (Ghost.reveal 'raw_bytes)
            network_out_bytes
            app_out_bytes;
          CT.lemma_network_bytes_decoded_message_projection_intro_consumed_zero
            'st0
            st1
            buffer_resp0
            (Ghost.reveal 'raw_bytes)
            network_out_bytes
            app_out_bytes;
          CT.lemma_network_bytes_step_correct_end_to_end
            'st0
            st1
            buffer_resp0
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            network_out_bytes
            'old_app_out
            app_out_bytes;
          assert (pure (buffer_resp0.CT.response.CT.status == CT.NeedMoreInput ==>
            buffer_resp0.CT.consumed_len == 0sz));
          assert (pure (buffer_resp0.CT.response.CT.status == CT.DecodeError ==>
            buffer_resp0.CT.consumed_len == 0sz));
          assert (pure (buffer_resp0.CT.response.CT.status == CT.IllegalTransition ==>
            buffer_resp0.CT.consumed_len == 0sz));
          assert (pure (buffer_resp0.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
          V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
          V.free decoded_buffer.L.decoded_buffer_fragment;
          V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
          V.free decoded_buffer.L.decoded_buffer_raw_record;
          buffer_resp0
        } else {
        assert (pure (illegal_transition == false));
        assert (pure (resp.CT.status == CT.IllegalTransition ==> False));
        CT.lemma_network_bytes_decoded_message_projection_intro_network_response
          'st0
          st1
          buffer_resp
          (Ghost.reveal 'raw_bytes)
          decoded_buffer.L.decoded_buffer_content_type
          fragment_bytes
          raw_record_bytes
          network_out_bytes
          app_out_bytes;
        CT.lemma_network_bytes_decode_error_projection_intro_non_decode_error
          'st0
          st1
          buffer_resp
          (Ghost.reveal 'raw_bytes)
          network_out_bytes
          app_out_bytes;
        CT.lemma_network_bytes_step_correct_end_to_end
          'st0
          st1
          buffer_resp
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes;
        assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
          buffer_resp.CT.consumed_len == 0sz));
        assert (pure (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
          buffer_resp.CT.consumed_len == 0sz));
        assert (pure (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
          buffer_resp.CT.consumed_len == 0sz));
        assert (pure (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==> False));
        V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
        V.free decoded_buffer.L.decoded_buffer_fragment;
        V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
        V.free decoded_buffer.L.decoded_buffer_raw_record;
        buffer_resp
        }
      }
    }
  }
}

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
{
  let resp =
    HLocal.handle_local_event
      c
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly c st1 **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_step_correct_end_to_end
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  resp
}
