module TLS13.Impl.Client

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module C = TLS13.Impl.ConnectionState
module CT = TLS13.Impl.Client.Types
module HDispatch = TLS13.Impl.Handle.Dispatch
module HDecodeError = TLS13.Impl.Handle.DecodeError
module HLocal = TLS13.Impl.Handle.Local
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module P = TLS13.Impl.Parser
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

fn new_client_default ()
  returns c:client
  ensures C.connection_exactly c C.default_initial_state
{
  C.new_client_default ()
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
                 SZ.v server_name_len <= C.max_hostname_len /\
                 SZ.v trust_anchors_len <= C.max_trust_anchors_len)
  returns c:client
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          C.connection_exactly
            c
            (C.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds)
{
  C.new_client
    server_name
    server_name_len
    trust_anchors
    trust_anchors_len
    validation_time_seconds
}

fn control_snapshot
  (c:client)
  requires C.connection_exactly c 'st0
  returns snapshot:C.control_snapshot
  ensures C.connection_exactly c 'st0 **
          pure (C.control_snapshot_matches snapshot 'st0)
{
  C.get_control_snapshot c
}

fn next_local_action
  (c:client)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  requires C.connection_exactly c 'st0
  returns action:CT.next_local_action
  ensures C.connection_exactly c 'st0
{
  let no_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let control = C.get_control_snapshot c;
  let keys = C.get_key_schedule_snapshot c;
  let start_ready = C.can_start_handshake_runtime c;
  let client_hello_ready = C.can_send_client_hello_runtime c network_out_len;
  let derive_ready =
    (control.C.snapshot_control_tag = 1uy) &&
    (control.C.snapshot_handshake_stage_tag = 3uy) &&
    not keys.C.snapshot_handshake_secret_present;
  let handshake_keys_ready = C.can_install_handshake_traffic_keys c;
  let client_handshake_keys_ready =
    handshake_keys_ready &&
    not keys.C.snapshot_client_handshake_traffic_present;
  let server_handshake_keys_ready =
    handshake_keys_ready &&
    not keys.C.snapshot_server_handshake_traffic_present;
  let certificate_ready =
    C.can_validate_certificate c certificate_public_key_len;
  let certificate_signature_ready =
    C.can_verify_certificate_signature c;
  let finished_ready =
    C.can_verify_server_finished c server_finished_payload_len;
  let application_keys_ready =
    C.can_install_application_traffic_keys c;
  let client_application_keys_ready =
    application_keys_ready &&
    not keys.C.snapshot_client_application_traffic_present;
  let server_application_keys_ready =
    application_keys_ready &&
    not keys.C.snapshot_server_application_traffic_present;
  let client_finished_ready =
    C.can_send_client_finished_runtime c network_out_len;
  let key_update_ready =
    C.can_send_key_update_runtime c network_out_len;

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
      CT.next_local_payload = CT.LocalPayloadServerFinishedHandshake;
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
  requires C.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 C.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          C.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                | Some leaf ->
                  SZ.v copied_len == B.length leaf /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                | None -> False))
{
  C.copy_certificate_leaf_der c out out_len
}

fn copy_certificate_verify_input
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 C.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          C.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                | Some input ->
                  SZ.v copied_len == B.length input /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                | None -> False))
{
  C.copy_certificate_verify_input c out out_len
}

fn copy_certificate_verify_signature
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:C.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          C.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.C.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  L.signature_scheme_matches snapshot.C.cv_signature_scheme cv.M.scheme /\
                  SZ.v snapshot.C.cv_signature_len == B.length cv.M.signature /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.C.cv_signature_len))
                    cv.M.signature
                | None -> False))
{
  C.copy_certificate_verify_signature c out out_len
}

fn copy_server_finished_verify_data
  (c:client)
  (out:array U8.t)
  (out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 32 <= SZ.v out_len /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          C.connection_exactly c 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len == 32 /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
                 | Some fin ->
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v copied_len))
                     fin.M.verify_data
                 | None -> False))
{
  C.copy_server_finished_verify_data c out out_len
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
  requires C.connection_exactly c 'st0 **
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
          C.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  st1
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes /\
                CT.some_legal_response 'st0 st1 resp network_out_bytes app_out_bytes)
{
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
  requires C.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          C.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ((resp.CT.status == CT.NeedMoreInput /\
                  resp.CT.network_out_len == 0sz /\
                  resp.CT.app_out_len == 0sz /\
                  st1 == 'st0 /\
                  Seq.equal network_out_bytes 'old_network_out /\
                  Seq.equal app_out_bytes 'old_app_out) \/
                 CT.some_legal_response
                   'st0
                   st1
                   resp
                   network_out_bytes
                   app_out_bytes /\
                 CT.some_legal_response_for_network_input
                   'st0
                   st1
                   resp
                   (Ghost.reveal 'raw_bytes)
                   network_out_bytes
                   app_out_bytes))
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
        (C.local_fail_state 'st0 C.tls_decode_error)
        resp
        'old_network_out
        'old_app_out));
      CT.lemma_decode_error_response_for_network_input
        'st0
        (C.local_fail_state 'st0 C.tls_decode_error)
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
  requires C.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns buffer_resp: CT.client_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          C.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let resp = buffer_resp.CT.response in
                 ((resp.CT.status == CT.NeedMoreInput /\
                   buffer_resp.CT.consumed_len == 0sz /\
                   resp.CT.network_out_len == 0sz /\
                   resp.CT.app_out_len == 0sz /\
                   st1 == 'st0 /\
                   Seq.equal network_out_bytes 'old_network_out /\
                   Seq.equal app_out_bytes 'old_app_out) \/
                  (SZ.v buffer_resp.CT.consumed_len <= B.length (Ghost.reveal 'raw_bytes) /\
                   CT.some_legal_response
                     'st0
                     st1
                     resp
                     network_out_bytes
                     app_out_bytes /\
                   CT.some_legal_response_for_network_prefix
                     'st0
                     st1
                     resp
                     (Ghost.reveal 'raw_bytes)
                     buffer_resp.CT.consumed_len
                     network_out_bytes
                     app_out_bytes))))
{
  let decoded = P.decode_network_buffer c raw raw_len;
  match decoded {
    L.NetworkBufferNeedMoreInput -> {
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.NeedMoreInput;
      };
      {
        CT.response = resp;
        CT.consumed_len = 0sz;
      }
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
        (C.local_fail_state 'st0 C.tls_decode_error)
        resp
        'old_network_out
        'old_app_out));
      CT.lemma_decode_error_response_for_network_input
        'st0
        (C.local_fail_state 'st0 C.tls_decode_error)
        resp
        (Seq.slice (Ghost.reveal 'raw_bytes) 0 0)
        'old_network_out
        'old_app_out;
      {
        CT.response = resp;
        CT.consumed_len = 0sz;
      }
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
      V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
      V.free decoded_buffer.L.decoded_buffer_fragment;
      V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
      V.free decoded_buffer.L.decoded_buffer_raw_record;
      {
        CT.response = resp;
        CT.consumed_len = decoded_buffer.L.decoded_buffer_consumed_len;
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
  requires C.connection_exactly c 'st0 **
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
          C.connection_exactly c st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.some_legal_response 'st0 st1 resp network_out_bytes app_out_bytes /\
                CT.legal_handled_local_response
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
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
  resp
}
