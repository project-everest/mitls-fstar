module TLS13.Impl.Server.Driver.BufferedNetwork

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module BS = Common.BufferedStream
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module DS = TLS13.Impl.Server.Driver.State
module M = TLS13.Messages
module Seq = FStar.Seq
module Sem = TLS13.Wire.Semantics
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

noeq type network_read_result = {
  network_read_len: SZ.t;
  network_read_buffer_resp: ST.server_buffer_response;
  network_read_written: SZ.t;
  network_read_prefix: Ghost.erased B.bytes;
}

noeq type buffered_network_result = {
  buffered_network_read: network_read_result;
  buffered_network_new_len: SZ.t;
}

noeq type completed_drive = {
  completed_drive_outcome:
    BS.drive_outcome unit ST.server_status buffered_network_result;
  completed_drive_pending_len: SZ.t;
}

noeq type local_write_result = {
  local_write_resp: ST.server_response;
  local_write_written: SZ.t;
}

noextract
let local_event_ready
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : prop =
  kind <> ST.LocalSelectServerParameters /\
  kind <> ST.LocalStartServer /\
  kind <> ST.LocalSendServerHello /\
  ST.server_local_event_input_ready_with_credentials
    st kind payload certificate_chain credential_identity /\
  (kind == ST.LocalVerifyClientFinished /\
   Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
   B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
     Bounds.max_transcript_len /\
   CM.can_verify_client_finished st
     (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
  (kind == ST.LocalSendCertificateVerify /\
   Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
   (let cv =
      Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
    B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
      8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
    B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
        Bounds.max_transcript_len)) /\
  (kind == ST.LocalSendCertificate ==>
   1 <= B.length certificate_chain /\
   B.length certificate_chain <= 32768 /\
   B.length (W.serialize_handshake
     (M.Certificate (SS.mk_cert_witness certificate_chain))) ==
       13 + B.length certificate_chain)

noextract
let local_event_success_correct
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  : prop =
  kind == ST.LocalDeriveSharedSecret /\
  resp.ST.status == ST.StepOk ==>
  exists shared.
   st1 == CM.derived_shared_secret_state st0 shared /\
   (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
    | Some ch ->
      (match CS.client_hello_key_share ch with
       | Some client_public ->
         CryptoSpec.x25519_shared payload client_public == Some shared
       | None -> False)
    | None -> False)

fn process_local_event
  (d:DS.buffered_driver)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      local_event_ready
        'st0
        kind
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal 'certificate_chain)
        (Ghost.reveal 'credential_identity))
  returns result:local_write_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        ST.server_local_event_end_to_end_correct
          'st0
          st1
          result.local_write_resp
          kind
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          app_out_bytes /\
        local_event_success_correct
          'st0
          st1
          result.local_write_resp
          kind
          (Ghost.reveal 'payload_bytes) /\
        result.local_write_written ==
          result.local_write_resp.ST.network_out_len)

noextract
let completed_drive_correct
  (st0 st1:CS.connection_state)
  (old_network_out network_out old_app_out app_out:B.bytes)
  (result:completed_drive)
  : prop =
  match result.completed_drive_outcome with
  | BS.DriveExhausted ->
    st1 == st0 /\
    Seq.equal network_out old_network_out /\
    Seq.equal app_out old_app_out
  | BS.DriveYield network consumed _ _ ->
    let buffer_resp =
      network.buffered_network_read.network_read_buffer_resp in
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    buffer_resp.ST.response.ST.status == ST.StepOk /\
    consumed == buffer_resp.ST.consumed_len
  | BS.DriveReject network error _ ->
    let buffer_resp =
      network.buffered_network_read.network_read_buffer_resp in
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    ST.server_network_consumed_input_projection
      st0
      st1
      buffer_resp
      (Ghost.reveal network.buffered_network_read.network_read_prefix)
      network_out
      app_out /\
    buffer_resp.ST.response.ST.status == error /\
    error <> ST.NeedMoreInput /\
    error <> ST.StepOk
  | BS.DriveProgress _ _ _
  | BS.DriveBufferFull _ _ ->
    False

inline_for_extraction
fn drive
  (d:DS.buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns result:completed_drive
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.completed_drive_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.completed_drive_pending_len /\
        B.length network_out_bytes == SZ.v network_out_capacity /\
        B.length app_out_bytes == SZ.v app_out_capacity /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        ST.server_end_to_end_invariant st1 /\
        completed_drive_correct
          'st0
          st1
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes
          result)
