module TLS13.Impl.Client.Engine

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module C = TLS13.Impl.Client
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Drain
module L = TLS13.Impl.Messages
module Sem = TLS13.Wire.Semantics
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val client_engine : Type0

inline_for_extraction
let engine_network_out_capacity : SZ.t = 20000sz

inline_for_extraction
let engine_app_out_capacity : SZ.t = 16640sz

inline_for_extraction
let engine_certificate_chain_capacity : SZ.t = 32768sz

inline_for_extraction
let engine_certificate_chain_entries : SZ.t = 8sz

inline_for_extraction
let engine_certificate_verify_input_capacity : SZ.t = 256sz

inline_for_extraction
let engine_signature_capacity : SZ.t = 4096sz

// Real-world leaf certificates with large SAN lists exceed 4096 bytes
// (e.g. googleapis.com is 6840 bytes). Must match
// TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY in runtime/tls13_client_engine.h
// and stay within Bounds.max_public_key_len.
inline_for_extraction
let engine_public_key_capacity : SZ.t = 16384sz

type engine_action =
  | EngineProgress
  | EngineNeedNetworkInput
  | EngineNeedCertificateVerification
  | EngineNeedCertificateSignatureVerification
  | EngineNetworkOutput
  | EngineApplicationData
  | EngineReady
  | EngineClosing
  | EngineClosed
  | EngineFailed

type engine_step_result = {
  engine_step_action: engine_action;
  engine_step_status: CT.client_status;
  engine_step_consumed_len: SZ.t;
  engine_step_network_out_len: SZ.t;
  engine_step_app_out_len: SZ.t;
}

type certificate_verify_request = {
  certificate_verify_input_len: SZ.t;
  certificate_verify_signature_scheme: FStar.UInt16.t;
  certificate_verify_signature_len: SZ.t;
}

val engine_live :
  e:client_engine ->
  st:CS.connection_state ->
  slprop

val engine_released :
  e:client_engine ->
  st:CS.connection_state ->
  slprop

noextract
let engine_waiting_for_certificate
  (st:CS.connection_state)
  : prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateReceived /\
  st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate

noextract
let engine_waiting_for_certificate_signature
  (st:CS.connection_state)
  : prop =
  st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
  Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
  Some?
    st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
  st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false

noextract
let engine_external_certificate_validation
  (st:CS.connection_state)
  (public_key:B.bytes)
  : prop =
  engine_waiting_for_certificate st /\
  CT.local_input_wf st CT.LocalValidateCertificate public_key

noextract
let engine_external_signature_validation
  (st:CS.connection_state)
  : prop =
  engine_waiting_for_certificate_signature st /\
  CT.local_input_wf st CT.LocalVerifyCertificateSignature B.empty

noextract
let engine_result_buffers_wf
  (result:engine_step_result)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  SZ.v result.engine_step_network_out_len <= B.length network_out /\
  SZ.v result.engine_step_app_out_len <= B.length app_out

noextract
let engine_local_result_matches
  (result:engine_step_result)
  (resp:CT.client_response)
  : prop =
  result.engine_step_status == resp.CT.status /\
  result.engine_step_consumed_len == 0sz /\
  result.engine_step_network_out_len == resp.CT.network_out_len /\
  result.engine_step_app_out_len == resp.CT.app_out_len /\
  result.engine_step_action ==
    (if resp.CT.status <> CT.StepOk
     then EngineFailed
     else if resp.CT.app_out_len <> 0sz
     then EngineApplicationData
     else if resp.CT.network_out_len <> 0sz
     then EngineNetworkOutput
     else EngineProgress)

noextract
let engine_network_result_matches
  (result:engine_step_result)
  (buffer_resp:CT.client_buffer_response)
  : prop =
  result.engine_step_status == buffer_resp.CT.response.CT.status /\
  result.engine_step_consumed_len == buffer_resp.CT.consumed_len /\
  result.engine_step_network_out_len ==
    buffer_resp.CT.response.CT.network_out_len /\
  result.engine_step_app_out_len ==
    buffer_resp.CT.response.CT.app_out_len /\
  result.engine_step_action ==
    (if buffer_resp.CT.response.CT.status == CT.NeedMoreInput
     then EngineNeedNetworkInput
     else if buffer_resp.CT.response.CT.status <> CT.StepOk
     then EngineFailed
     else if buffer_resp.CT.response.CT.app_out_len <> 0sz
     then EngineApplicationData
     else if buffer_resp.CT.response.CT.network_out_len <> 0sz
     then EngineNetworkOutput
     else EngineProgress)

noextract
let engine_local_step_correct
  (st0 st1:CS.connection_state)
  (result:engine_step_result)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists resp.
    CT.local_event_end_to_end_correct
      st0 st1 resp kind payload network_out app_out /\
    engine_local_result_matches result resp /\
    engine_result_buffers_wf result network_out app_out

noextract
let engine_network_step_correct
  (st0 st1:CS.connection_state)
  (result:engine_step_result)
  (network_input:B.bytes)
  (old_network_out network_out:B.bytes)
  (old_app_out app_out:B.bytes)
  : prop =
  exists buffer_resp.
    CT.coalesced_network_bytes_end_to_end_correct
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out /\
    engine_network_result_matches result buffer_resp /\
    engine_result_buffers_wf result network_out app_out /\
    SZ.v result.engine_step_consumed_len <= B.length network_input

fn new_engine
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_context:array U8.t)
  (trust_context_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_context 'trust_context_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_context_bytes == SZ.v trust_context_len /\
                 SZ.v server_name_len <= Bounds.max_hostname_len /\
                 SZ.v trust_context_len <= Bounds.max_trust_anchors_len)
  returns e:client_engine
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_context 'trust_context_bytes **
          engine_live
            e
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_context_bytes)
              validation_time_seconds)

fn poll
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_result_buffers_wf result network_out_bytes app_out_bytes /\
                (result.engine_step_action ==
                   EngineNeedCertificateVerification ==>
                 engine_waiting_for_certificate st1) /\
                (result.engine_step_action ==
                   EngineNeedCertificateSignatureVerification ==>
                 engine_waiting_for_certificate_signature st1) /\
                (result.engine_step_action == EngineReady ==>
                 st1.CS.cs_model.CS.model_control ==
                   CS.ControlApplicationData /\
                 ~(D.internal_pending st1)))

fn feed_network
  (e:client_engine)
  (network_input:array U8.t)
  (network_input_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_input 'network_input_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'network_input_bytes == SZ.v network_input_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_input 'network_input_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_network_step_correct
                  'st0
                  st1
                  result
                  (Ghost.reveal 'network_input_bytes)
                  'old_network_out
                  network_out_bytes
                  'old_app_out
                  app_out_bytes)

fn copy_certificate_chain
  (e:client_engine)
  (chain_out:array U8.t)
  (chain_out_len:SZ.t)
  (offsets_out:array SZ.t)
  (offsets_out_len:SZ.t)
  (lens_out:array SZ.t)
  (lens_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to chain_out 'old_chain_out **
           pts_to offsets_out 'old_offsets_out **
           pts_to lens_out 'old_lens_out **
           pure (B.length 'old_chain_out == SZ.v chain_out_len /\
                 Seq.length 'old_offsets_out == SZ.v offsets_out_len /\
                 Seq.length 'old_lens_out == SZ.v lens_out_len /\
                 chain_out_len == engine_certificate_chain_capacity /\
                 offsets_out_len == engine_certificate_chain_entries /\
                 lens_out_len == engine_certificate_chain_entries /\
                 engine_waiting_for_certificate 'st0)
  returns snapshot:CR.certificate_chain_snapshot
  ensures exists* chain_bytes offsets lens.
          engine_live e 'st0 **
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

fn copy_certificate_verify_request
  (e:client_engine)
  (input_out:array U8.t)
  (input_out_len:SZ.t)
  (signature_out:array U8.t)
  (signature_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to input_out 'old_input_out **
           pts_to signature_out 'old_signature_out **
           pure (B.length 'old_input_out == SZ.v input_out_len /\
                 B.length 'old_signature_out == SZ.v signature_out_len /\
                 input_out_len == engine_certificate_verify_input_capacity /\
                 signature_out_len == engine_signature_capacity /\
                 engine_waiting_for_certificate_signature 'st0)
  returns request:certificate_verify_request
  ensures exists* input_bytes signature_bytes.
          engine_live e 'st0 **
          pts_to input_out input_bytes **
          pts_to signature_out signature_bytes **
          pure (B.length input_bytes == SZ.v input_out_len /\
                B.length signature_bytes == SZ.v signature_out_len /\
                SZ.v request.certificate_verify_input_len <=
                  B.length input_bytes /\
                SZ.v request.certificate_verify_signature_len <=
                  B.length signature_bytes /\
                (match
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input,
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify
                 with
                 | Some input, Some cv ->
                   B.length input <= B.length input_bytes /\
                   Seq.equal
                     (Seq.slice input_bytes 0 (B.length input))
                     input /\
                   L.signature_scheme_matches
                     request.certificate_verify_signature_scheme
                     (Sem.certificateVerify_scheme cv) /\
                   SZ.v request.certificate_verify_input_len ==
                     B.length input /\
                   SZ.v request.certificate_verify_signature_len ==
                     B.length (Sem.certificateVerify_signature_bytes cv) /\
                   Seq.equal
                     (Seq.slice
                       signature_bytes
                       0
                       (SZ.v request.certificate_verify_signature_len))
                     (Sem.certificateVerify_signature_bytes cv)
                 | _, _ -> False))

fn complete_certificate_verification
  (e:client_engine)
  (public_key:array U8.t)
  (public_key_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to public_key 'public_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'public_key_bytes == SZ.v public_key_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v public_key_len <= Bounds.max_public_key_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 engine_external_certificate_validation
                   'st0
                   (Ghost.reveal 'public_key_bytes))
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to public_key 'public_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalValidateCertificate
                  (Ghost.reveal 'public_key_bytes)
                  network_out_bytes
                  app_out_bytes)

fn complete_certificate_signature_verification
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 engine_external_signature_validation 'st0)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalVerifyCertificateSignature
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn send_application_data
  (e:client_engine)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v payload_len <= 16384 /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn send_close_notify
  (e:client_engine)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires engine_live e 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v engine_network_out_capacity <= SZ.v network_out_len /\
                 SZ.v engine_app_out_capacity <= SZ.v app_out_len /\
                 CT.local_input_wf 'st0 CT.LocalSendCloseNotify B.empty)
  returns result:engine_step_result
  ensures exists* st1 network_out_bytes app_out_bytes.
          engine_live e st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                engine_local_step_correct
                  'st0
                  st1
                  result
                  CT.LocalSendCloseNotify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn free_engine
  (e:client_engine)
  requires engine_live e 'st0
  ensures engine_released e 'st0
