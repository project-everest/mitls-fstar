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
module CN = TLS13.Impl.ConnectionState.Network
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
module SC = TLS13.Impl.Serializer.Common
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module Trace = TLS13.Trace
module U8 = FStar.UInt8
module U64 = FStar.UInt64
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

let lemma_legal_protected_handshake_head
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
     (requires
       model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       step.CS.protected_handshake_buffering == false /\
       step.CS.protected_handshake_offset == 0 /\
       step.CS.protected_handshake_head /\
       0 < step.CS.protected_handshake_consumed /\
       step.CS.protected_handshake_consumed <=
         B.length step.CS.protected_handshake_fragment /\
       CS.protected_handshake_message_supported
         step.CS.protected_handshake_message /\
       WS.parse_handshake step.CS.protected_handshake_fragment ==
         Some
           (step.CS.protected_handshake_message,
            step.CS.protected_handshake_consumed) /\
       CS.legal_handshake_message
         model
         TLS13.ConnectionLog.Received
         step.CS.protected_handshake_message /\
       CS.protected_handshake_buffer_empty model)
     (ensures
       CS.legal_event model (CS.ConnProtectedHandshake step))
=
  assert (Seq.slice
    step.CS.protected_handshake_fragment
    0
    (B.length step.CS.protected_handshake_fragment) ==
     step.CS.protected_handshake_fragment)

let lemma_legal_protected_handshake_drain
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
     (requires
       model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       step.CS.protected_handshake_buffering == false /\
       step.CS.protected_handshake_head == false /\
       Seq.equal
         step.CS.protected_handshake_fragment
         model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes /\
       step.CS.protected_handshake_offset ==
         model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed /\
       0 < step.CS.protected_handshake_consumed /\
       step.CS.protected_handshake_offset +
         step.CS.protected_handshake_consumed <=
           B.length step.CS.protected_handshake_fragment /\
       CS.protected_handshake_message_supported
         step.CS.protected_handshake_message /\
       WS.parse_handshake
         (Seq.slice
           step.CS.protected_handshake_fragment
           step.CS.protected_handshake_offset
           (B.length step.CS.protected_handshake_fragment)) ==
         Some
           (step.CS.protected_handshake_message,
            step.CS.protected_handshake_consumed) /\
       CS.legal_handshake_message
         model
         TLS13.ConnectionLog.Received
         step.CS.protected_handshake_message)
     (ensures
       CS.legal_event model (CS.ConnProtectedHandshake step))
=
  assert (step.CS.protected_handshake_offset <
    B.length step.CS.protected_handshake_fragment)

let lemma_legal_protected_handshake_buffer
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
     (requires
       model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       step.CS.protected_handshake_buffering == true /\
       step.CS.protected_handshake_head == true /\
       step.CS.protected_handshake_offset == 0 /\
       step.CS.protected_handshake_consumed == 0 /\
       0 < B.length step.CS.protected_handshake_fragment /\
       B.length (CS.protected_handshake_stream model step) <=
         CS.max_pending_protected_handshake /\
       (match model.CS.model_control with
        | CS.ControlHandshaking stage -> CS.protected_handshake_buffering_stage stage
        | _ -> False) /\
       (~ (CS.protected_handshake_buffer_empty model) \/
        WS.parse_handshake step.CS.protected_handshake_fragment == None))
     (ensures
       CS.legal_event model (CS.ConnProtectedHandshake step))
= ()

(* [copy_pending_protected_handshake] reports [None] precisely when the
   pending buffer's plaintext has all been parsed already (parsed >= length);
   in that case the leftover carried forward by a subsequent buffering step
   is empty, whether the buffer's length and parsed offset happen to coincide
   or the offset has run past it. *)
let lemma_pending_protected_handshake_leftover_empty
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed >=
          B.length
            model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes)
      (ensures
        Seq.equal
          (CS.pending_protected_handshake_leftover model)
          B.empty)
=
  let bufs = model.CS.model_handshake.CS.hs_buffers in
  let bytes = bufs.CS.hb_encrypted_server_handshake_bytes in
  let parsed = bufs.CS.hb_encrypted_server_handshake_parsed in
  if parsed <= B.length bytes
  then Seq.lemma_len_slice bytes parsed (B.length bytes)
  else ()

fn try_process_protected_handshake_head
  (c:client)
  (content_type:U8.t)
  (parsed:L.tls_message)
  (consumed:SZ.t)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (message_fragment:array U8.t)
  (protected_fragment:array U8.t)
  (protected_fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
          (exists* msg.
            L.is_valid_tls_message parsed (M.TlsHandshake msg) **
            pure (
              CT.parsed_message_wire_success_for
                0x16uy
                (Ghost.reveal 'message_fragment_bytes)
                parsed
                (M.TlsHandshake msg) /\
              WS.parse_handshake
                (Ghost.reveal 'protected_fragment_bytes) ==
                  Some (msg, SZ.v consumed))) **
          pts_to raw 'raw_bytes **
          pts_to message_fragment 'message_fragment_bytes **
          pts_to protected_fragment 'protected_fragment_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (
            B.length 'raw_bytes == SZ.v raw_len /\
            B.length 'message_fragment_bytes == SZ.v consumed /\
            B.length 'protected_fragment_bytes ==
              SZ.v protected_fragment_len /\
            B.length 'old_network_out == SZ.v network_out_len /\
            B.length 'old_app_out == SZ.v app_out_len /\
            0 < SZ.v consumed /\
            SZ.v protected_fragment_len <= Bounds.max_handshake_flight_len /\
            SZ.v consumed <= SZ.v protected_fragment_len /\
            CT.protected_decoder_fragment_relation
              'st0
              content_type
              (Ghost.reveal 'protected_fragment_bytes)
              (Ghost.reveal 'raw_bytes) /\
            (exists outer_fragment.
              WS.parse_record (Ghost.reveal 'raw_bytes) ==
                Some
                  (T.Application_data,
                   outer_fragment,
                   B.length (Ghost.reveal 'raw_bytes))) /\
            L.content_type_matches content_type T.Handshake)
  returns handled:option CT.client_response
  ensures
    (match handled with
    | None ->
      CR.connection_exactly c 'st0 **
      (exists* msg.
        L.is_valid_tls_message parsed (M.TlsHandshake msg)) **
      pts_to raw 'raw_bytes **
      pts_to message_fragment 'message_fragment_bytes **
      pts_to protected_fragment 'protected_fragment_bytes **
      pts_to network_out 'old_network_out **
      pts_to app_out 'old_app_out
    | Some resp ->
      exists* st1.
        CR.connection_exactly c st1 **
        pts_to raw 'raw_bytes **
        pts_to message_fragment 'message_fragment_bytes **
        pts_to protected_fragment 'protected_fragment_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          (exists step.
            CT.protected_handshake_step_correct
              'st0
              st1
              resp
              step
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out) /\
          (CT.client_end_to_end_invariant 'st0 ==>
           CT.client_end_to_end_invariant st1)))
{
  Trace.emit Trace.client_protected_head
    (SZ.sizet_to_uint64 consumed)
    (SZ.sizet_to_uint64 protected_fragment_len)
    (SZ.sizet_to_uint64 raw_len);
  with msg. assert (
    L.is_valid_tls_message parsed (M.TlsHandshake msg));
  let protected_buffer_empty =
    CQ.protected_handshake_buffer_empty_runtime c;
  if protected_buffer_empty {
   match parsed {
    L.LTlsHandshake lhs -> {
     unfold
       (L.is_valid_tls_message
         (L.LTlsHandshake lhs)
         (M.TlsHandshake msg));
     assert (L.is_valid_handshake_msg lhs msg);
     match lhs {
       L.LEncryptedExtensions lee -> {
         unfold (L.is_valid_handshake_msg (L.LEncryptedExtensions lee) msg);
         with ee. _;
         assert (pure (msg == M.EncryptedExtensions ee));
         assert (pure (CT.parsed_message_wire_success_for
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (L.LTlsHandshake (L.LEncryptedExtensions lee))
           (M.TlsHandshake (M.EncryptedExtensions ee))));
         assert (pure (CT.wire_parse_success
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (M.TlsHandshake (M.EncryptedExtensions ee))));
         assert (pure (Seq.equal
           (Ghost.reveal 'message_fragment_bytes)
           (WS.serialize_handshake (M.EncryptedExtensions ee))));
         let ready =
           CQ.can_receive_encrypted_extensions c #ee consumed;
         if ready {
           let step = Ghost.hide {
             CS.protected_handshake_message = M.EncryptedExtensions ee;
             CS.protected_handshake_fragment =
               Ghost.reveal 'protected_fragment_bytes;
             CS.protected_handshake_offset = 0;
             CS.protected_handshake_consumed = SZ.v consumed;
             CS.protected_handshake_head = true;
             CS.protected_handshake_buffering = false;
           };
           CT.lemma_protected_head_decoder_projection
             'st0
             content_type
             (Ghost.reveal 'protected_fragment_bytes)
             (Ghost.reveal 'raw_bytes)
             (Ghost.reveal step);
           assert (pure (CS.legal_handshake_message
             'st0.CS.cs_model
             TLS13.ConnectionLog.Received
             (M.EncryptedExtensions ee)));
           assert (pure (WS.parse_handshake
             (Ghost.reveal 'protected_fragment_bytes) ==
               Some (M.EncryptedExtensions ee, SZ.v consumed)));
           assert (pure (CS.protected_handshake_buffer_empty
             'st0.CS.cs_model));
           assert (pure (CS.protected_handshake_message_supported
             (M.EncryptedExtensions ee)));
           assert (pure (0 < SZ.v consumed));
           assert (pure (SZ.v consumed <=
             B.length (Ghost.reveal 'protected_fragment_bytes)));
           lemma_legal_protected_handshake_head
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.legal_event
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))));
           CT.lemma_legal_protected_handshake_step_some
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.event_raw_delta_legal
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))
             B.empty
             (Ghost.reveal 'raw_bytes)));
           CN.mark_received_protected_encrypted_extensions
             c
             raw
             message_fragment
             consumed
             protected_fragment
             protected_fragment_len
             lee
             #ee
             #step;
           let resp = {
             CT.network_out_len = 0sz;
             CT.app_out_len = 0sz;
             CT.status = CT.StepOk;
           };
           CT.lemma_protected_handshake_step_correct_intro
             'st0
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
             'st0
             (CM.protected_handshake_state
               'st0
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes))
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           assert (pure (
             CT.protected_handshake_step_correct
               'st0
               (CM.protected_handshake_state
                 'st0
                 (Ghost.reveal step)
                 (Ghost.reveal 'raw_bytes))
               resp
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes)
               'old_network_out
               'old_app_out /\
             (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant
                (CM.protected_handshake_state
                  'st0
                  (Ghost.reveal step)
                  (Ghost.reveal 'raw_bytes)))));
           Some resp
         } else {
           fold
             (L.is_valid_handshake_msg
               (L.LEncryptedExtensions lee)
               (M.EncryptedExtensions ee));
           fold
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LEncryptedExtensions lee))
               (M.TlsHandshake (M.EncryptedExtensions ee)));
           rewrite
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LEncryptedExtensions lee))
               (M.TlsHandshake (M.EncryptedExtensions ee)))
             as
             (L.is_valid_tls_message
               parsed
               (M.TlsHandshake (M.EncryptedExtensions ee)));
           None #CT.client_response
         }
       }
       L.LCertificate lcert -> {
         unfold (L.is_valid_handshake_msg (L.LCertificate lcert) msg);
         with cert. _;
         assert (pure (msg == M.Certificate cert));
         assert (pure (CT.parsed_message_wire_success_for
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (L.LTlsHandshake (L.LCertificate lcert))
           (M.TlsHandshake (M.Certificate cert))));
         assert (pure (CT.wire_parse_success
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (M.TlsHandshake (M.Certificate cert))));
         assert (pure (Seq.equal
           (Ghost.reveal 'message_fragment_bytes)
           (WS.serialize_handshake (M.Certificate cert))));
         let ready =
           CQ.can_receive_certificate c lcert #cert consumed;
         if ready {
           let step = Ghost.hide {
             CS.protected_handshake_message = M.Certificate cert;
             CS.protected_handshake_fragment =
               Ghost.reveal 'protected_fragment_bytes;
             CS.protected_handshake_offset = 0;
             CS.protected_handshake_consumed = SZ.v consumed;
             CS.protected_handshake_head = true;
             CS.protected_handshake_buffering = false;
           };
           CT.lemma_protected_head_decoder_projection
             'st0
             content_type
             (Ghost.reveal 'protected_fragment_bytes)
             (Ghost.reveal 'raw_bytes)
             (Ghost.reveal step);
           assert (pure (CS.legal_handshake_message
             'st0.CS.cs_model
             TLS13.ConnectionLog.Received
             (M.Certificate cert)));
           assert (pure (WS.parse_handshake
             (Ghost.reveal 'protected_fragment_bytes) ==
               Some (M.Certificate cert, SZ.v consumed)));
           assert (pure (CS.protected_handshake_buffer_empty
             'st0.CS.cs_model));
           assert (pure (CS.protected_handshake_message_supported
             (M.Certificate cert)));
           assert (pure (0 < SZ.v consumed));
           assert (pure (SZ.v consumed <=
             B.length (Ghost.reveal 'protected_fragment_bytes)));
           lemma_legal_protected_handshake_head
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.legal_event
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))));
           CT.lemma_legal_protected_handshake_step_some
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.event_raw_delta_legal
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))
             B.empty
             (Ghost.reveal 'raw_bytes)));
           CN.mark_received_protected_certificate_head
             c
             raw
             message_fragment
             consumed
             protected_fragment
             protected_fragment_len
             lcert
             #cert
             #step;
           let resp = {
             CT.network_out_len = 0sz;
             CT.app_out_len = 0sz;
             CT.status = CT.StepOk;
           };
           CT.lemma_protected_handshake_step_correct_intro
             'st0
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
             'st0
             (CM.protected_handshake_state
               'st0
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes))
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           assert (pure (
             CT.protected_handshake_step_correct
               'st0
               (CM.protected_handshake_state
                 'st0
                 (Ghost.reveal step)
                 (Ghost.reveal 'raw_bytes))
               resp
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes)
               'old_network_out
               'old_app_out /\
             (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant
                (CM.protected_handshake_state
                  'st0
                  (Ghost.reveal step)
                  (Ghost.reveal 'raw_bytes)))));
           Some resp
         } else {
           fold
             (L.is_valid_handshake_msg
               (L.LCertificate lcert)
               (M.Certificate cert));
           fold
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LCertificate lcert))
               (M.TlsHandshake (M.Certificate cert)));
           rewrite
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LCertificate lcert))
               (M.TlsHandshake (M.Certificate cert)))
             as
             (L.is_valid_tls_message
               parsed
               (M.TlsHandshake (M.Certificate cert)));
           None #CT.client_response
         }
       }
       L.LCertificateVerify lcv -> {
         unfold
           (L.is_valid_handshake_msg
             (L.LCertificateVerify lcv)
             msg);
         with cv. _;
         assert (pure (msg == M.CertificateVerify cv));
         assert (pure (CT.parsed_message_wire_success_for
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (L.LTlsHandshake (L.LCertificateVerify lcv))
           (M.TlsHandshake (M.CertificateVerify cv))));
         assert (pure (CT.wire_parse_success
           0x16uy
           (Ghost.reveal 'message_fragment_bytes)
           (M.TlsHandshake (M.CertificateVerify cv))));
         assert (pure (Seq.equal
           (Ghost.reveal 'message_fragment_bytes)
           (WS.serialize_handshake (M.CertificateVerify cv))));
         let ready =
           CQ.can_receive_certificate_verify c #cv consumed;
         if ready {
           let step = Ghost.hide {
             CS.protected_handshake_message = M.CertificateVerify cv;
             CS.protected_handshake_fragment =
               Ghost.reveal 'protected_fragment_bytes;
             CS.protected_handshake_offset = 0;
             CS.protected_handshake_consumed = SZ.v consumed;
             CS.protected_handshake_head = true;
             CS.protected_handshake_buffering = false;
           };
           CT.lemma_protected_head_decoder_projection
             'st0
             content_type
             (Ghost.reveal 'protected_fragment_bytes)
             (Ghost.reveal 'raw_bytes)
             (Ghost.reveal step);
           assert (pure (CS.legal_handshake_message
             'st0.CS.cs_model
             TLS13.ConnectionLog.Received
             (M.CertificateVerify cv)));
           assert (pure (WS.parse_handshake
             (Ghost.reveal 'protected_fragment_bytes) ==
               Some (M.CertificateVerify cv, SZ.v consumed)));
           assert (pure (CS.protected_handshake_buffer_empty
             'st0.CS.cs_model));
           assert (pure (CS.protected_handshake_message_supported
             (M.CertificateVerify cv)));
           assert (pure (0 < SZ.v consumed));
           assert (pure (SZ.v consumed <=
             B.length (Ghost.reveal 'protected_fragment_bytes)));
           lemma_legal_protected_handshake_head
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.legal_event
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))));
           CT.lemma_legal_protected_handshake_step_some
             'st0.CS.cs_model
             (Ghost.reveal step);
           assert (pure (CS.event_raw_delta_legal
             'st0.CS.cs_model
             (CS.ConnProtectedHandshake (Ghost.reveal step))
             B.empty
             (Ghost.reveal 'raw_bytes)));
           CN.mark_received_protected_certificate_verify_head
             c
             raw
             message_fragment
             consumed
             protected_fragment
             protected_fragment_len
             lcv
             #cv
             #step;
           let resp = {
             CT.network_out_len = 0sz;
             CT.app_out_len = 0sz;
             CT.status = CT.StepOk;
           };
           CT.lemma_protected_handshake_step_correct_intro
             'st0
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
             'st0
             (CM.protected_handshake_state
               'st0
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes))
             resp
             (Ghost.reveal step)
             (Ghost.reveal 'raw_bytes)
             'old_network_out
             'old_app_out;
           assert (pure (
             CT.protected_handshake_step_correct
               'st0
               (CM.protected_handshake_state
                 'st0
                 (Ghost.reveal step)
                 (Ghost.reveal 'raw_bytes))
               resp
               (Ghost.reveal step)
               (Ghost.reveal 'raw_bytes)
               'old_network_out
               'old_app_out /\
             (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant
                (CM.protected_handshake_state
                  'st0
                  (Ghost.reveal step)
                  (Ghost.reveal 'raw_bytes)))));
           Some resp
         } else {
           fold
             (L.is_valid_handshake_msg
               (L.LCertificateVerify lcv)
               (M.CertificateVerify cv));
           fold
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LCertificateVerify lcv))
               (M.TlsHandshake (M.CertificateVerify cv)));
           rewrite
             (L.is_valid_tls_message
               (L.LTlsHandshake (L.LCertificateVerify lcv))
               (M.TlsHandshake (M.CertificateVerify cv)))
             as
             (L.is_valid_tls_message
               parsed
               (M.TlsHandshake (M.CertificateVerify cv)));
           None #CT.client_response
         }
       }
       lhs_other -> {
         fold (L.is_valid_tls_message
           (L.LTlsHandshake lhs_other)
           (M.TlsHandshake msg));
         rewrite
           (L.is_valid_tls_message
             (L.LTlsHandshake lhs_other)
             (M.TlsHandshake msg))
           as
           (L.is_valid_tls_message parsed (M.TlsHandshake msg));
         None #CT.client_response
       }
     }
    }
    parsed_other -> {
     with msg. assert (
       L.is_valid_tls_message parsed_other (M.TlsHandshake msg));
     rewrite
       (L.is_valid_tls_message parsed_other (M.TlsHandshake msg))
       as
       (L.is_valid_tls_message parsed (M.TlsHandshake msg));
     None #CT.client_response
    }
   }
  } else {
    None #CT.client_response
  }
}

(* A record whose plaintext cannot supply a whole message is not an error --
   this is exactly what happens when a server splits a handshake message
   across records.  Instead of rejecting it, append it to the connection's
   pending protected-handshake buffer so a later record can complete the
   message.  There is no message to deliver and hence nothing written to
   [network_out]/[app_out]; both stay untouched on every path, mirroring
   [try_process_protected_handshake_head]'s output shape so callers thread
   the same arguments through unchanged. *)
fn try_buffer_protected_handshake_record
  (c:client)
  (content_type:U8.t)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (protected_fragment:array U8.t)
  (protected_fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to protected_fragment 'protected_fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (
             B.length 'raw_bytes == SZ.v raw_len /\
             B.length 'protected_fragment_bytes == SZ.v protected_fragment_len /\
             B.length 'old_network_out == SZ.v network_out_len /\
             B.length 'old_app_out == SZ.v app_out_len /\
             SZ.v protected_fragment_len <= Bounds.max_handshake_flight_len /\
             CT.protected_decoder_fragment_relation
               'st0
               content_type
               (Ghost.reveal 'protected_fragment_bytes)
               (Ghost.reveal 'raw_bytes) /\
             (exists outer_fragment.
               WS.parse_record (Ghost.reveal 'raw_bytes) ==
                 Some
                   (T.Application_data,
                    outer_fragment,
                    B.length (Ghost.reveal 'raw_bytes))) /\
             L.content_type_matches content_type T.Handshake)
  returns handled:option CT.client_response
  ensures
    (match handled with
    | None ->
      CR.connection_exactly c 'st0 **
      pts_to raw 'raw_bytes **
      pts_to protected_fragment 'protected_fragment_bytes **
      pts_to network_out 'old_network_out **
      pts_to app_out 'old_app_out
    | Some resp ->
      exists* st1.
        CR.connection_exactly c st1 **
        pts_to raw 'raw_bytes **
        pts_to protected_fragment 'protected_fragment_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          (exists step.
            CT.protected_handshake_step_correct
              'st0
              st1
              resp
              step
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out) /\
          (CT.client_end_to_end_invariant 'st0 ==>
           CT.client_end_to_end_invariant st1)))
{
  let ok = CQ.can_buffer_protected_handshake c;
  if (not ok) {
    None #CT.client_response
  } else if (SZ.eq protected_fragment_len 0sz) {
    None #CT.client_response
  } else {
    let pending = CQ.copy_pending_protected_handshake c;
    match pending {
      None -> {
        lemma_pending_protected_handshake_leftover_empty 'st0.CS.cs_model;
        (* Buffering with an already-empty pending buffer is a last resort:
           legal only when this record's own plaintext does not already
           parse as a complete handshake message, since otherwise the head
           path would be the one to deliver it. *)
        let absent = P.handshake_prefix_absent protected_fragment protected_fragment_len;
        if (not absent) {
          None #CT.client_response
        } else {
        let stream_len = protected_fragment_len;
        let stream = V.alloc 0uy stream_len;
        V.to_array_pts_to stream;
        SC.copy_array_slice_to_array
          protected_fragment protected_fragment_len 0sz protected_fragment_len
          (V.vec_to_array stream) stream_len 0sz;
        with stream_bytes. assert (pts_to (V.vec_to_array stream) stream_bytes);
        assert (pure (Seq.equal
          stream_bytes
          (Ghost.reveal 'protected_fragment_bytes)));

        let step = Ghost.hide {
          CS.protected_handshake_message = M.HelloRetryRequest;
          CS.protected_handshake_fragment = Ghost.reveal 'protected_fragment_bytes;
          CS.protected_handshake_offset = 0;
          CS.protected_handshake_consumed = 0;
          CS.protected_handshake_head = true;
          CS.protected_handshake_buffering = true;
        };
        assert (pure (Seq.equal
          stream_bytes
          (CS.protected_handshake_stream 'st0.CS.cs_model (Ghost.reveal step))));
        assert (pure (
          WS.parse_handshake (Ghost.reveal step).CS.protected_handshake_fragment ==
            None));

        lemma_legal_protected_handshake_buffer
          'st0.CS.cs_model
          (Ghost.reveal step);
        CT.lemma_protected_buffer_decoder_projection
          'st0
          content_type
          (Ghost.reveal 'protected_fragment_bytes)
          (Ghost.reveal 'raw_bytes)
          (Ghost.reveal step);
        CT.lemma_legal_protected_handshake_step_some
          'st0.CS.cs_model
          (Ghost.reveal step);

        Trace.emit Trace.client_protected_buffer
          (SZ.sizet_to_uint64 stream_len)
          (SZ.sizet_to_uint64 protected_fragment_len)
          (SZ.sizet_to_uint64 raw_len);
        CN.buffer_protected_handshake_record
          c raw (V.vec_to_array stream) stream_len #step;

        V.to_vec_pts_to stream;
        V.free stream;

        let resp = {
          CT.network_out_len = 0sz;
          CT.app_out_len = 0sz;
          CT.status = CT.StepOk;
        };
        CT.lemma_protected_handshake_step_correct_intro
          'st0
          resp
          (Ghost.reveal step)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          'old_app_out;
        CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
          'st0
          (CM.protected_handshake_state
            'st0
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes))
          resp
          (Ghost.reveal step)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          'old_app_out;
        Some resp
        }
      }
      Some pending -> {
        with pending_fragment_bytes. assert (
          V.pts_to pending.pending_protected_fragment pending_fragment_bytes);
        let leftover_len =
          SZ.sub
            pending.pending_protected_fragment_len
            pending.pending_protected_parsed;
        let room = SZ.sub Bounds.max_handshake_flight_len_sz leftover_len;
        let fits_check = SZ.lte protected_fragment_len room;
        if (not fits_check) {
          V.free pending.pending_protected_fragment;
          None #CT.client_response
        } else {
          let stream_len = SZ.add leftover_len protected_fragment_len;
          let stream = V.alloc 0uy stream_len;
          V.to_array_pts_to stream;
          V.to_array_pts_to pending.pending_protected_fragment;
          SC.copy_array_slice_to_array
            (V.vec_to_array pending.pending_protected_fragment)
            pending.pending_protected_fragment_len
            pending.pending_protected_parsed
            leftover_len
            (V.vec_to_array stream)
            stream_len
            0sz;
          SC.copy_array_slice_to_array
            protected_fragment
            protected_fragment_len
            0sz
            protected_fragment_len
            (V.vec_to_array stream)
            stream_len
            leftover_len;
          V.to_vec_pts_to pending.pending_protected_fragment;
          V.free pending.pending_protected_fragment;

          with stream_bytes. assert (pts_to (V.vec_to_array stream) stream_bytes);
          assert (pure (Seq.equal
            stream_bytes
            (Seq.append
              (Seq.slice
                pending_fragment_bytes
                (SZ.v pending.pending_protected_parsed)
                (SZ.v pending.pending_protected_fragment_len))
              (Ghost.reveal 'protected_fragment_bytes))));

          let step = Ghost.hide {
            CS.protected_handshake_message = M.HelloRetryRequest;
            CS.protected_handshake_fragment = Ghost.reveal 'protected_fragment_bytes;
            CS.protected_handshake_offset = 0;
            CS.protected_handshake_consumed = 0;
            CS.protected_handshake_head = true;
            CS.protected_handshake_buffering = true;
          };
          assert (pure (Seq.equal
            stream_bytes
            (CS.protected_handshake_stream 'st0.CS.cs_model (Ghost.reveal step))));
          (* [pending_protected_parsed < pending_protected_fragment_len] means
             the pending buffer's plaintext is nonempty, which is the other
             half of the "buffering is a last resort" disjunct: a non-empty
             pending buffer already rules out the head rule regardless of
             what this record's own fragment parses as. *)
          assert (pure (~ (CS.protected_handshake_buffer_empty 'st0.CS.cs_model)));

          lemma_legal_protected_handshake_buffer
            'st0.CS.cs_model
            (Ghost.reveal step);
          CT.lemma_protected_buffer_decoder_projection
            'st0
            content_type
            (Ghost.reveal 'protected_fragment_bytes)
            (Ghost.reveal 'raw_bytes)
            (Ghost.reveal step);
          CT.lemma_legal_protected_handshake_step_some
            'st0.CS.cs_model
            (Ghost.reveal step);

          Trace.emit Trace.client_protected_buffer
            (SZ.sizet_to_uint64 stream_len)
            (SZ.sizet_to_uint64 protected_fragment_len)
            (SZ.sizet_to_uint64 raw_len);
          CN.buffer_protected_handshake_record
            c raw (V.vec_to_array stream) stream_len #step;

          V.to_vec_pts_to stream;
          V.free stream;

          let resp = {
            CT.network_out_len = 0sz;
            CT.app_out_len = 0sz;
            CT.status = CT.StepOk;
          };
          CT.lemma_protected_handshake_step_correct_intro
            'st0
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
            'st0
            (CM.protected_handshake_state
              'st0
              (Ghost.reveal step)
              (Ghost.reveal 'raw_bytes))
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          Some resp
        }
      }
    }
  }
}

(* G3: a CLEARTEXT record's raw bytes, viewed as a [ConnCleartextHandshake]
   delta.  Client twin of [TLS13.Impl.Server.Network.lemma_cleartext_record_raw_delta_legal]:
   the decoder leaves the outer content type existential and only says the
   dispatcher's [content_type] byte matches it, so pinning that byte to 0x16
   collapses the existential to [T.Handshake] -- in particular it rules out the
   [Application_data] arm, which is the protected reading. *)
let lemma_client_cleartext_record_raw_delta_legal
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        (exists outer_ct.
          L.content_type_matches content_type outer_ct /\
          WS.parse_record_wire raw_received ==
            Some (outer_ct, fragment, B.length raw_received)) /\
        L.content_type_matches content_type T.Handshake)
      (ensures
        WS.parse_record_wire raw_received ==
          Some (T.Handshake, fragment, B.length raw_received))
= ()

(** G3, client half: set a CLEARTEXT handshake record's fragment aside instead
    of rejecting it.

    The exact mirror of [TLS13.Impl.Server.Network.try_buffer_cleartext_handshake_record],
    and reached from the same place -- the record decoder's "this fragment
    parses as no message" arm -- because that is what a server splitting its
    ServerHello across records looks like from here.

    Returns [None], meaning "not my business, fall through to the decode error",
    when:
      - the record is not a cleartext handshake record (it is protected, or its
        content type is not 0x16);
      - the connection is not in a state that could ever drain the buffer (only
        a client that has sent its ClientHello and is awaiting a ServerHello
        qualifies), which [CQ.can_buffer_cleartext_handshake] decides;
      - the fragment is empty, so the step would make no progress and a peer
        could feed empty records forever;
      - the coalesced stream `pending ++ fragment` is longer than
        [max_client_hello_len], so it could never be completed into the one
        message this buffer can ever be drained by;
      - the coalesced stream already PARSES as a whole message.  Buffering it
        would be illegal (the model's last-resort conjunct) and pointless. *)
fn try_buffer_cleartext_handshake_record
  (c:client)
  (protected:bool)
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
           pure (
             B.length 'raw_bytes == SZ.v raw_len /\
             B.length 'fragment_bytes == SZ.v fragment_len /\
             B.length 'old_network_out == SZ.v network_out_len /\
             B.length 'old_app_out == SZ.v app_out_len /\
             SZ.v fragment_len <= Bounds.max_handshake_flight_len /\
             CT.client_end_to_end_invariant 'st0 /\
             (~protected ==>
               (exists outer_ct.
                 L.content_type_matches content_type outer_ct /\
                 WS.parse_record_wire (Ghost.reveal 'raw_bytes) ==
                   Some
                     (outer_ct,
                      Ghost.reveal 'fragment_bytes,
                      B.length (Ghost.reveal 'raw_bytes)))) /\
             (forall (ct:T.content_type).
               L.content_type_matches content_type ct ==>
               WS.parse_tls_message ct (Ghost.reveal 'fragment_bytes) == None))
  returns handled:option CT.client_response
  ensures
    (match handled with
    | None ->
      CR.connection_exactly c 'st0 **
      pts_to raw 'raw_bytes **
      pts_to fragment 'fragment_bytes **
      pts_to network_out 'old_network_out **
      pts_to app_out 'old_app_out
    | Some resp ->
      exists* st1.
        CR.connection_exactly c st1 **
        pts_to raw 'raw_bytes **
        pts_to fragment 'fragment_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          (exists step.
            st1 ==
              CM.cleartext_handshake_state
                'st0
                step
                (Ghost.reveal 'raw_bytes) /\
            CT.cleartext_handshake_step_correct
              'st0
              st1
              resp
              step
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out) /\
          (CT.client_end_to_end_invariant 'st0 ==>
           CT.client_end_to_end_invariant st1)))
{
  let is_cleartext_handshake = ((not protected) && content_type = 0x16uy);
  if (not is_cleartext_handshake) {
    None #CT.client_response
  } else if (SZ.eq fragment_len 0sz) {
    None #CT.client_response
  } else {
    let ok = CQ.can_buffer_cleartext_handshake c;
    if (not ok) {
      None #CT.client_response
    } else {
      let pending = CQ.copy_pending_cleartext_handshake c;
      match pending {
        Some p -> {
          with pending_bytes. assert (
            V.pts_to p.CR.pending_cleartext_fragment pending_bytes);
          (* The reassembly cap is [max_client_hello_len], not the model's
             [max_pending_cleartext_handshake].  A cleartext buffer can only
             ever be drained by a ServerHello here, which is bounded by it, so
             anything larger could never complete; capping also keeps the
             stream inside [parse_tls_message]'s record-fragment bound. *)
          let pending_fits =
            SZ.lte
              p.CR.pending_cleartext_fragment_len
              Bounds.max_client_hello_len_sz;
          if (not pending_fits) {
            V.free p.CR.pending_cleartext_fragment;
            None #CT.client_response
          } else {
            let room =
              SZ.sub
                Bounds.max_client_hello_len_sz
                p.CR.pending_cleartext_fragment_len;
            let fits = SZ.lte fragment_len room;
            if (not fits) {
              V.free p.CR.pending_cleartext_fragment;
              None #CT.client_response
            } else {
              let stream_len =
                SZ.add p.CR.pending_cleartext_fragment_len fragment_len;
              let stream = V.alloc 0uy stream_len;
              V.to_array_pts_to stream;
              V.to_array_pts_to p.CR.pending_cleartext_fragment;
              SC.copy_array_slice_to_array
                (V.vec_to_array p.CR.pending_cleartext_fragment)
                p.CR.pending_cleartext_fragment_len
                0sz
                p.CR.pending_cleartext_fragment_len
                (V.vec_to_array stream)
                stream_len
                0sz;
              SC.copy_array_slice_to_array
                fragment
                fragment_len
                0sz
                fragment_len
                (V.vec_to_array stream)
                stream_len
                p.CR.pending_cleartext_fragment_len;
              V.to_vec_pts_to p.CR.pending_cleartext_fragment;
              V.free p.CR.pending_cleartext_fragment;
              with stream_bytes. assert (
                pts_to (V.vec_to_array stream) stream_bytes);
              let step = Ghost.hide ({
                CS.cleartext_handshake_fragment = Ghost.reveal 'fragment_bytes;
              } <: CS.cleartext_handshake_step);
              assert (pure (Seq.equal
                (Ghost.reveal stream_bytes)
                (CS.cleartext_handshake_stream
                  'st0.CS.cs_model
                  (Ghost.reveal step))));
              (* THE coalescing decode: the combined stream, not this record's
                 fragment alone, is what has to fail to parse for buffering to
                 be a legal last resort. *)
              let coalesced =
                P.parse_tls_message
                  content_type
                  (V.vec_to_array stream)
                  stream_len;
              match coalesced {
                Some l -> {
                  (* The record COMPLETES a message.  Delivering a reassembled
                     ServerHello is the next increment; for now hand back to
                     the decode-error path rather than buffer a stream that
                     already parses, which the model forbids. *)
                  L.free_tls_message l;
                  V.to_vec_pts_to stream;
                  V.free stream;
                  None #CT.client_response
                }
                None -> {
                  assert (pure (L.content_type_matches content_type T.Handshake));
                  assert (pure (WS.parse_tls_message
                    T.Handshake
                    (CS.cleartext_handshake_stream
                      'st0.CS.cs_model
                      (Ghost.reveal step)) == None));
                  assert (pure (CS.legal_cleartext_handshake_step
                    'st0.CS.cs_model
                    (Ghost.reveal step)));
                  assert (pure (CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnCleartextHandshake (Ghost.reveal step))));
                  assert (pure (Some? (CS.step_cleartext_handshake
                    'st0.CS.cs_model
                    (Ghost.reveal step))));
                  lemma_client_cleartext_record_raw_delta_legal
                    content_type
                    (Ghost.reveal 'fragment_bytes)
                    (Ghost.reveal 'raw_bytes);
                  assert (pure (CS.event_raw_delta_legal
                    'st0.CS.cs_model
                    (CS.ConnCleartextHandshake (Ghost.reveal step))
                    B.empty
                    (Ghost.reveal 'raw_bytes)));

                  Trace.emit Trace.client_cleartext_buffer
                    (SZ.sizet_to_uint64 fragment_len)
                    (SZ.sizet_to_uint64 raw_len)
                    (SZ.sizet_to_uint64 stream_len);
                  CN.buffer_cleartext_handshake_record
                    c raw (V.vec_to_array stream) stream_len #step;
                  V.to_vec_pts_to stream;
                  V.free stream;

                  let resp = {
                    CT.network_out_len = 0sz;
                    CT.app_out_len = 0sz;
                    CT.status = CT.StepOk;
                  };
                  CT.lemma_cleartext_handshake_step_correct_intro
                    'st0
                    resp
                    (Ghost.reveal step)
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_app_out;
                  CT.lemma_cleartext_handshake_step_correct_preserves_end_to_end_invariant_conditional
                    'st0
                    (CM.cleartext_handshake_state
                      'st0
                      (Ghost.reveal step)
                      (Ghost.reveal 'raw_bytes))
                    resp
                    (Ghost.reveal step)
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_app_out;
                  Some resp
                }
              }
            }
          }
        }
        None -> {
          (* The buffer is empty, so the assembled stream is exactly this
             record's fragment -- which the decoder has just told us parses
             as no message at all, discharging the "last resort" conjunct. *)
          assert (pure (CS.cleartext_handshake_buffer_empty 'st0.CS.cs_model));
          let step = Ghost.hide ({
            CS.cleartext_handshake_fragment = Ghost.reveal 'fragment_bytes;
          } <: CS.cleartext_handshake_step);
          assert (pure (Seq.equal
            (CS.cleartext_handshake_stream 'st0.CS.cs_model (Ghost.reveal step))
            (Ghost.reveal 'fragment_bytes)));
          assert (pure (L.content_type_matches content_type T.Handshake));
          assert (pure (WS.parse_tls_message
            T.Handshake
            (CS.cleartext_handshake_stream 'st0.CS.cs_model (Ghost.reveal step)) == None));
          assert (pure (CS.legal_cleartext_handshake_step
            'st0.CS.cs_model
            (Ghost.reveal step)));
          assert (pure (CS.legal_event
            'st0.CS.cs_model
            (CS.ConnCleartextHandshake (Ghost.reveal step))));
          assert (pure (Some? (CS.step_cleartext_handshake
            'st0.CS.cs_model
            (Ghost.reveal step))));
          lemma_client_cleartext_record_raw_delta_legal
            content_type
            (Ghost.reveal 'fragment_bytes)
            (Ghost.reveal 'raw_bytes);
          assert (pure (CS.event_raw_delta_legal
            'st0.CS.cs_model
            (CS.ConnCleartextHandshake (Ghost.reveal step))
            B.empty
            (Ghost.reveal 'raw_bytes)));

          Trace.emit Trace.client_cleartext_buffer
            (SZ.sizet_to_uint64 fragment_len)
            (SZ.sizet_to_uint64 raw_len)
            0UL;
          CN.buffer_cleartext_handshake_record
            c raw fragment fragment_len #step;

          let resp = {
            CT.network_out_len = 0sz;
            CT.app_out_len = 0sz;
            CT.status = CT.StepOk;
          };
          CT.lemma_cleartext_handshake_step_correct_intro
            'st0
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          CT.lemma_cleartext_handshake_step_correct_preserves_end_to_end_invariant_conditional
            'st0
            (CM.cleartext_handshake_state
              'st0
              (Ghost.reveal step)
              (Ghost.reveal 'raw_bytes))
            resp
            (Ghost.reveal step)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
          Some resp
        }
      }
    }
  }
}

fn try_process_protected_handshake_drain
  (c:client)
  (parsed:L.tls_message)
  (consumed:SZ.t)
  (offset:SZ.t)
  (parsed_total:SZ.t)
  (empty:array U8.t)
  (message_fragment:array U8.t)
  (pending_fragment:array U8.t)
  (pending_fragment_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           (exists* msg.
             L.is_valid_tls_message parsed (M.TlsHandshake msg) **
             pure (
               CT.parsed_message_wire_success_for
                 0x16uy
                 (Ghost.reveal 'message_fragment_bytes)
                 parsed
                 (M.TlsHandshake msg) /\
               SZ.v offset <
                 B.length (Ghost.reveal 'pending_fragment_bytes) /\
               WS.parse_handshake
                 (Seq.slice
                   (Ghost.reveal 'pending_fragment_bytes)
                   (SZ.v offset)
                   (B.length (Ghost.reveal 'pending_fragment_bytes))) ==
                 Some (msg, SZ.v consumed))) **
           pts_to empty 'empty_bytes **
           pts_to message_fragment 'message_fragment_bytes **
           pts_to pending_fragment 'pending_fragment_bytes **
           pure (
             Seq.equal (Ghost.reveal 'empty_bytes) B.empty /\
             B.length 'message_fragment_bytes == SZ.v consumed /\
             B.length 'pending_fragment_bytes == SZ.v pending_fragment_len /\
             Seq.equal
               (Ghost.reveal 'pending_fragment_bytes)
               'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes /\
             SZ.v offset ==
               'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed /\
             0 < SZ.v consumed /\
             SZ.v offset + SZ.v consumed == SZ.v parsed_total /\
             SZ.v parsed_total <= SZ.v pending_fragment_len /\
             CT.client_end_to_end_invariant 'st0)
  returns handled:option CT.client_response
  ensures
    (match handled with
     | None ->
       CR.connection_exactly c 'st0 **
       (exists* msg.
         L.is_valid_tls_message parsed (M.TlsHandshake msg)) **
       pts_to empty 'empty_bytes **
       pts_to message_fragment 'message_fragment_bytes **
       pts_to pending_fragment 'pending_fragment_bytes
     | Some resp ->
       exists* st1.
         CR.connection_exactly c st1 **
         pts_to empty 'empty_bytes **
         pts_to message_fragment 'message_fragment_bytes **
         pts_to pending_fragment 'pending_fragment_bytes **
         pure (
           (exists step.
             CT.protected_handshake_step_correct
               'st0 st1 resp step B.empty B.empty B.empty) /\
           CT.client_end_to_end_invariant st1))
{
  Trace.emit Trace.client_protected_drain
    (SZ.sizet_to_uint64 offset)
    (SZ.sizet_to_uint64 consumed)
    (SZ.sizet_to_uint64 pending_fragment_len);
  with msg. assert (
    L.is_valid_tls_message parsed (M.TlsHandshake msg));
  match parsed {
    L.LTlsHandshake lhs -> {
      unfold
        (L.is_valid_tls_message
          (L.LTlsHandshake lhs)
          (M.TlsHandshake msg));
      assert (L.is_valid_handshake_msg lhs msg);
      match lhs {
        L.LCertificate lcert -> {
          unfold
            (L.is_valid_handshake_msg
              (L.LCertificate lcert)
              msg);
          with cert. _;
          assert (pure (msg == M.Certificate cert));
          assert (pure (CT.parsed_message_wire_success_for
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (L.LTlsHandshake (L.LCertificate lcert))
            (M.TlsHandshake (M.Certificate cert))));
          assert (pure (CT.wire_parse_success
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (M.TlsHandshake (M.Certificate cert))));
          assert (pure (Seq.equal
            (Ghost.reveal 'message_fragment_bytes)
            (WS.serialize_handshake (M.Certificate cert))));
          let ready = CQ.can_receive_certificate c lcert #cert consumed;
          if ready {
            let step = Ghost.hide {
              CS.protected_handshake_message = M.Certificate cert;
              CS.protected_handshake_fragment =
                Ghost.reveal 'pending_fragment_bytes;
              CS.protected_handshake_offset = SZ.v offset;
              CS.protected_handshake_consumed = SZ.v consumed;
              CS.protected_handshake_head = false;
              CS.protected_handshake_buffering = false;
            };
            assert (pure (CS.legal_handshake_message
              'st0.CS.cs_model
              TLS13.ConnectionLog.Received
              (M.Certificate cert)));
            assert (pure (CS.protected_handshake_message_supported
              (M.Certificate cert)));
            lemma_legal_protected_handshake_drain
              'st0.CS.cs_model
              (Ghost.reveal step);
            CT.lemma_legal_protected_handshake_step_some
              'st0.CS.cs_model
              (Ghost.reveal step);
            assert (pure (CS.event_raw_delta_legal
              'st0.CS.cs_model
              (CS.ConnProtectedHandshake (Ghost.reveal step))
              B.empty
              B.empty));
            CN.mark_received_protected_certificate_drain
              c
              empty
              message_fragment
              consumed
              parsed_total
              lcert
              #cert
              #step;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.StepOk;
            };
            CT.lemma_protected_handshake_step_correct_intro
              'st0
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant
              'st0
              (CM.protected_handshake_state
                'st0
                (Ghost.reveal step)
                B.empty)
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            Some resp
          } else {
            fold
              (L.is_valid_handshake_msg
                (L.LCertificate lcert)
                (M.Certificate cert));
            fold
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LCertificate lcert))
                (M.TlsHandshake (M.Certificate cert)));
            rewrite
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LCertificate lcert))
                (M.TlsHandshake (M.Certificate cert)))
              as
              (L.is_valid_tls_message
                parsed
                (M.TlsHandshake (M.Certificate cert)));
            None #CT.client_response
          }
        }
        L.LCertificateVerify lcv -> {
          unfold
            (L.is_valid_handshake_msg
              (L.LCertificateVerify lcv)
              msg);
          with cv. _;
          assert (pure (msg == M.CertificateVerify cv));
          assert (pure (CT.parsed_message_wire_success_for
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (L.LTlsHandshake (L.LCertificateVerify lcv))
            (M.TlsHandshake (M.CertificateVerify cv))));
          assert (pure (CT.wire_parse_success
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (M.TlsHandshake (M.CertificateVerify cv))));
          assert (pure (Seq.equal
            (Ghost.reveal 'message_fragment_bytes)
            (WS.serialize_handshake (M.CertificateVerify cv))));
          let ready =
            CQ.can_receive_certificate_verify c #cv consumed;
          if ready {
            let step = Ghost.hide {
              CS.protected_handshake_message = M.CertificateVerify cv;
              CS.protected_handshake_fragment =
                Ghost.reveal 'pending_fragment_bytes;
              CS.protected_handshake_offset = SZ.v offset;
              CS.protected_handshake_consumed = SZ.v consumed;
              CS.protected_handshake_head = false;
              CS.protected_handshake_buffering = false;
            };
            assert (pure (CS.legal_handshake_message
              'st0.CS.cs_model
              TLS13.ConnectionLog.Received
              (M.CertificateVerify cv)));
            assert (pure (CS.protected_handshake_message_supported
              (M.CertificateVerify cv)));
            lemma_legal_protected_handshake_drain
              'st0.CS.cs_model
              (Ghost.reveal step);
            CT.lemma_legal_protected_handshake_step_some
              'st0.CS.cs_model
              (Ghost.reveal step);
            assert (pure (CS.event_raw_delta_legal
              'st0.CS.cs_model
              (CS.ConnProtectedHandshake (Ghost.reveal step))
              B.empty
              B.empty));
            CN.mark_received_protected_certificate_verify_drain
              c
              empty
              message_fragment
              consumed
              parsed_total
              lcv
              #cv
              #step;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.StepOk;
            };
            CT.lemma_protected_handshake_step_correct_intro
              'st0
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant
              'st0
              (CM.protected_handshake_state
                'st0
                (Ghost.reveal step)
                B.empty)
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            Some resp
          } else {
            fold
              (L.is_valid_handshake_msg
                (L.LCertificateVerify lcv)
                (M.CertificateVerify cv));
            fold
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LCertificateVerify lcv))
                (M.TlsHandshake (M.CertificateVerify cv)));
            rewrite
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LCertificateVerify lcv))
                (M.TlsHandshake (M.CertificateVerify cv)))
              as
              (L.is_valid_tls_message
                parsed
                (M.TlsHandshake (M.CertificateVerify cv)));
            None #CT.client_response
          }
        }
        L.LFinished lfin -> {
          unfold
            (L.is_valid_handshake_msg
              (L.LFinished lfin)
              msg);
          with fin. _;
          assert (pure (msg == M.Finished fin));
          assert (pure (CT.parsed_message_wire_success_for
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (L.LTlsHandshake (L.LFinished lfin))
            (M.TlsHandshake (M.Finished fin))));
          assert (pure (CT.wire_parse_success
            0x16uy
            (Ghost.reveal 'message_fragment_bytes)
            (M.TlsHandshake (M.Finished fin))));
          assert (pure (Seq.equal
            (Ghost.reveal 'message_fragment_bytes)
            (WS.serialize_handshake (M.Finished fin))));
          let ready = CQ.can_receive_server_finished c #fin;
          if ready {
            let step = Ghost.hide {
              CS.protected_handshake_message = M.Finished fin;
              CS.protected_handshake_fragment =
                Ghost.reveal 'pending_fragment_bytes;
              CS.protected_handshake_offset = SZ.v offset;
              CS.protected_handshake_consumed = SZ.v consumed;
              CS.protected_handshake_head = false;
              CS.protected_handshake_buffering = false;
            };
            assert (pure (CS.legal_handshake_message
              'st0.CS.cs_model
              TLS13.ConnectionLog.Received
              (M.Finished fin)));
            assert (pure (CS.protected_handshake_message_supported
              (M.Finished fin)));
            lemma_legal_protected_handshake_drain
              'st0.CS.cs_model
              (Ghost.reveal step);
            CT.lemma_legal_protected_handshake_step_some
              'st0.CS.cs_model
              (Ghost.reveal step);
            assert (pure (CS.event_raw_delta_legal
              'st0.CS.cs_model
              (CS.ConnProtectedHandshake (Ghost.reveal step))
              B.empty
              B.empty));
            CN.mark_received_protected_server_finished_drain
              c
              empty
              message_fragment
              consumed
              parsed_total
              lfin
              #fin
              #step;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.StepOk;
            };
            CT.lemma_protected_handshake_step_correct_intro
              'st0
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant
              'st0
              (CM.protected_handshake_state
                'st0
                (Ghost.reveal step)
                B.empty)
              resp
              (Ghost.reveal step)
              B.empty
              B.empty
              B.empty;
            Some resp
          } else {
            fold
              (L.is_valid_handshake_msg
                (L.LFinished lfin)
                (M.Finished fin));
            fold
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LFinished lfin))
                (M.TlsHandshake (M.Finished fin)));
            rewrite
              (L.is_valid_tls_message
                (L.LTlsHandshake (L.LFinished lfin))
                (M.TlsHandshake (M.Finished fin)))
              as
              (L.is_valid_tls_message
                parsed
                (M.TlsHandshake (M.Finished fin)));
            None #CT.client_response
          }
        }
        lhs_other -> {
          fold
            (L.is_valid_tls_message
              (L.LTlsHandshake lhs_other)
              (M.TlsHandshake msg));
          rewrite
            (L.is_valid_tls_message
              (L.LTlsHandshake lhs_other)
              (M.TlsHandshake msg))
            as
            (L.is_valid_tls_message parsed (M.TlsHandshake msg));
          None #CT.client_response
        }
      }
    }
    parsed_other -> {
      with returned_msg. assert (
        L.is_valid_tls_message
          parsed_other
          (M.TlsHandshake returned_msg));
      rewrite
        (L.is_valid_tls_message
          parsed_other
          (M.TlsHandshake returned_msg))
        as
        (L.is_valid_tls_message
          parsed
          (M.TlsHandshake returned_msg));
      None #CT.client_response
    }
  }
}

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
  Trace.emit Trace.client_new 0UL 0UL 0UL;
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
  Trace.emit Trace.client_new
    (SZ.sizet_to_uint64 server_name_len)
    (SZ.sizet_to_uint64 trust_anchors_len)
    (SZ.sizet_to_uint64 validation_time_seconds);
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

fn protected_handshake_buffer_empty
  (c:client)
  requires CR.connection_exactly c 'st0
  returns empty:bool
  ensures CR.connection_exactly c 'st0 **
          pure (empty ==>
            CS.protected_handshake_buffer_empty 'st0.CS.cs_model)
{
  CQ.protected_handshake_buffer_empty_runtime c
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

// The record-transition primitive: decode one record off the front of `raw`
// and take the single semantic step it induces.  Private since Phase 9 -- the
// only client receive primitive in `TLS13.Impl.Client.fsti` is
// `process_coalesced_network_bytes`, so the interface itself witnesses that
// there is one receive path.  This function serves the records whose semantics
// is a single `ConnNetworkEvent`: alerts, change-cipher-spec, application data,
// post-handshake messages, and the two cleartext handshake messages covered by
// the documented Phase 6 exception (`ServerHello`, `HelloRetryRequest`).
// Protected handshake records do not come here; they enter the internal-event
// pipeline in `process_coalesced_network_bytes`.
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
  Trace.emit Trace.client_network_begin
    (SZ.sizet_to_uint64 raw_len)
    0UL
    0UL;
  let decoded = P.decode_network_buffer c raw raw_len;
  match decoded {
    L.NetworkBufferNeedMoreInput -> {
      Trace.emit Trace.client_network_need_more
        (SZ.sizet_to_uint64 raw_len)
        0UL
        0UL;
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
      Trace.emit Trace.client_network_decode_error
        (SZ.sizet_to_uint64 raw_len)
        0UL
        0UL;
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
      Trace.emit Trace.client_network_record
        (FStar.Int.Cast.uint8_to_uint64
          decoded_buffer.L.decoded_buffer_content_type)
        (SZ.sizet_to_uint64
          decoded_buffer.L.decoded_buffer_raw_record_len)
        (SZ.sizet_to_uint64
          decoded_buffer.L.decoded_buffer_fragment_len);
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

// `process_network_bytes` restated in invariant-carrying form.  The body is a
// call plus two assertions: `coalesced_network_bytes_end_to_end_correct` and
// `client_end_to_end_invariant` are both derivable from
// `network_bytes_end_to_end_correct`, so this is an adapter, not a second
// semantics.  It exists because the record primitive is proved without the
// end-to-end invariant while every caller of the receive primitive carries it.
fn process_direct_record
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
                 L.max_record_fragment_len <= SZ.v app_out_len /\
                 CT.client_end_to_end_invariant 'st0)
  returns buffer_resp: CT.client_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.coalesced_network_bytes_end_to_end_correct
                  'st0 st1 buffer_resp (Ghost.reveal 'raw_bytes)
                  'old_network_out network_out_bytes
                  'old_app_out app_out_bytes /\
                CT.client_end_to_end_invariant st1 /\
                (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
                 buffer_resp.CT.consumed_len == 0sz /\
                 WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
                 WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None /\
                 CT.response_stuttered
                   'st0
                   st1
                   buffer_resp.CT.response
                   'old_network_out
                   network_out_bytes
                   'old_app_out
                   app_out_bytes) /\
                (buffer_resp.CT.response.CT.status == CT.StepOk ==>
                 0 < SZ.v buffer_resp.CT.consumed_len) /\
                (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (SZ.v buffer_resp.CT.response.CT.app_out_len > 0 ==>
                 buffer_resp.CT.response.CT.status == CT.StepOk /\
                 buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==>
                 False))
{
  let buffer_resp =
    process_network_bytes
      c raw raw_len
      network_out network_out_len
      app_out app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly c st1 **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  assert (pure (CT.coalesced_network_bytes_end_to_end_correct
    'st0 st1 buffer_resp (Ghost.reveal 'raw_bytes)
    'old_network_out network_out_bytes 'old_app_out app_out_bytes));
  assert (pure (CT.client_end_to_end_invariant st1));
  buffer_resp
}

#push-options "--z3rlimit 100"
fn process_coalesced_network_bytes
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
                 L.max_record_fragment_len <= SZ.v app_out_len /\
                 CT.client_end_to_end_invariant 'st0)
  returns buffer_resp: CT.client_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.coalesced_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  network_out_bytes
                  'old_app_out
                  app_out_bytes /\
                CT.client_end_to_end_invariant st1 /\
                (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
                 buffer_resp.CT.consumed_len == 0sz /\
                 WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
                 WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None /\
                 CT.response_stuttered
                   'st0
                   st1
                   buffer_resp.CT.response
                   'old_network_out
                   network_out_bytes
                   'old_app_out
                   app_out_bytes) /\
                (buffer_resp.CT.response.CT.status == CT.StepOk ==>
                 0 < SZ.v buffer_resp.CT.consumed_len) /\
                (buffer_resp.CT.response.CT.status == CT.DecodeError ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.IllegalTransition ==>
                 buffer_resp.CT.consumed_len == 0sz) /\
                (SZ.v buffer_resp.CT.response.CT.app_out_len > 0 ==>
                 buffer_resp.CT.response.CT.status == CT.StepOk /\
                 buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                (buffer_resp.CT.response.CT.status == CT.OutputBufferTooSmall ==>
                 False))
{
  Trace.emit Trace.client_network_begin
    (SZ.sizet_to_uint64 raw_len)
    1UL
    0UL;
  let decoded = P.decode_network_buffer c raw raw_len;
  match decoded {
    L.NetworkBufferNeedMoreInput -> {
      process_direct_record
        c raw raw_len network_out network_out_len app_out app_out_len
    }
    L.NetworkBufferDecodeError -> {
      process_direct_record
        c raw raw_len network_out network_out_len app_out app_out_len
    }
    L.NetworkBufferOk decoded_buffer -> {
      Trace.emit Trace.client_network_record
        (FStar.Int.Cast.uint8_to_uint64
          decoded_buffer.L.decoded_buffer_content_type)
        (SZ.sizet_to_uint64
          decoded_buffer.L.decoded_buffer_raw_record_len)
        (SZ.sizet_to_uint64
          decoded_buffer.L.decoded_buffer_fragment_len);
      with raw_record_bytes protected_fragment_bytes.
        assert (
          V.pts_to
            decoded_buffer.L.decoded_buffer_raw_record
            raw_record_bytes **
          V.pts_to
            decoded_buffer.L.decoded_buffer_fragment
            protected_fragment_bytes);
      if (decoded_buffer.L.decoded_buffer_protected &&
          decoded_buffer.L.decoded_buffer_content_type = 0x16uy) {
        match decoded_buffer.L.decoded_buffer_parsed {
          Some already_parsed -> {
            with msg. assert (L.is_valid_tls_message already_parsed msg);
            L.free_tls_message already_parsed;
            V.free decoded_buffer.L.decoded_buffer_fragment;
            V.free decoded_buffer.L.decoded_buffer_raw_record;
            process_direct_record
              c raw raw_len network_out network_out_len app_out app_out_len
          }
          None -> {
            V.to_array_pts_to decoded_buffer.L.decoded_buffer_fragment;
            let prefix =
              P.parse_handshake_prefix
                (V.vec_to_array decoded_buffer.L.decoded_buffer_fragment)
                decoded_buffer.L.decoded_buffer_fragment_len;
            match prefix {
              None -> {
                V.to_array_pts_to decoded_buffer.L.decoded_buffer_raw_record;
                let buffered =
                  try_buffer_protected_handshake_record
                    c
                    decoded_buffer.L.decoded_buffer_content_type
                    (V.vec_to_array decoded_buffer.L.decoded_buffer_raw_record)
                    decoded_buffer.L.decoded_buffer_raw_record_len
                    (V.vec_to_array decoded_buffer.L.decoded_buffer_fragment)
                    decoded_buffer.L.decoded_buffer_fragment_len
                    network_out network_out_len
                    app_out app_out_len;
                match buffered {
                  None -> {
                    Trace.emit Trace.client_protected_error
                      0UL
                      (SZ.sizet_to_uint64
                        decoded_buffer.L.decoded_buffer_fragment_len)
                      0UL;
                    V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
                    V.free decoded_buffer.L.decoded_buffer_fragment;
                    V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
                    V.free decoded_buffer.L.decoded_buffer_raw_record;
                    process_direct_record
                      c raw raw_len
                      network_out network_out_len
                      app_out app_out_len
                  }
                  Some resp -> {
                    with st1. assert (
                      CR.connection_exactly c st1 **
                      pure (
                        (exists step.
                          CT.protected_handshake_step_correct
                            'st0
                            st1
                            resp
                            step
                            raw_record_bytes
                            'old_network_out
                            'old_app_out) /\
                        CT.client_end_to_end_invariant st1));
                    V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
                    V.free decoded_buffer.L.decoded_buffer_fragment;
                    V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
                    V.free decoded_buffer.L.decoded_buffer_raw_record;
                    let buffer_resp = {
                      CT.response = resp;
                      CT.consumed_len =
                        decoded_buffer.L.decoded_buffer_consumed_len;
                    };
                    assert (pure (Seq.equal
                      raw_record_bytes
                      (CT.network_consumed_prefix
                        (Ghost.reveal 'raw_bytes)
                        decoded_buffer.L.decoded_buffer_consumed_len)));
                    Seq.lemma_eq_elim
                      raw_record_bytes
                      (CT.network_consumed_prefix
                        (Ghost.reveal 'raw_bytes)
                        decoded_buffer.L.decoded_buffer_consumed_len);
                    Seq.lemma_eq_intro 'old_network_out 'old_network_out;
                    Seq.lemma_eq_intro 'old_app_out 'old_app_out;
                    assert (pure (
                      CT.coalesced_network_bytes_end_to_end_correct
                        'st0
                        st1
                        buffer_resp
                        (Ghost.reveal 'raw_bytes)
                        'old_network_out
                        'old_network_out
                        'old_app_out
                        'old_app_out));
                    assert (pure (
                      buffer_resp.CT.response.CT.status == CT.StepOk));
                    assert (pure (
                      0 < SZ.v buffer_resp.CT.consumed_len));
                    buffer_resp
                  }
                }
              }
              Some parsed_prefix -> {
                with msg message_fragment_bytes.
                  assert (
                    V.pts_to
                      parsed_prefix.L.parsed_handshake_fragment
                      message_fragment_bytes **
                    L.is_valid_tls_message
                      parsed_prefix.L.parsed_handshake_message
                      (M.TlsHandshake msg));
                // A protected record is described by a head/tail chain of
                // ConnProtectedHandshake steps whether or not it actually
                // coalesces several messages: since Phase 2b the head step may
                // saturate its fragment, so a single-message record takes this
                // same route.  There is no second shape and hence no guard:
                // `parse_handshake_prefix` already establishes
                // `consumed <= B.length fragment`.
                V.to_array_pts_to
                  decoded_buffer.L.decoded_buffer_raw_record;
                V.to_array_pts_to
                  parsed_prefix.L.parsed_handshake_fragment;
                let handled =
                  try_process_protected_handshake_head
                    c
                    decoded_buffer.L.decoded_buffer_content_type
                    parsed_prefix.L.parsed_handshake_message
                    parsed_prefix.L.parsed_handshake_consumed
                    (V.vec_to_array
                      decoded_buffer.L.decoded_buffer_raw_record)
                    decoded_buffer.L.decoded_buffer_raw_record_len
                    (V.vec_to_array
                      parsed_prefix.L.parsed_handshake_fragment)
                    (V.vec_to_array
                      decoded_buffer.L.decoded_buffer_fragment)
                    decoded_buffer.L.decoded_buffer_fragment_len
                    network_out
                    network_out_len
                    app_out
                    app_out_len;
                match handled {
                  None -> {
                    with returned_msg. assert (
                      L.is_valid_tls_message
                        parsed_prefix.L.parsed_handshake_message
                        (M.TlsHandshake returned_msg));
                    L.free_tls_message
                      parsed_prefix.L.parsed_handshake_message;
                    V.to_vec_pts_to
                      parsed_prefix.L.parsed_handshake_fragment;
                    V.free
                      parsed_prefix.L.parsed_handshake_fragment;
                    let buffered =
                      try_buffer_protected_handshake_record
                        c
                        decoded_buffer.L.decoded_buffer_content_type
                        (V.vec_to_array
                          decoded_buffer.L.decoded_buffer_raw_record)
                        decoded_buffer.L.decoded_buffer_raw_record_len
                        (V.vec_to_array
                          decoded_buffer.L.decoded_buffer_fragment)
                        decoded_buffer.L.decoded_buffer_fragment_len
                        network_out
                        network_out_len
                        app_out
                        app_out_len;
                    match buffered {
                      None -> {
                        V.to_vec_pts_to
                          decoded_buffer.L.decoded_buffer_fragment;
                        V.free
                          decoded_buffer.L.decoded_buffer_fragment;
                        V.to_vec_pts_to
                          decoded_buffer.L.decoded_buffer_raw_record;
                        V.free
                          decoded_buffer.L.decoded_buffer_raw_record;
                        process_direct_record
                          c raw raw_len
                          network_out network_out_len
                          app_out app_out_len
                      }
                      Some resp -> {
                        with st1. assert (
                          CR.connection_exactly c st1 **
                          pure (
                            (exists step.
                              CT.protected_handshake_step_correct
                                'st0
                                st1
                                resp
                                step
                                raw_record_bytes
                                'old_network_out
                                'old_app_out) /\
                            CT.client_end_to_end_invariant st1));
                        V.to_vec_pts_to
                          decoded_buffer.L.decoded_buffer_fragment;
                        V.free
                          decoded_buffer.L.decoded_buffer_fragment;
                        V.to_vec_pts_to
                          decoded_buffer.L.decoded_buffer_raw_record;
                        V.free
                          decoded_buffer.L.decoded_buffer_raw_record;
                        let buffer_resp = {
                          CT.response = resp;
                          CT.consumed_len =
                            decoded_buffer.L.decoded_buffer_consumed_len;
                        };
                        assert (pure (Seq.equal
                          raw_record_bytes
                          (CT.network_consumed_prefix
                            (Ghost.reveal 'raw_bytes)
                            decoded_buffer.L.decoded_buffer_consumed_len)));
                        Seq.lemma_eq_elim
                          raw_record_bytes
                          (CT.network_consumed_prefix
                            (Ghost.reveal 'raw_bytes)
                            decoded_buffer.L.decoded_buffer_consumed_len);
                        Seq.lemma_eq_intro 'old_network_out 'old_network_out;
                        Seq.lemma_eq_intro 'old_app_out 'old_app_out;
                        assert (pure (
                          CT.coalesced_network_bytes_end_to_end_correct
                            'st0
                            st1
                            buffer_resp
                            (Ghost.reveal 'raw_bytes)
                            'old_network_out
                            'old_network_out
                            'old_app_out
                            'old_app_out));
                        assert (pure (
                          buffer_resp.CT.response.CT.status == CT.StepOk));
                        assert (pure (
                          0 < SZ.v buffer_resp.CT.consumed_len));
                        buffer_resp
                      }
                    }
                  }
                  Some resp -> {
                    with st1. assert (
                      CR.connection_exactly c st1 **
                      pure (
                        (exists step.
                          CT.protected_handshake_step_correct
                            'st0
                            st1
                            resp
                            step
                            raw_record_bytes
                            'old_network_out
                            'old_app_out) /\
                        CT.client_end_to_end_invariant st1));
                    V.to_vec_pts_to
                      parsed_prefix.L.parsed_handshake_fragment;
                    V.free
                      parsed_prefix.L.parsed_handshake_fragment;
                    V.to_vec_pts_to
                      decoded_buffer.L.decoded_buffer_fragment;
                    V.free
                      decoded_buffer.L.decoded_buffer_fragment;
                    V.to_vec_pts_to
                      decoded_buffer.L.decoded_buffer_raw_record;
                    V.free
                      decoded_buffer.L.decoded_buffer_raw_record;
                    let buffer_resp = {
                      CT.response = resp;
                      CT.consumed_len =
                        decoded_buffer.L.decoded_buffer_consumed_len;
                    };
                    assert (pure (Seq.equal
                      raw_record_bytes
                      (CT.network_consumed_prefix
                        (Ghost.reveal 'raw_bytes)
                        decoded_buffer.L.decoded_buffer_consumed_len)));
                    Seq.lemma_eq_elim
                      raw_record_bytes
                      (CT.network_consumed_prefix
                        (Ghost.reveal 'raw_bytes)
                        decoded_buffer.L.decoded_buffer_consumed_len);
                    Seq.lemma_eq_intro
                      'old_network_out
                      'old_network_out;
                    Seq.lemma_eq_intro 'old_app_out 'old_app_out;
                    assert (pure (
                      CT.coalesced_network_bytes_end_to_end_correct
                        'st0
                        st1
                        buffer_resp
                        (Ghost.reveal 'raw_bytes)
                        'old_network_out
                        'old_network_out
                        'old_app_out
                        'old_app_out));
                    assert (pure (
                      buffer_resp.CT.response.CT.status == CT.StepOk));
                    assert (pure (
                      0 < SZ.v buffer_resp.CT.consumed_len));
                    buffer_resp
                  }
                }
              }
            }
          }
        }
      } else {
        match decoded_buffer.L.decoded_buffer_parsed {
          Some parsed -> {
            with msg. assert (L.is_valid_tls_message parsed msg);
            L.free_tls_message parsed;
            V.free decoded_buffer.L.decoded_buffer_fragment;
            V.free decoded_buffer.L.decoded_buffer_raw_record;
            process_direct_record
              c raw raw_len network_out network_out_len app_out app_out_len
          }
          None -> {
            (* G3: a CLEARTEXT record whose fragment parses as no message is
               not necessarily malformed -- it may be one piece of a
               ServerHello split across records.  Try to set it aside before
               treating it as a decode error. *)
            V.to_array_pts_to decoded_buffer.L.decoded_buffer_raw_record;
            V.to_array_pts_to decoded_buffer.L.decoded_buffer_fragment;
            let buffered =
              try_buffer_cleartext_handshake_record
                c
                decoded_buffer.L.decoded_buffer_protected
                decoded_buffer.L.decoded_buffer_content_type
                (V.vec_to_array decoded_buffer.L.decoded_buffer_raw_record)
                decoded_buffer.L.decoded_buffer_raw_record_len
                (V.vec_to_array decoded_buffer.L.decoded_buffer_fragment)
                decoded_buffer.L.decoded_buffer_fragment_len
                network_out network_out_len
                app_out app_out_len;
            match buffered {
              None -> {
                V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
                V.free decoded_buffer.L.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
                V.free decoded_buffer.L.decoded_buffer_raw_record;
                process_direct_record
                  c raw raw_len network_out network_out_len app_out app_out_len
              }
              Some resp -> {
                with st1. assert (
                  CR.connection_exactly c st1 **
                  pure (
                    (exists step.
                      CT.cleartext_handshake_step_correct
                        'st0
                        st1
                        resp
                        step
                        raw_record_bytes
                        'old_network_out
                        'old_app_out) /\
                    CT.client_end_to_end_invariant st1));
                V.to_vec_pts_to decoded_buffer.L.decoded_buffer_fragment;
                V.free decoded_buffer.L.decoded_buffer_fragment;
                V.to_vec_pts_to decoded_buffer.L.decoded_buffer_raw_record;
                V.free decoded_buffer.L.decoded_buffer_raw_record;
                let buffer_resp = {
                  CT.response = resp;
                  CT.consumed_len =
                    decoded_buffer.L.decoded_buffer_consumed_len;
                };
                assert (pure (Seq.equal
                  raw_record_bytes
                  (CT.network_consumed_prefix
                    (Ghost.reveal 'raw_bytes)
                    decoded_buffer.L.decoded_buffer_consumed_len)));
                Seq.lemma_eq_elim
                  raw_record_bytes
                  (CT.network_consumed_prefix
                    (Ghost.reveal 'raw_bytes)
                    decoded_buffer.L.decoded_buffer_consumed_len);
                Seq.lemma_eq_intro 'old_network_out 'old_network_out;
                Seq.lemma_eq_intro 'old_app_out 'old_app_out;
                assert (pure (
                  CT.coalesced_network_bytes_end_to_end_correct
                    'st0
                    st1
                    buffer_resp
                    (Ghost.reveal 'raw_bytes)
                    'old_network_out
                    'old_network_out
                    'old_app_out
                    'old_app_out));
                assert (pure (
                  buffer_resp.CT.response.CT.status == CT.StepOk));
                assert (pure (
                  0 < SZ.v buffer_resp.CT.consumed_len));
                buffer_resp
              }
            }
          }
        }
      }
    }
  }
}

#pop-options
fn process_pending_protected_handshake
  (c:client)
  (empty:array U8.t)
  requires CR.connection_exactly c 'st0 **
           pts_to empty 'empty_bytes **
           pure (Seq.equal (Ghost.reveal 'empty_bytes) B.empty /\
                 CT.client_end_to_end_invariant 'st0)
  returns result:option CT.client_response
  ensures exists* st1.
          CR.connection_exactly c st1 **
          pts_to empty 'empty_bytes **
          pure (
            CT.pending_protected_handshake_result_correct
              'st0 st1 result /\
            CT.client_end_to_end_invariant st1)
{
  let pending = CQ.copy_pending_protected_handshake c;
  match pending {
    None -> {
      Trace.emit Trace.client_protected_empty 0UL 0UL 0UL;
      assert (pure (
        CT.pending_protected_handshake_result_correct
          'st0 'st0 None));
      None #CT.client_response
    }
    Some snapshot -> {
      with pending_fragment_bytes. assert (
        V.pts_to
          snapshot.CR.pending_protected_fragment
          pending_fragment_bytes);
      V.to_array_pts_to snapshot.CR.pending_protected_fragment;
      let prefix =
        P.parse_handshake_prefix_at
          (V.vec_to_array snapshot.CR.pending_protected_fragment)
          snapshot.CR.pending_protected_fragment_len
          snapshot.CR.pending_protected_parsed;
      match prefix {
        None -> {
          Trace.emit Trace.client_protected_buffer
            (SZ.sizet_to_uint64
              snapshot.CR.pending_protected_parsed)
            (SZ.sizet_to_uint64
              snapshot.CR.pending_protected_fragment_len)
            0UL;
          V.to_vec_pts_to snapshot.CR.pending_protected_fragment;
          V.free snapshot.CR.pending_protected_fragment;
          // With cross-record reassembly, a pending buffer that does not yet
          // hold a complete handshake message is the ordinary in-flight
          // case, not a decode failure: the message is still arriving over
          // more records. Leaving the state untouched (rather than reporting
          // DecodeError) lets the driver keep reading network bytes and
          // buffering them onto this same pending message.
          let resp = {
            CT.network_out_len = 0sz;
            CT.app_out_len = 0sz;
            CT.status = CT.NeedMoreInput;
          };
          assert (pure (
            CT.pending_protected_handshake_result_correct
              'st0 'st0 (Some resp)));
          Some resp
        }
        Some parsed_prefix -> {
          with msg message_fragment_bytes. assert (
            V.pts_to
              parsed_prefix.L.parsed_handshake_fragment
              message_fragment_bytes **
            L.is_valid_tls_message
              parsed_prefix.L.parsed_handshake_message
              (M.TlsHandshake msg));
          let parsed_total =
            SZ.add
              snapshot.CR.pending_protected_parsed
              parsed_prefix.L.parsed_handshake_consumed;
          V.to_array_pts_to
            parsed_prefix.L.parsed_handshake_fragment;
          let handled =
            try_process_protected_handshake_drain
              c
              parsed_prefix.L.parsed_handshake_message
              parsed_prefix.L.parsed_handshake_consumed
              snapshot.CR.pending_protected_parsed
              parsed_total
              empty
              (V.vec_to_array
                parsed_prefix.L.parsed_handshake_fragment)
              (V.vec_to_array
                snapshot.CR.pending_protected_fragment)
              snapshot.CR.pending_protected_fragment_len;
          match handled {
            None -> {
              with returned_msg. assert (
                L.is_valid_tls_message
                  parsed_prefix.L.parsed_handshake_message
                  (M.TlsHandshake returned_msg));
              L.free_tls_message
                parsed_prefix.L.parsed_handshake_message;
              V.to_vec_pts_to
                parsed_prefix.L.parsed_handshake_fragment;
              V.free
                parsed_prefix.L.parsed_handshake_fragment;
              V.to_vec_pts_to
                snapshot.CR.pending_protected_fragment;
              V.free snapshot.CR.pending_protected_fragment;
              let resp = {
                CT.network_out_len = 0sz;
                CT.app_out_len = 0sz;
                CT.status = CT.IllegalTransition;
              };
              assert (pure (
                CT.pending_protected_handshake_result_correct
                  'st0 'st0 (Some resp)));
              Some resp
            }
            Some resp -> {
              with st1. assert (
                CR.connection_exactly c st1 **
                pure (
                  (exists step.
                    CT.protected_handshake_step_correct
                      'st0 st1 resp step B.empty B.empty B.empty) /\
                  CT.client_end_to_end_invariant st1));
              V.to_vec_pts_to
                parsed_prefix.L.parsed_handshake_fragment;
              V.free
                parsed_prefix.L.parsed_handshake_fragment;
              V.to_vec_pts_to
                snapshot.CR.pending_protected_fragment;
              V.free snapshot.CR.pending_protected_fragment;
              assert (pure (
                CT.pending_protected_handshake_result_correct
                  'st0 st1 (Some resp)));
              Some resp
            }
          }
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
  Trace.emit Trace.client_local_event_begin
    (match kind with
     | CT.LocalStartHandshake -> 0UL
     | CT.LocalDeriveSharedSecret -> 1UL
     | CT.LocalInstallClientHandshakeTrafficKeys -> 2UL
     | CT.LocalInstallServerHandshakeTrafficKeys -> 3UL
     | CT.LocalInstallClientApplicationTrafficKeys -> 4UL
     | CT.LocalInstallServerApplicationTrafficKeys -> 5UL
     | CT.LocalValidateCertificate -> 6UL
     | CT.LocalVerifyCertificateSignature -> 7UL
     | CT.LocalVerifyFinished -> 8UL
     | CT.LocalDeliverApplicationData -> 9UL
     | CT.LocalSendClientHello -> 10UL
     | CT.LocalSendClientFinished -> 11UL
     | CT.LocalSendApplicationData -> 12UL
     | CT.LocalSendKeyUpdate -> 13UL
     | CT.LocalSendCloseNotify -> 14UL
     | CT.LocalFail -> 15UL
     | CT.LocalProcessPendingHandshake -> 16UL
     | CT.LocalSendKeyUpdateRequested -> 17UL)
    (SZ.sizet_to_uint64 payload_len)
    0UL;
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
  Trace.emit Trace.client_local_event_end
    (match resp.CT.status with
     | CT.StepOk -> 0UL
     | CT.NeedMoreInput -> 1UL
     | CT.DecodeError -> 2UL
     | CT.IllegalTransition -> 3UL
     | CT.OutputBufferTooSmall -> 4UL
     | CT.ConnectionFailed -> 5UL)
    (SZ.sizet_to_uint64 resp.CT.network_out_len)
    (SZ.sizet_to_uint64 resp.CT.app_out_len);
  resp
}

fn free_client
  (c:client)
  requires connection_exactly c 'st0
  ensures connection_released c 'st0
{
  Trace.emit Trace.client_free 0UL 0UL 0UL;
  rewrite (connection_exactly c 'st0) as (CR.connection_exactly c 'st0);
  CR.free_connection c;
  rewrite (CR.connection_released c 'st0) as (connection_released c 'st0)
}
