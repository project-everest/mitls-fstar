module TLS13.Impl.ConnectionState.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Queries = TLS13.Impl.ConnectionState.Queries
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.StateMachine
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Queries
open TLS13.Impl.ConnectionState.Repr

fn mark_received_change_cipher_spec
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((exists stage.
                    st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsChangeCipherSpec;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_change_cipher_spec_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_alert_failure
  (c:connection_state)
  (raw:array U8.t)
  (alert_wire:U8.t)
  (#alert:erased T.alert_description)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (Ghost.reveal alert <> T.Close_notify /\
                 Tags.alert_tag_matches alert_wire (Ghost.reveal alert) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert (Ghost.reveal alert);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_alert_failure_state st0 (Ghost.reveal alert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_close_notify_for_role
  (c:connection_state)
  (raw:array U8.t)
  (#role:erased CS.endpoint_role)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure ((st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == role /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsAlert T.Close_notify;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_close_notify
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          pure ((st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                CS.event_raw_delta_legal
                  st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.Close_notify;
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
           c
           (received_close_notify_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_hello_retry_request_rejected
  (c:connection_state)
  (raw:array U8.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_hello_retry_request_rejected_state st0 (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_server_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased GSH.serverHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloSent /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 SZ.v fragment_len <= max_server_hello_len /\
                 Seq.equal
                   (Ghost.reveal 'fragment_bytes)
                   (W.serialize_handshake (M.ServerHello sh)) /\
                 st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   B.length (W.serialize_handshake (M.ServerHello sh)) <=
                   max_transcript_len /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   }) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_hello_state st0 sh (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes

fn mark_received_client_hello
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased GCH.clientHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          IM.is_valid_client_hello lch ch **
          pure (st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
                B.length 'fragment_bytes == SZ.v fragment_len /\
                SZ.v fragment_len <= max_client_hello_len /\
                Seq.equal
                  (Ghost.reveal 'fragment_bytes)
                  (W.serialize_handshake (M.ClientHello ch)) /\
                lch.IM.client_hello_has_server_name == true /\
                client_hello_server_name_len_for ch ==
                  lch.IM.client_hello_server_name_len /\
                client_hello_cipher_suites_len_for ch ==
                  lch.IM.client_hello_cipher_suites_len /\
                client_hello_signature_schemes_len_for ch ==
                  lch.IM.client_hello_signature_schemes_len /\
                st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
                B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  B.length (W.serialize_handshake (M.ClientHello ch)) <=
                  max_transcript_len /\
                CS.legal_event
                  st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                CS.event_raw_delta_legal
                  st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
           c
           (received_client_hello_state st0 ch (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          IM.is_valid_client_hello lch ch

fn mark_received_encrypted_extensions
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lee:IM.encrypted_extensions)
  (#ee:erased GEE.encryptedExtensions)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_encrypted_extensions lee ee **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerHelloReceived /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.EncryptedExtensions ee)) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_encrypted_extensions_state st0 ee (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes

fn mark_received_certificate
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_msg lcert cert **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
           st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
           Sem.certificate_entries (Ghost.reveal cert) <> [] /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          Pulse.Lib.Array.PtsTo.pts_to fragment 'fragment_bytes **
          pure (match Sem.certificate_entries (Ghost.reveal cert) with
                | leaf :: _ ->
                  (received_certificate_state st0 (Ghost.reveal cert) (Ghost.reveal 'raw_bytes)).
                    CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der ==
                    Some leaf
                | [] -> False)

fn mark_received_certificate_verify
  (c:connection_state)
  (raw:array U8.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lcv:IM.certificate_verify)
  (#cv:erased GCV.certificateVerify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           ArrPts.pts_to fragment 'fragment_bytes **
           IM.is_valid_certificate_verify lcv cv **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateValidated /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  B.length 'fragment_bytes == SZ.v fragment_len /\
                  Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (W.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= max_transcript_len /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes **
          ArrPts.pts_to fragment 'fragment_bytes **
          pure ((received_certificate_verify_state st0 (Ghost.reveal cv) (Ghost.reveal 'raw_bytes)).
                  CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input ==
                Some
                  (H.certificate_verify_input
                    (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)))

fn mark_received_server_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    max_transcript_len /\
                  U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                  CS.event_raw_delta_legal
                    st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
                    })
                    B.empty
                    (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_server_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes

fn mark_received_client_finished
  (c:connection_state)
  (raw:array U8.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pure (Model.can_receive_client_finished st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal 'raw_bytes)) **
          ArrPts.pts_to raw 'raw_bytes

fn mark_received_application_data
  (c:connection_state)
  (raw:array U8.t)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsApplicationData bytes;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_application_data_for_role
  (c:connection_state)
  (raw:array U8.t)
  (#role:erased CS.endpoint_role)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
          pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st0.CS.cs_model.CS.model_config.CS.config_role == role /\
                CS.application_traffic_available_for_role
                  role
                  st0.CS.cs_model.CS.model_handshake
                  CL.Received /\
                U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                CS.event_raw_delta_legal
                  st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
           c
           (received_application_data_state st0 bytes (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_ignored_post_handshake
  (c:connection_state)
  (raw:array U8.t)
  (#body:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsIgnoredPostHandshake body;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_ignored_post_handshake_state st0 body (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes

fn mark_received_key_update
  (c:connection_state)
  (raw:array U8.t)
  (requested:bool)
  (#req:erased M.key_update_request)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                 (requested ==> req == M.UpdateRequested) /\
                 (requested == false ==> req == M.UpdateNotRequested) /\
                 CS.event_raw_delta_legal
                   st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsKeyUpdate req;
                   })
                   B.empty
                   (Ghost.reveal 'raw_bytes))
  ensures connection_exactly
            c
            (received_key_update_state st0 req (Ghost.reveal 'raw_bytes)) **
          Pulse.Lib.Array.PtsTo.pts_to raw 'raw_bytes
