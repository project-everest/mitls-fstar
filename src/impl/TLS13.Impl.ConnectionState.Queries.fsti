module TLS13.Impl.ConnectionState.Queries

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

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Repr

fn config_role_is_client
  (cfg:connection_config_storage)
  (#spec:erased CS.connection_config)
  requires connection_config_exactly cfg spec
  returns ok: bool
  ensures connection_config_exactly cfg spec **
          pure (ok ==> spec.CS.config_role == CS.ClientEndpoint)

fn config_role_is_server
  (cfg:connection_config_storage)
  (#spec:erased CS.connection_config)
  requires connection_config_exactly cfg spec
  returns ok: bool
  ensures connection_config_exactly cfg spec **
          pure (ok ==> spec.CS.config_role == CS.ServerEndpoint)

fn get_control_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:control_snapshot
  ensures connection_exactly c st0 **
          pure (control_snapshot_matches snapshot st0)

fn get_key_schedule_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:key_schedule_snapshot
  ensures connection_exactly c st0 **
          pure (key_schedule_snapshot_matches snapshot st0)

fn copy_certificate_leaf_der
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                | Some leaf ->
                  SZ.v copied_len == B.length leaf /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                | None -> False))

fn copy_certificate_verify_input
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                | Some input ->
                  SZ.v copied_len == B.length input /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                | None -> False))

fn copy_certificate_verify_signature
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 IM.max_signature_len <= SZ.v out_len /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.cv_signature_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  IM.signature_scheme_matches snapshot.cv_signature_scheme cv.M.scheme /\
                  SZ.v snapshot.cv_signature_len == B.length cv.M.signature /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.cv_signature_len))
                    cv.M.signature
                | None -> False))

fn get_certificate_verify_signature_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:certificate_verify_signature_snapshot
  ensures connection_exactly c st0 **
          pure (SZ.v snapshot.cv_signature_len <= IM.max_signature_len /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  IM.signature_scheme_matches snapshot.cv_signature_scheme cv.M.scheme /\
                  SZ.v snapshot.cv_signature_len == B.length cv.M.signature
                | None -> False))

fn is_handshaking
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==> (exists stage.
            st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage))

fn is_waiting_server_hello
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)

fn can_start_handshake_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlNew /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_start == None)

fn can_start_server_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlNew /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)

fn can_send_client_hello_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsStarted /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_start /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
              <= max_transcript_len - max_client_hello_len /\
            517 <= SZ.v network_out_len)

fn can_receive_server_hello
  (c:connection_state)
  (#sh:erased M.server_hello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              B.length (W.serialize_handshake (M.ServerHello sh)) <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ServerHello sh);
              }))

fn can_receive_client_hello
  (c:connection_state)
  (fragment_len:SZ.t)
  (#ch:erased M.client_hello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsAwaitingClientHello /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }))

fn can_receive_client_finished
  (c:connection_state)
  (#fin:erased M.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
              }))

fn can_receive_application_data
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))

fn can_receive_endpoint_application_data
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Received /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))

fn can_deliver_application_data
  (c:connection_state)
  (payload_len:SZ.t)
  (app_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            SZ.v payload_len <= SZ.v app_out_len)

fn can_install_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)

fn can_install_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)

fn can_receive_encrypted_extensions
  (c:connection_state)
  (#ee:erased M.encrypted_extensions)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              }))

fn can_send_encrypted_extensions_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value =
                  M.TlsHandshake (M.EncryptedExtensions { M.negotiated_alpn = None });
              }))

fn can_send_certificate_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (match st0.CS.cs_model.CS.model_config.CS.config_server with
                | Some cfg ->
                  B.length cfg.CS.server_certificate_chain <=
                    max_server_certificate_chain_len
                | None -> False)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            (match st0.CS.cs_model.CS.model_config.CS.config_server with
             | Some cfg ->
              B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                B.length
                  (W.serialize_certificate_from_credential
                    { M.chain = [cfg.CS.server_certificate_chain] }) <=
                  max_transcript_len /\
              CS.legal_event
                st0.CS.cs_model
                (CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value =
                    M.TlsHandshake
                      (M.Certificate { M.chain = [cfg.CS.server_certificate_chain] });
                })
             | None -> False))

fn can_sign_certificate_verify_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None)

fn can_send_certificate_verify_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            (let cv =
              Some?.v
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
               B.length (W.serialize_certificate_verify_from_signature cv) <=
                 max_transcript_len /\
             CS.legal_event
               st0.CS.cs_model
               (CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
               })))

fn can_send_server_finished_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len)

fn can_receive_certificate
  (c:connection_state)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           IM.is_valid_certificate_msg lcert cert
  returns ok: bool
  ensures connection_exactly c st0 **
          IM.is_valid_certificate_msg lcert cert **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
            (Ghost.reveal cert).M.chain <> [] /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
              }))

fn can_validate_certificate
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der /\
            SZ.v payload_len <= max_public_key_len)

fn can_receive_certificate_verify
  (c:connection_state)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateValidated /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
              }))

fn can_verify_certificate_signature
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false)

fn can_receive_server_finished
  (c:connection_state)
  (#fin:erased M.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
              }))

fn can_verify_server_finished
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v payload_len <= max_transcript_len)

fn server_finished_verify_data_matches
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedReceived /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
             | Some fin, Some server_hs ->
               H.verify_finished
                 server_hs.CS.traffic_secret
                 (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                 fin
             | _, _ -> False))

fn can_send_client_finished_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len /\
            58 <= SZ.v network_out_len)

fn can_send_application_data_runtime
  (c:connection_state)
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            SZ.v payload_len <= SM.max_application_data_fragment_len /\
            SZ.v payload_len + 22 <= SZ.v network_out_len)

fn can_send_endpoint_application_data_runtime
  (c:connection_state)
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Sent /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            SZ.v payload_len <= SM.max_application_data_fragment_len /\
            SZ.v payload_len + 22 <= SZ.v network_out_len)

fn can_send_close_notify_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            24 <= SZ.v network_out_len)

fn can_send_endpoint_close_notify_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Sent /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            24 <= SZ.v network_out_len)

fn can_send_key_update_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            27 <= SZ.v network_out_len)

fn can_receive_endpoint_close_notify
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
             st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))

fn can_receive_close_notify
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
             st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
