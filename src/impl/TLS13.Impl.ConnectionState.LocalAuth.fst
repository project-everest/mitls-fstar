module TLS13.Impl.ConnectionState.LocalAuth

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

fn mark_validated_certificate
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (#peer:erased X.peer_identity)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
                  B.length 'payload_bytes == SZ.v payload_len /\
                  SZ.v payload_len <= max_public_key_len /\
                  (Ghost.reveal peer).X.validated_hostname ==
                    st0.CS.cs_model.CS.model_config.CS.config_server_name /\
                  (Ghost.reveal peer).X.leaf_public_key ==
                    (Ghost.reveal 'payload_bytes) /\
                  (Ghost.reveal peer).X.permitted_signature_schemes == [] /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalValidateCertificate (Ghost.reveal peer))))
  ensures connection_exactly
            c
            (validated_certificate_state st0 (Ghost.reveal peer)) **
          ArrPts.pts_to payload 'payload_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));
  assert (pure (B.length 'payload_bytes == SZ.v payload_len));
  assert (pure (SZ.v payload_len <= max_public_key_len));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalValidateCertificate (Ghost.reveal peer)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
  with role validation_time. _;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len. _;

  c.control.handshake_stage_tag := 6uy;
  assert (pure (Tags.control_state_matches
    1uy
    6uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateValidated)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateValidated)
    st0.CS.cs_model.CS.model_failure);

  fold (sized_bytes_allocated
    c.handshake.validated_peer.validated_hostname
    max_hostname_len);
  copy_hostname_sized_bytes
    c.config.server_name
    c.handshake.validated_peer.validated_hostname;
  rewrite (sized_bytes_exactly
    c.handshake.validated_peer.validated_hostname
    max_hostname_len
    st0.CS.cs_model.CS.model_config.CS.config_server_name)
    as (sized_bytes_exactly
      c.handshake.validated_peer.validated_hostname
      max_hostname_len
      (Ghost.reveal peer).X.validated_hostname);

  fold (sized_bytes_allocated
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len);
  copy_array_to_public_key_sized_bytes
    payload
    c.handshake.validated_peer.leaf_public_key
    payload_len;
  rewrite (sized_bytes_exactly
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len
    (Ghost.reveal 'payload_bytes))
    as (sized_bytes_exactly
      c.handshake.validated_peer.leaf_public_key
      max_public_key_len
      (Ghost.reveal peer).X.leaf_public_key);

  c.handshake.validated_peer.permitted_signature_schemes.len := 0sz;
  c.handshake.validated_peer.present := true;

  unfold (sized_bytes_exactly
    c.handshake.validated_peer.validated_hostname
    max_hostname_len
    (Ghost.reveal peer).X.validated_hostname);
  with stored_hostname stored_hostname_len. _;
  unfold (sized_bytes_exactly
    c.handshake.validated_peer.leaf_public_key
    max_public_key_len
    (Ghost.reveal peer).X.leaf_public_key);
  with stored_public_key stored_public_key_len. _;
  assert_norm (IM.signature_schemes_match peer_schemes 0 []);
  assert (pure (IM.signature_schemes_match
    peer_schemes
    (SZ.v 0sz)
    (Ghost.reveal peer).X.permitted_signature_schemes));
  fold (peer_exactly
    c.handshake.validated_peer
    (Some (Ghost.reveal peer)));

  fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);

  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (cv_verified ==
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_handshake);

  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (validated_certificate_state st0 (Ghost.reveal peer)).CS.cs_model);

  lemma_validated_certificate_state_evolves st0 (Ghost.reveal peer);
  MR.update
    c.ghost_state
    (validated_certificate_state st0 (Ghost.reveal peer));
  fold (connection_exactly
    c
    (validated_certificate_state st0 (Ghost.reveal peer)))
}

fn mark_verified_certificate_signature
  (c:connection_state)
  (#cv:erased GCV.certificateVerify)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalVerifyCertificateSignature (Ghost.reveal cv))))
  ensures connection_exactly
            c
            (verified_certificate_signature_state st0 (Ghost.reveal cv))
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsCertificateVerifyReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    Some (Ghost.reveal cv)));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalVerifyCertificateSignature (Ghost.reveal cv)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.handshake_stage_tag := 8uy;
  assert (pure (Tags.control_state_matches
    1uy
    8uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsCertificateVerifyVerified)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsCertificateVerifyVerified)
    st0.CS.cs_model.CS.model_failure);

  c.handshake.certificate_verify_verified := true;

  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    as (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (true ==
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_handshake);

  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config);
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (verified_certificate_signature_state st0 (Ghost.reveal cv)).CS.cs_model);

  lemma_verified_certificate_signature_state_evolves st0 (Ghost.reveal cv);
  MR.update
    c.ghost_state
    (verified_certificate_signature_state st0 (Ghost.reveal cv));
  fold (connection_exactly
    c
    (verified_certificate_signature_state st0 (Ghost.reveal cv)))
}

fn mark_verified_server_finished
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    Some (Ghost.reveal fin) /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
                  B.length 'payload_bytes == SZ.v payload_len /\
                  Seq.equal
                    (Ghost.reveal 'payload_bytes)
                    (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v payload_len <= max_transcript_len /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalVerifyFinished (Ghost.reveal fin))))
  ensures connection_exactly
            c
            (verified_server_finished_state st0 (Ghost.reveal fin)) **
          ArrPts.pts_to payload 'payload_bytes
{
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedReceived));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));
  assert (pure (B.length 'payload_bytes == SZ.v payload_len));
  assert (pure (Seq.equal
    (Ghost.reveal 'payload_bytes)
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalVerifyFinished (Ghost.reveal fin)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.handshake_stage_tag := 10uy;
  assert (pure (Tags.control_state_matches
    1uy
    10uy
    false
    0uy
    0uy
    (CS.ControlHandshaking CS.HsServerFinishedVerified)));
  fold (control_exactly
    c.control
    (CS.ControlHandshaking CS.HsServerFinishedVerified)
    st0.CS.cs_model.CS.model_failure);

  c.handshake.server_finished_verified := true;

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v payload_len <= max_transcript_len));

  copy_array_to_transcript
    payload
    c.handshake.transcript.bytes
    payload_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v payload_len)));
  let new_transcript_len = SZ.add transcript_len payload_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'payload_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (true ==
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure (cv_verified ==
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  fold (handshake_exactly
    c.handshake
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);

  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config);
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (verified_server_finished_state st0 (Ghost.reveal fin)).CS.cs_model);

  lemma_verified_server_finished_state_evolves st0 (Ghost.reveal fin);
  MR.update
    c.ghost_state
    (verified_server_finished_state st0 (Ghost.reveal fin));
  fold (connection_exactly
    c
    (verified_server_finished_state st0 (Ghost.reveal fin)))
}

fn mark_verified_stored_server_finished
  (c:connection_state)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedReceived /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    Some (Ghost.reveal fin) /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
                  B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    max_transcript_len /\
                  CS.legal_event
                    st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalVerifyFinished (Ghost.reveal fin))))
  ensures connection_exactly
            c
            (verified_server_finished_state st0 (Ghost.reveal fin))
{
  let mut serialized_finished = [| 0uy; 36sz |];

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  with stored. assert (Box.pts_to c.handshake.messages.server_finished stored);
  let stored_fin_opt = !c.handshake.messages.server_finished;
  assert (pure (stored_fin_opt == stored));
  assert (pure (Some? stored_fin_opt));
  let lfin = Some?.v stored_fin_opt;
  assert (pure (stored_fin_opt == Some lfin));
  assert (pure (stored == Some lfin));

  rewrite (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_finished lfin (Ghost.reveal fin));
  let written_len =
    Ser.serialize_finished_handshake
      #fin
      lfin
      serialized_finished
      36sz;
  with serialized_finished_bytes.
    assert (ArrPts.pts_to serialized_finished serialized_finished_bytes);
  assert (pure (Seq.equal
    serialized_finished_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (SZ.v written_len == 36));
  rewrite (IM.is_valid_finished lfin (Ghost.reveal fin))
    as (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
      | _, _ -> pure False);
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  mark_verified_server_finished
    c
    serialized_finished
    36sz
    #fin
}

fn mark_verified_client_finished
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 Seq.equal
                   (Ghost.reveal 'payload_bytes)
                   (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v payload_len <= max_transcript_len /\
                 can_verify_client_finished st0 (Ghost.reveal fin))
  ensures connection_exactly
            c
            (verified_client_finished_state st0 (Ghost.reveal fin)) **
          ArrPts.pts_to payload 'payload_bytes
{
  assert (pure (can_verify_client_finished st0 (Ghost.reveal fin)));
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientFinishedReceived));
  assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent
      (CS.LocalVerifyClientFinished (Ghost.reveal fin)))));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.control_tag := 2uy;
  assert (pure (Tags.control_state_matches
    2uy
    17uy
    false
    0uy
    0uy
    CS.ControlApplicationData));
  fold (control_exactly
    c.control
    CS.ControlApplicationData
    st0.CS.cs_model.CS.model_failure);

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v payload_len <= max_transcript_len));

  copy_array_to_transcript
    payload
    c.handshake.transcript.bytes
    payload_len
    transcript_len;

  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v payload_len)));
  let new_transcript_len = SZ.add transcript_len payload_len;
  c.handshake.transcript.len := new_transcript_len;

  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'payload_bytes))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (handshake_messages_exactly
    c.handshake.messages
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (cv_verified ==
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_handshake);

  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record ==
    st0.CS.cs_model.CS.model_record));
  assert (pure ((verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config);
  rewrite (record_layer_exactly c.records st0.CS.cs_model.CS.model_record)
    as (record_layer_exactly
      c.records
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_record);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (verified_client_finished_state st0 (Ghost.reveal fin)).CS.cs_model);

  lemma_verified_client_finished_state_evolves st0 (Ghost.reveal fin);
  MR.update
    c.ghost_state
    (verified_client_finished_state st0 (Ghost.reveal fin));
  fold (connection_exactly
    c
    (verified_client_finished_state st0 (Ghost.reveal fin)))
}

fn mark_verified_stored_client_finished
  (c:connection_state)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                   Some (Ghost.reveal fin) /\
                 B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   max_transcript_len /\
                 can_verify_client_finished st0 (Ghost.reveal fin))
  ensures connection_exactly
            c
            (verified_client_finished_state st0 (Ghost.reveal fin))
{
  let mut serialized_finished = [| 0uy; 36sz |];

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  with stored. assert (Box.pts_to c.handshake.messages.client_finished stored);
  let stored_fin_opt = !c.handshake.messages.client_finished;
  assert (pure (stored_fin_opt == stored));
  assert (pure (Some? stored_fin_opt));
  let lfin = Some?.v stored_fin_opt;
  assert (pure (stored_fin_opt == Some lfin));
  assert (pure (stored == Some lfin));

  rewrite (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_finished lfin (Ghost.reveal fin));
  let written_len =
    Ser.serialize_finished_handshake
      #fin
      lfin
      serialized_finished
      36sz;
  with serialized_finished_bytes.
    assert (ArrPts.pts_to serialized_finished serialized_finished_bytes);
  assert (pure (Seq.equal
    serialized_finished_bytes
    (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  assert (pure (SZ.v written_len == 36));
  rewrite (IM.is_valid_finished lfin (Ghost.reveal fin))
    as (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
      | _, _ -> pure False);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  mark_verified_client_finished
    c
    serialized_finished
    36sz
    #fin
}
