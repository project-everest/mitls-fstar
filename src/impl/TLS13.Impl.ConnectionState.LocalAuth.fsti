module TLS13.Impl.ConnectionState.LocalAuth

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
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
module SM = TLS13.Spec.StateMachine.ClientTrace
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
