module TLS13.Impl.ConnectionState.Queries

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
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

// Phase 5: handshake_msg payloads are now the QuackyDucky-generated wire
// records; profile-relevant fields are read through the TLS13.Wire.Semantics
// accessors instead of the deleted M.<record> projection fields.
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

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

fn copy_pending_protected_handshake
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:option pending_protected_handshake_snapshot
  ensures connection_exactly c st0 **
          (match snapshot with
           | None ->
             pure (
               st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed >=
                 B.length
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes)
           | Some pending ->
             exists* fragment.
               V.pts_to pending.pending_protected_fragment fragment **
               pure (
                 V.is_full_vec pending.pending_protected_fragment /\
                 V.length pending.pending_protected_fragment ==
                   SZ.v pending.pending_protected_fragment_len /\
                 B.length fragment ==
                   SZ.v pending.pending_protected_fragment_len /\
                 Seq.equal
                   fragment
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes /\
                 SZ.v pending.pending_protected_fragment_len ==
                   B.length
                     st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes /\
                 SZ.v pending.pending_protected_fragment_len <=
                   max_handshake_flight_len /\
                 SZ.v pending.pending_protected_parsed ==
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed /\
                 SZ.v pending.pending_protected_parsed <
                   SZ.v pending.pending_protected_fragment_len))

fn protected_handshake_buffer_empty_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns empty:bool
  ensures connection_exactly c st0 **
          pure (empty ==>
            CS.protected_handshake_buffer_empty st0.CS.cs_model)

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

fn copy_certificate_chain
  (c:connection_state)
  (chain_out:array U8.t)
  (chain_out_len:SZ.t)
  (offsets_out:array SZ.t)
  (offsets_out_len:SZ.t)
  (lens_out:array SZ.t)
  (lens_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to chain_out 'old_chain_out **
           ArrPts.pts_to offsets_out 'old_offsets_out **
           ArrPts.pts_to lens_out 'old_lens_out **
           pure (B.length 'old_chain_out == SZ.v chain_out_len /\
                Seq.length 'old_offsets_out == SZ.v offsets_out_len /\
                Seq.length 'old_lens_out == SZ.v lens_out_len /\
                SZ.v chain_out_len == IM.max_certificate_chain_bytes /\
                SZ.v offsets_out_len == IM.max_certificate_chain_entries /\
                SZ.v lens_out_len == IM.max_certificate_chain_entries /\
                Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate)
  returns snapshot:certificate_chain_snapshot
  ensures exists* chain_bytes offsets lens.
          connection_exactly c st0 **
          ArrPts.pts_to chain_out chain_bytes **
          ArrPts.pts_to offsets_out offsets **
          ArrPts.pts_to lens_out lens **
          pure (B.length chain_bytes == SZ.v chain_out_len /\
                Seq.length offsets == SZ.v offsets_out_len /\
                Seq.length lens == SZ.v lens_out_len /\
                SZ.v snapshot.certificate_chain_bytes_len <= B.length chain_bytes /\
                SZ.v snapshot.certificate_chain_cert_count <= Seq.length offsets /\
                SZ.v snapshot.certificate_chain_cert_count <= Seq.length lens /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_certificate with
                | Some cert ->
                  IM.certificate_chain_matches
                    chain_bytes
                    (SZ.v snapshot.certificate_chain_bytes_len)
                    offsets
                    lens
                    (SZ.v snapshot.certificate_chain_cert_count)
                    (Sem.certificate_entries cert)
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
                  IM.signature_scheme_matches snapshot.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                  SZ.v snapshot.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.cv_signature_len))
                    (Sem.certificateVerify_signature_bytes cv)
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
                  IM.signature_scheme_matches snapshot.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                  SZ.v snapshot.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv)
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
  (fragment_len:SZ.t)
  (#sh:erased GSH.serverHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Sem.serverHello_cipher_suite sh == Some T.TLS_CHACHA20_POLY1305_SHA256 /\
             // Parse-success equation supplied by the caller (see
             // TLS13.Impl.Handle.Handshake): the decoded ServerHello serializes
             // back to the on-the-wire fragment, so its serialized-handshake
             // length equals the concrete [fragment_len].  Combined with the
             // runtime [fragment_fits_sh] gate this discharges the ServerHello
             // wire-profile bound (<= 16640) in the [legal_event] obligation
             // without re-proving the deleted static length lemma.
             B.length (W.serialize_handshake (M.ServerHello sh)) == SZ.v fragment_len)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            // Phase 4 deleted W.lemma_serialize_server_hello_len, so
            // `B.length (serialize_handshake (M.ServerHello sh)) <=
            // max_server_hello_len` is no longer a static theorem for general
            // generated serverHello records that carry arbitrary extensions.
            // The gate therefore takes the concrete [fragment_len] (the length of
            // the serialized record on the wire) and checks at runtime that it
            // fits the ServerHello buffer and the remaining transcript budget,
            // exactly as [can_receive_client_hello] does.  The caller connects
            // [SZ.v fragment_len] to [B.length (serialize_handshake ...)] via the
            // parse-success equation before calling [mark_received_server_hello].
            SZ.v fragment_len <= Bounds.max_server_hello_len /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <=
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
  (#ch:erased GCH.clientHello)
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

fn can_select_supported_server_parameters_runtime
  (c:connection_state)
  (#server_random:erased (b:B.bytes{B.length b == 32}))
  (#server_private_key:erased (b:B.bytes{B.length b == 32}))
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
                  (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                         st0.CS.cs_model.CS.model_config.CS.config_server with
                   | Some ch, Some cfg ->
                     CS.cipher_suite_offered
                       cfg.CS.server_supported_cipher_suites
                       T.TLS_CHACHA20_POLY1305_SHA256 /\
                     CS.named_group_offered
                       cfg.CS.server_supported_groups
                       T.X25519 /\
                     CS.signature_scheme_offered
                       cfg.CS.server_allowed_signature_schemes
                       T.Rsa_pss_rsae_sha256 /\
                     CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
                   | _, _ -> True))
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            server_selection_absent st0.CS.cs_model.CS.model_handshake /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                    st0.CS.cs_model.CS.model_config.CS.config_server with
              | Some ch, Some cfg ->
                let selection = {
                  CS.server_selected_client_hello = ch;
                  CS.server_selected_cipher_suite =
                    T.TLS_CHACHA20_POLY1305_SHA256;
                  CS.server_selected_group = T.X25519;
                  CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                  CS.server_random = Ghost.reveal server_random;
                  CS.server_key_share_private =
                    Some (Ghost.reveal server_private_key);
                  CS.server_key_share_public =
                    CryptoSpec.x25519_public_from_private
                      (Ghost.reveal server_private_key);
                  CS.server_selected_credential =
                    cfg.CS.server_credential_identity;
                } in
                can_select_server_parameters st0 selection
              | _, _ -> False))

fn can_schedule_select_server_parameters_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            server_selection_absent st0.CS.cs_model.CS.model_handshake /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server)

fn can_schedule_derive_shared_secret_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
             | Some selection ->
               CS.server_selection_key_share_consistent selection /\
               st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                 Some selection.CS.server_selected_client_hello
             | None -> False))

fn can_send_server_hello_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
             | Some selection ->
               CS.server_selection_key_share_consistent selection /\
               Some? selection.CS.server_key_share_private
             | None -> False) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
              max_transcript_len)

fn can_receive_client_finished
  (c:connection_state)
  (#fin:erased GFin.finished)
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
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len /\
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
  (#ee:erased GEE.encryptedExtensions)
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
                  M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
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
               // Transcript-length bound for the Certificate flight.  The
               // handshake message serializes to exactly 13 + |chain| bytes
               // (TLS13.Impl.Server.Send.lemma_mk_cert_witness_bytesize) and the
               // runtime transcript-room check below guarantees it fits.  (The
               // legal_event (M.Certificate cert) obligation stays a caller
               // obligation, discharged with the build-direction witness.)
               B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 13 +
                 B.length cfg.CS.server_certificate_chain <= max_transcript_len
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
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            (let cv =
              Some?.v
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
             // Transcript-length bound for the CertificateVerify flight.  The
             // handshake message serializes to exactly 8 + |signature| bytes
             // (TLS13.Impl.Server.Send.lemma_serialize_handshake_certificate_verify_len)
             // and the runtime transcript-room check below guarantees it fits.
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 8 +
               B.length (Sem.certificateVerify_signature_bytes cv) <= max_transcript_len /\
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
  (#cert:erased GCert.certificate)
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
            (Sem.certificate_entries (Ghost.reveal cert)) <> [] /\
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
  (#cv:erased GCV.certificateVerify)
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
  (#fin:erased GFin.finished)
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
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len /\
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

fn client_finished_verify_data_matches
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientFinishedReceived /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
                  st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
             | Some fin, Some client_hs ->
              H.verify_finished
                client_hs.CS.traffic_secret
                (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                fin
             | _, _ -> False))

fn can_verify_client_finished_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
            // TODO-A1: Model.can_verify_client_finished bundles a transcript-length
            // conjunct `B.length transcript + B.length (serialize_handshake
            // (M.Finished fin)) <= max_transcript_len`, whose proof needed the
            // Phase-4-deleted W.lemma_serialize_finished_len (which gave
            // serialize_handshake (M.Finished fin) == 36).  That bound is no longer
            // provable for general generated finished records, so we expose the
            // remaining (provable) conjuncts of can_verify_client_finished here
            // instead of the bundled predicate.  (Only the out-of-scope
            // TLS13.Impl.Server.Schedule consumes this result.)
            (let fin = Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
             st0.CS.cs_model.CS.model_control ==
               CS.ControlHandshaking CS.HsClientFinishedReceived /\
             st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             CS.application_record_keys_installed_for_role
               CS.ServerEndpoint st0.CS.cs_model /\
             (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
              | Some stored_fin, Some client_hs ->
                stored_fin == fin /\
                H.verify_finished
                  client_hs.CS.traffic_secret
                  (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                  fin
              | _, _ -> False) /\
             CS.legal_event
               st0.CS.cs_model
               (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) /\
             // Transcript-length bound of CM.can_verify_client_finished: a
             // Finished handshake message serializes to exactly 36 bytes
             // (TLS13.Impl.Server.Send.lemma_serialize_handshake_finished_len);
             // the runtime transcript-room check below guarantees it fits.
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
               max_transcript_len))

fn server_application_record_keys_installed_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            CS.application_record_keys_installed_for_role
              CS.ServerEndpoint
              st0.CS.cs_model)

fn client_application_record_keys_installed_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            CS.application_record_keys_installed_for_role
              CS.ClientEndpoint
              st0.CS.cs_model)

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
            (match st0.CS.cs_model.CS.model_record.CS.record_write.R.key,
                   st0.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
             | Some _, Some _ -> True
             | _, _ -> False) /\
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
