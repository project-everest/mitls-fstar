module TLS13.Impl.Server.Send

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U64 = FStar.UInt64
module U8 = FStar.UInt8

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

fn process_send_server_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v raw_len <= SZ.v network_out_len /\
                 Seq.equal
                    (Seq.slice (Ghost.reveal 'old_network_out) 0 (SZ.v raw_len))
                    (Ghost.reveal 'raw_bytes) /\
                 Seq.equal
                    (Ghost.reveal 'fragment_bytes)
                    (TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh)) /\
                 SZ.v fragment_len <= Bounds.max_server_hello_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello 'st0 sh (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello_serialized
  (s:server)
  (lsh:IM.server_hello)
  (#sh:erased M.server_hello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_server_hello lsh sh **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                Seq.equal
                  network_out_bytes
                  (CS.serialized_cleartext_tls_message
                    (M.TlsHandshake (M.ServerHello sh))) /\
                st1 ==
                  CM.sent_server_hello_state
                    'st0
                    sh
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendServerHello
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_hello_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 (let sh = {
                   M.random = Ghost.reveal 'server_random_bytes;
                   M.key_share = Ghost.reveal 'server_key_share_bytes;
                   M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                 } in
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (let sh = {
                    M.random = Ghost.reveal 'server_random_bytes;
                    M.key_share = Ghost.reveal 'server_key_share_bytes;
                    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                  } in
                  Seq.equal
                    network_out_bytes
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh))) /\
                  st1 ==
                    CM.sent_server_hello_state
                      'st0
                      sh
                      network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_server_hello_with_derived_public_from_private_array
  (s:server)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_private_key_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 95 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 (let sh = {
                   M.random = Ghost.reveal 'server_random_bytes;
                   M.key_share =
                     CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes);
                   M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                 } in
                 CM.can_send_server_hello
                   'st0
                   sh
                   (CS.serialized_cleartext_tls_message
                     (M.TlsHandshake (M.ServerHello sh)))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 ==>
                 (let sh = {
                    M.random = Ghost.reveal 'server_random_bytes;
                    M.key_share =
                      CryptoSpec.x25519_public_from_private
                        (Ghost.reveal 'server_private_key_bytes);
                    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                  } in
                  Seq.equal
                    network_out_bytes
                    (CS.serialized_cleartext_tls_message
                      (M.TlsHandshake (M.ServerHello sh))) /\
                  st1 ==
                    CM.sent_server_hello_state
                      'st0
                      sh
                      network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerHello
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_encrypted_extensions_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 28 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerHelloSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
                   Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake
                         (M.EncryptedExtensions { M.negotiated_alpn = None; M.body = B.empty });
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let ee = { M.negotiated_alpn = None } in
                 st1 ==
                   CM.sent_encrypted_extensions_state
                     'st0
                     ee
                     network_out_bytes) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendEncryptedExtensions
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn build_certificate_from_credentials
  (creds:O.server_credentials)
  requires O.is_server_credentials creds 'certificate_chain 'credential_identity
  returns result: option IM.certificate_msg
  ensures O.is_server_credentials creds 'certificate_chain 'credential_identity **
          (match result with
           | Some lcert ->
             IM.is_valid_certificate_msg
               lcert
               { M.chain = [Ghost.reveal 'certificate_chain] } **
             pure (
               SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
                 B.length (Ghost.reveal 'certificate_chain) /\
               lcert.IM.certificate_msg_cert_count == 1sz)
           | None ->
             pure (
               B.length (Ghost.reveal 'certificate_chain) >
                 IM.max_certificate_chain_bytes))

fn process_send_certificate_serialized
  (s:server)
  (lcert:IM.certificate_msg)
  (#cert:erased M.certificate_msg)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_msg lcert cert **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_from_credential
                       (Ghost.reveal cert)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 (Ghost.reveal cert).M.chain <> [] /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> CS.certificate_msg_matches_server_config cfg (Ghost.reveal cert)
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.Certificate (Ghost.reveal cert));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    (Ghost.reveal cert)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_from_credentials
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
                 Some?
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                  ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640 /\
                 SZ.v network_out_len ==
                  13 + B.length (Ghost.reveal 'certificate_chain) + 22 /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg -> cfg.CS.server_certificate_chain == Ghost.reveal 'certificate_chain
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  13 + B.length (Ghost.reveal 'certificate_chain) <=
                    Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value =
                      M.TlsHandshake
                        (M.Certificate { M.chain = [Ghost.reveal 'certificate_chain]; M.body = B.empty });
                  }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_state
                    'st0
                    { M.chain = [Ghost.reveal 'certificate_chain] }
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificate
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_certificate_verify_serialized
  (s:server)
  (lcv:IM.certificate_verify)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           IM.is_valid_certificate_verify lcv cv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                       (Ghost.reveal cv)) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                  | Some stored_cv -> stored_cv == Ghost.reveal cv
                  | None -> False) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                   SZ.v fragment_len <= Bounds.max_transcript_len /\
                 CS.legal_event
                   'st0.CS.cs_model
                   (CS.ConnNetworkEvent {
                     CL.message_direction = CL.Sent;
                     CL.message_value =
                       M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_stored_certificate_verify_serialized
  (s:server)
  (#cv:erased M.certificate_verify)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  SZ.v fragment_len ==
                    B.length
                      (TLS13.Wire.Spec.serialize_certificate_verify_from_signature
                        (Ghost.reveal cv)) /\
                  SZ.v fragment_len + 17 <= 16640 /\
                  SZ.v network_out_len == SZ.v fragment_len + 22 /\
                  ST.server_end_to_end_invariant 'st0 /\
                  'st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                  'st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                  Some?
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  U64.fits
                    ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    Some (Ghost.reveal cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    SZ.v fragment_len <= Bounds.max_transcript_len /\
                  CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnNetworkEvent {
                      CL.message_direction = CL.Sent;
                      CL.message_value =
                        M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
                    }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.sent_certificate_verify_state
                    'st0
                    (Ghost.reveal cv)
                    network_out_bytes /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSendCertificateVerify
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_send_server_finished_serialized
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 SZ.v network_out_len == 58 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                 U64.fits
                   ('st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (match
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic
                 with
                 | Some server_hs ->
                   let fin = {
                     M.verify_data =
                       K.finished_verify_data
                         server_hs.CS.traffic_secret
                         (Tr.hash
                           'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
                   } in
                   st1 ==
                     CM.sent_server_finished_state
                       'st0
                       fin
                       network_out_bytes
                 | None -> True) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendServerFinished
                  B.empty
                  network_out_bytes
                  app_out_bytes)
