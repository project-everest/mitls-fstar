module TLS13.Impl.Server

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CryptoSpec = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module M = TLS13.Messages
module O = TLS13.OpenSSL
module R = TLS13.Record.Spec
module SM = TLS13.Spec.StateMachine.ClientTrace
module ST = TLS13.Impl.Server.Types
module Tr = TLS13.Transcript
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GSHbody = TLS13.Wire.Generated.ServerHello_body
module GCS = TLS13.Wire.Generated.CipherSuite
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module SS = TLS13.Impl.Server.Send

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

noextract
let server_state_ref (s:server) : CR.state_ref =
  CR.connection_state_ref s

noextract
let next_local_action_sound = ST.next_local_action_sound

noextract
let server_local_event_input_ready = ST.server_local_event_input_ready

noextract
let server_local_event_input_ready_with_credentials
  = ST.server_local_event_input_ready_with_credentials

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (credential_identity:array U8.t)
  (credential_identity_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to credential_identity 'credential_identity_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'credential_identity_bytes == SZ.v credential_identity_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns s:server
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to credential_identity 'credential_identity_bytes **
          connection_exactly
            s
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal 'credential_identity_bytes)) **
          pure (ST.server_state_correct
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_end_to_end_invariant
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                ST.server_raw_to_message_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_protected_raw_segmented_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)) /\
                // The constructed initial state satisfies the server-config
                // validity predicate consumed as an ENTRY HYPOTHESIS by the
                // system-level stream-integrity theorem.  Establishing it here
                // is what turns that hypothesis from an assumption about the
                // starting state into a proved property of the state this
                // implementation actually builds.
                CR.server_config_valid
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal 'credential_identity_bytes)))

fn new_server_erased_credential_identity
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (#credential_identity:erased CS.server_credential_identity)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns s:server
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          connection_exactly
            s
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              (Ghost.reveal credential_identity)) **
          pure (ST.server_state_correct
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                ST.server_end_to_end_invariant
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                ST.server_raw_to_message_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                TLS13.Spec.StateMachine.Replay.connection_state_protected_raw_segmented_replay_consistent
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)) /\
                // See `new_server`: the stream-integrity entry hypothesis, proved
                // rather than assumed.
                CR.server_config_valid
                  (CR.server_initial_state
                    (Ghost.reveal 'certificate_chain_bytes)
                    (Ghost.reveal credential_identity)))

fn next_local_action
  (s:server)
  requires connection_exactly s 'st0 **
           pure (ST.server_state_correct 'st0)
  returns action:ST.next_local_action
  ensures connection_exactly s 'st0 **
          pure (ST.server_state_correct 'st0 /\
                next_local_action_sound 'st0 action)

fn process_select_server_parameters
  (s:server)
  (#selection:erased CS.server_handshake_selection)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                  B.length 'old_app_out == SZ.v app_out_len /\
                  ST.server_end_to_end_invariant 'st0 /\
                  CM.can_select_server_parameters 'st0 selection /\
                  CR.server_selection_absent
                    'st0.CS.cs_model.CS.model_handshake /\
                  CR.server_selection_private_absent selection)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.selected_server_parameters_state
                    'st0
                    (Ghost.reveal selection) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalSelectServerParameters
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_select_default_server_parameters_from_arrays
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
                 ST.server_end_to_end_invariant 'st0 /\
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                    Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                    Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                    CS.server_selected_client_hello = ch;
                    CS.server_selected_cipher_suite =
                      (CM.server_selected_suite 'st0);
                    CS.server_selected_group = T.X25519;
                    CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private = None;
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_selected_credential =
                      cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
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
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    let selection = {
                      CS.server_selected_client_hello = ch;
                      CS.server_selected_cipher_suite =
                        (CM.server_selected_suite 'st0);
                      CS.server_selected_group = T.X25519;
                      CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private = None;
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_selected_credential =
                        cfg.CS.server_credential_identity;
                    } in
                    st1 == CM.selected_server_parameters_state 'st0 selection
                  | _ -> True)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSelectServerParameters
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_select_default_server_parameters_with_private_from_arrays
  (s:server)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  (server_key_share:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_random 'server_random_bytes **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to server_key_share 'server_key_share_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_random_bytes == 32 /\
                 B.length 'server_private_key_bytes == 32 /\
                 B.length 'server_key_share_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CR.server_selection_absent
                   'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                    Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                    Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                    CS.server_selected_client_hello = ch;
                    CS.server_selected_cipher_suite =
                      (CM.server_selected_suite 'st0);
                    CS.server_selected_group = T.X25519;
                    CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private =
                      Some (Ghost.reveal 'server_private_key_bytes);
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_selected_credential =
                      cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_random 'server_random_bytes **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to server_key_share 'server_key_share_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (B.length (Ghost.reveal 'server_random_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_private_key_bytes) == 32 /\
                 B.length (Ghost.reveal 'server_key_share_bytes) == 32 ==>
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    let selection = {
                      CS.server_selected_client_hello = ch;
                      CS.server_selected_cipher_suite =
                        (CM.server_selected_suite 'st0);
                      CS.server_selected_group = T.X25519;
                      CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private =
                        Some (Ghost.reveal 'server_private_key_bytes);
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_selected_credential =
                        cfg.CS.server_credential_identity;
                    } in
                    st1 == CM.selected_server_parameters_state 'st0 selection
                  | _ -> True)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSelectServerParameters
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_select_default_server_parameters_with_derived_public_from_private_array
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
                 ST.server_end_to_end_invariant 'st0 /\
                 CR.server_selection_absent
                  'st0.CS.cs_model.CS.model_handshake /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (let ch =
                   Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
                  let cfg =
                   Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server in
                  let selection = {
                   CS.server_selected_client_hello = ch;
                   CS.server_selected_cipher_suite =
                     (CM.server_selected_suite 'st0);
                   CS.server_selected_group = T.X25519;
                   CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                   CS.server_random = Ghost.reveal 'server_random_bytes;
                   CS.server_key_share_private =
                     Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_key_share_public =
                     CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes);
                   CS.server_selected_credential =
                     cfg.CS.server_credential_identity;
                  } in
                  CM.can_select_server_parameters 'st0 selection))
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
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                       'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                   let selection = {
                     CS.server_selected_client_hello = ch;
                     CS.server_selected_cipher_suite =
                       (CM.server_selected_suite 'st0);
                     CS.server_selected_group = T.X25519;
                     CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                     CS.server_random = Ghost.reveal 'server_random_bytes;
                     CS.server_key_share_private =
                       Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_key_share_public =
                       CryptoSpec.x25519_public_from_private
                         (Ghost.reveal 'server_private_key_bytes);
                     CS.server_selected_credential =
                       cfg.CS.server_credential_identity;
                   } in
                   st1 == CM.selected_server_parameters_state 'st0 selection
                  | _ -> True)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSelectServerParameters
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_send_server_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lsh:IM.server_hello)
  (#sh:erased GSH.serverHello)
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
  (sid_len:SZ.t)
  (#sh:erased GSH.serverHello)
  (#server_random_bytes: erased B.bytes)
  (#server_key_share_bytes: erased B.bytes)
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
                 SZ.v network_out_len ==
                   95 + Seq.length (CM.stored_client_hello_session_id 'st0) /\
                 SZ.v sid_len ==
                   Seq.length (CM.stored_client_hello_session_id 'st0) /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 Seq.length (Ghost.reveal server_random_bytes) == 32 /\
                 (Ghost.reveal server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst /\
                 Seq.length (Ghost.reveal server_key_share_bytes) == 32 /\
                 Ghost.reveal sh ==
                   SS.mk_server_hello_witness
                     (Ghost.reveal server_random_bytes)
                     (Ghost.reveal server_key_share_bytes)
                     (CM.stored_client_hello_session_id 'st0)
                     (CM.server_selected_suite 'st0) /\
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
                 SZ.v network_out_len ==
                   95 + Seq.length (CM.stored_client_hello_session_id 'st0) /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = SS.mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
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
                 (let sh = SS.mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (Ghost.reveal 'server_key_share_bytes) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
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
                 SZ.v network_out_len ==
                   95 + Seq.length (CM.stored_client_hello_session_id 'st0) /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 // TODO-A1: ServerHello random must differ from the HelloRetryRequest
                 // sentinel (serverHello_body_cst); unprovable for a symbolic random,
                 // so threaded as an explicit caller obligation.
                 (Seq.length (Ghost.reveal 'server_random_bytes) == 32 ==>
                  (Ghost.reveal 'server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                 (let sh = SS.mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
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
                 (let sh = SS.mk_server_hello_witness (Ghost.reveal 'server_random_bytes) (CryptoSpec.x25519_public_from_private
                        (Ghost.reveal 'server_private_key_bytes)) (CM.stored_client_hello_session_id 'st0) (CM.server_selected_suite 'st0) in
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
                         (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
                   }))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (let ee = ([] <: GEE.encryptedExtensions) in
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

fn process_send_certificate_serialized
  (s:server)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (#chain:erased B.bytes)
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
                 1 <= Seq.length (Ghost.reveal chain) /\
                 Seq.length (Ghost.reveal chain) <= 32768 /\
                 Ghost.reveal cert == SS.mk_cert_witness (Ghost.reveal chain) /\
                 SZ.v fragment_len ==
                   B.length
                     (TLS13.Wire.Spec.serialize_handshake (M.Certificate (Ghost.reveal cert))) /\
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
                 lcert.IM.certificate_msg_cert_count == 1sz /\
                 (exists (certificate:B.bytes).
                   Sem.certificate_entries (Ghost.reveal cert) == [certificate]) /\
                 Sem.certificate_entries (Ghost.reveal cert) <> [] /\
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
                 // TODO-A1: chain length bound not exposed by O.is_server_credentials;
                 // needed because mk_cert_witness's Sem.certificate_entries postcondition is conditional
                 // on 1 <= |chain| <= 32768.
                 1 <= B.length (Ghost.reveal 'certificate_chain) /\
                 B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
                 // TODO-A1: |serialize_handshake (Certificate cert)| == 13 + |chain| was provided
                 // by the now-deleted W.lemma_serialize_certificate_from_single_chain_len; threaded
                 // as a precondition.
                 B.length (TLS13.Wire.Spec.serialize_handshake
                  (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                  13 + B.length (Ghost.reveal 'certificate_chain) /\
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
                        (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)));
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
                    (SS.mk_cert_witness (Ghost.reveal 'certificate_chain))
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
  (#cv:erased GCV.certificateVerify)
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
                     (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                 SZ.v fragment_len + 17 <= 16640 /\
                 SZ.v network_out_len == SZ.v fragment_len + 22 /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
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
  (#cv:erased GCV.certificateVerify)
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
                      (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))) /\
                  SZ.v fragment_len + 17 <= 16640 /\
                  SZ.v network_out_len == SZ.v fragment_len + 22 /\
                  ST.server_end_to_end_invariant 'st0 /\
                  'st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                  'st0.CS.cs_model.CS.model_config.CS.config_role ==
                    CS.ServerEndpoint /\
                  'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
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
                   let fin = ((K.finished_verify_data
                         server_hs.CS.traffic_secret
                         (Tr.hash
                           'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)) <: GFin.finished) in
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

fn process_derive_shared_secret
  (s:server)
  (shared_src:array U8.t)
  (#shared:erased TLS13.Crypto.Spec.x25519_shared_secret)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to shared_src shared **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length (Ghost.reveal shared) == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalDeriveSharedSecret (Ghost.reveal shared))))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to shared_src shared **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.derived_shared_secret_state
                    'st0
                    (Ghost.reveal shared) /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalDeriveSharedSecret
                   (Ghost.reveal shared)
                   network_out_bytes
                   app_out_bytes)

fn process_derive_shared_secret_from_private_array
  (s:server)
  (server_private_key:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to server_private_key 'server_private_key_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'server_private_key_bytes == 32 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientHelloReceived /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
                   None /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    CS.server_selection_key_share_consistent selection /\
                    'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                      Some selection.CS.server_selected_client_hello /\
                    Some? selection.CS.server_key_share_private /\
                    Some?.v selection.CS.server_key_share_private ==
                      Ghost.reveal 'server_private_key_bytes
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_private_key 'server_private_key_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalDeriveSharedSecret
                  (Ghost.reveal 'server_private_key_bytes)
                  network_out_bytes
                  app_out_bytes /\
                (resp.ST.status == ST.StepOk ==>
                  (exists shared.
                    st1 == CM.derived_shared_secret_state 'st0 shared /\
                    (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
                     | Some ch ->
                       (match CS.client_hello_key_share ch with
                        | Some ch_ks ->
                          TLS13.Crypto.Spec.x25519_shared
                            (Ghost.reveal 'server_private_key_bytes)
                            ch_ks == Some shared
                        | None -> False)
                     | None -> False))) /\
                (resp.ST.status == ST.IllegalTransition ==>
                  ST.unexpected_message_response
                    'st0
                    st1
                    resp
                    network_out_bytes
                    app_out_bytes))

fn process_install_server_handshake_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                    'st0.CS.cs_model
                    (CS.ConnLocalEvent
                      (CS.LocalInstallTrafficKeysForRole {
                        CS.install_role = CS.ServerEndpoint;
                        CS.install_payload = {
                          CS.install_epoch = CS.TrafficHandshake;
                          CS.install_direction = CS.TrafficWrite;
                          CS.install_material = Ghost.reveal material;
                        };
                      })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                   'st0
                   st1
                   resp
                   ST.LocalInstallServerHandshakeTrafficKeys
                   B.empty
                   network_out_bytes
                   app_out_bytes)

fn process_derive_and_install_server_handshake_write_keys
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
                   ST.server_end_to_end_invariant 'st0 /\
                   'st0.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsServerHelloSent /\
                   'st0.CS.cs_model.CS.model_config.CS.config_role ==
                     CS.ServerEndpoint /\
                   Some?
                     'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     (CM.installed_traffic_keys_for_role_state 'st0 {
                       CS.install_role = CS.ServerEndpoint;
                       CS.install_payload = {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       };
                     })
                     resp
                     ST.LocalInstallServerHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)

fn process_install_client_handshake_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                   B.length 'old_app_out == SZ.v app_out_len /\
                   ST.server_end_to_end_invariant 'st0 /\
                   CS.legal_event
                      'st0.CS.cs_model
                      (CS.ConnLocalEvent
                        (CS.LocalInstallTrafficKeysForRole {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficHandshake;
                            CS.install_direction = CS.TrafficRead;
                            CS.install_material = Ghost.reveal material;
                          };
                        })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficHandshake;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                     'st0
                     st1
                     resp
                     ST.LocalInstallClientHandshakeTrafficKeys
                     B.empty
                     network_out_bytes
                     app_out_bytes)

fn process_derive_and_install_client_handshake_read_keys
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
                     ST.server_end_to_end_invariant 'st0 /\
                     'st0.CS.cs_model.CS.model_control ==
                       CS.ControlHandshaking CS.HsServerHelloSent /\
                     'st0.CS.cs_model.CS.model_config.CS.config_role ==
                       CS.ServerEndpoint /\
                     Some?
                       'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       (CM.installed_traffic_keys_for_role_state 'st0 {
                         CS.install_role = CS.ServerEndpoint;
                         CS.install_payload = {
                           CS.install_epoch = CS.TrafficHandshake;
                           CS.install_direction = CS.TrafficRead;
                           CS.install_material = material;
                         };
                       })
                       resp
                       ST.LocalInstallClientHandshakeTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_install_server_application_write_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficWrite;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallServerApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_install_client_application_read_keys
  (s:server)
  (traffic_secret_src:array U8.t)
  (traffic_key_src:array U8.t)
  (traffic_iv_src:array U8.t)
  (#material:erased CS.traffic_key_material)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to traffic_secret_src material.CS.traffic_secret **
           pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
           pts_to traffic_iv_src material.CS.traffic_iv **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CS.legal_event
                        'st0.CS.cs_model
                        (CS.ConnLocalEvent
                          (CS.LocalInstallTrafficKeysForRole {
                            CS.install_role = CS.ServerEndpoint;
                            CS.install_payload = {
                              CS.install_epoch = CS.TrafficApplication;
                              CS.install_direction = CS.TrafficRead;
                              CS.install_material = Ghost.reveal material;
                            };
                          })))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to traffic_secret_src material.CS.traffic_secret **
          pts_to traffic_key_src (TLS13.Crypto.Spec.pad_key_32 material.CS.traffic_key) **
          pts_to traffic_iv_src material.CS.traffic_iv **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.installed_traffic_keys_for_role_state 'st0 {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = Ghost.reveal material;
                    };
                  } /\
                ST.server_local_event_end_to_end_correct
                       'st0
                       st1
                       resp
                       ST.LocalInstallClientApplicationTrafficKeys
                       B.empty
                       network_out_bytes
                       app_out_bytes)

fn process_derive_and_install_server_application_write_keys
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
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerFinishedSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.installed_traffic_keys_for_role_state 'st0 {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficApplication;
                            CS.install_direction = CS.TrafficWrite;
                            CS.install_material = material;
                          };
                        })
                        resp
                        ST.LocalInstallServerApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_derive_and_install_client_application_read_keys
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
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsClientFinishedReceived /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes material.
          connection_exactly
            s
            (CM.installed_traffic_keys_for_role_state 'st0 {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            }) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.installed_traffic_keys_for_role_state 'st0 {
                          CS.install_role = CS.ServerEndpoint;
                          CS.install_payload = {
                            CS.install_epoch = CS.TrafficApplication;
                            CS.install_direction = CS.TrafficRead;
                            CS.install_material = material;
                          };
                        })
                        resp
                        ST.LocalInstallClientApplicationTrafficKeys
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_send_application_data_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_application_data_state
                        'st0
                        (Ghost.reveal 'payload_bytes)
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_send_close_notify_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_local_event_input_ready
                   'st0
                   ST.LocalSendCloseNotify
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_close_notify_state
                        'st0
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCloseNotify
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_send_key_update_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (req:M.key_update_request)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 ((kind == ST.LocalSendKeyUpdate /\ req == M.UpdateNotRequested) \/
                  (kind == ST.LocalSendKeyUpdateRequested /\ req == M.UpdateRequested)) /\
                 server_local_event_input_ready
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.server_sent_key_update_state
                        'st0
                        req
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_verify_client_finished
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
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                 // TODO-A1: transcript+36 bound (was derived from the deleted
                 // W.lemma_serialize_finished_len) threaded as explicit precondition.
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len /\
                 CM.can_verify_client_finished
                   'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes fin.
          connection_exactly
           s
           (CM.verified_client_finished_state 'st0 fin) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                  Some fin /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.verified_client_finished_state 'st0 fin)
                        resp
                        ST.LocalVerifyClientFinished
                        B.empty
                        network_out_bytes
                        app_out_bytes)

fn process_sign_certificate_verify
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
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    selection.CS.server_selected_signature_scheme ==
                      T.Rsa_pss_rsae_sha256 /\
                    selection.CS.server_selected_credential ==
                      Ghost.reveal 'credential_identity /\
                    CS.signature_scheme_offered
                      'st0.CS.cs_model.CS.model_config.CS.config_signature_schemes
                      T.Rsa_pss_rsae_sha256
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSignCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)

fn process_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 // TODO-A1: CM.can_verify_client_finished bundles an abstract
                 // transcript+|serialize_handshake (Finished fin)| conjunct that is not
                 // provable from server_local_event_input_ready alone (deleted
                 // W.lemma_serialize_finished_len); threaded as explicit caller obligation.
                 // The additional transcript+36 bound is required by Auth's wrapper.
                 (kind == ST.LocalVerifyClientFinished /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    Bounds.max_transcript_len /\
                  CM.can_verify_client_finished 'st0
                    (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
                 // TODO-A1: server_local_event_input_ready weakened can_send_server_hello
                 // to True (no GSH.serverHello witness builder in Model yet).  The
                 // cst-guard (random != HelloRetryRequest sentinel) is also unresolvable
                 // for a symbolic random.  Both threaded as explicit caller obligation.
                 (kind == ST.LocalSendServerHello /\
                  SZ.v network_out_len ==
                    95 + Seq.length (CM.stored_client_hello_session_id 'st0) ==>
                  (let server_random_bytes = CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 in
                   let server_private_key_bytes = CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64 in
                   (Seq.length server_random_bytes == 32 ==>
                    (server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                   (let sh = SS.mk_server_hello_witness server_random_bytes
                      (CryptoSpec.x25519_public_from_private server_private_key_bytes)
                      (CM.stored_client_hello_session_id 'st0)
                      (CM.server_selected_suite 'st0) in
                    CM.can_send_server_hello 'st0 sh
                      (CS.serialized_cleartext_tls_message
                        (M.TlsHandshake (M.ServerHello sh)))))) /\
                 // TODO-A1: server_local_event_input_ready weakened the CV
                 // transcript-length bound to True, and the deleted
                 // lemma_serialize_certificate_verify_from_signature_len provided the
                 // serialize-length equation; both threaded as explicit caller obligation.
                 (kind == ST.LocalSendCertificateVerify /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
                  (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                   B.length (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify cv)) ==
                     8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                   B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                     B.length (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify cv)) <=
                     Bounds.max_transcript_len)) /\
                 server_local_event_input_ready
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
               B.length app_out_bytes == SZ.v app_out_len /\
               ST.server_local_event_end_to_end_correct
                 'st0
                 st1
                 resp
                 kind
                 (Ghost.reveal 'payload_bytes)
                 network_out_bytes
                 app_out_bytes)

fn process_local_event_with_credentials
  (s:server)
  (creds:O.server_credentials)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                ST.server_end_to_end_invariant 'st0 /\
                // TODO-A1: CM.can_verify_client_finished bundles an abstract
                // transcript+|serialize_handshake (Finished fin)| conjunct that is not
                // provable from server_local_event_input_ready alone (deleted
                // W.lemma_serialize_finished_len); threaded as explicit caller obligation.
                // The additional transcript+36 bound is required by Auth's wrapper.
                (kind == ST.LocalVerifyClientFinished /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len /\
                 CM.can_verify_client_finished 'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
                // TODO-A1: server_local_event_input_ready weakened can_send_server_hello
                // to True (no GSH.serverHello witness builder in Model yet).  The
                // cst-guard (random != HelloRetryRequest sentinel) is also unresolvable
                // for a symbolic random.  Both threaded as explicit caller obligation.
                (kind == ST.LocalSendServerHello /\
                  SZ.v network_out_len ==
                    95 + Seq.length (CM.stored_client_hello_session_id 'st0) ==>
                 (let server_random_bytes = CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 in
                  let server_private_key_bytes = CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64 in
                  (Seq.length server_random_bytes == 32 ==>
                   (server_random_bytes <: Seq.lseq U8.t 32) <> GSHbody.serverHello_body_cst) /\
                  (let sh = SS.mk_server_hello_witness server_random_bytes
                     (CryptoSpec.x25519_public_from_private server_private_key_bytes)
                     (CM.stored_client_hello_session_id 'st0)
                     (CM.server_selected_suite 'st0) in
                   CM.can_send_server_hello 'st0 sh
                     (CS.serialized_cleartext_tls_message
                       (M.TlsHandshake (M.ServerHello sh)))))) /\
                // TODO-A1: server_local_event_input_ready weakened the CV
                // transcript-length bound to True, and the deleted
                // lemma_serialize_certificate_verify_from_signature_len provided the
                // serialize-length equation; both threaded as explicit caller obligation.
                (kind == ST.LocalSendCertificateVerify /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
                 (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                  B.length (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify cv)) ==
                    8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    B.length (TLS13.Wire.Spec.serialize_handshake (M.CertificateVerify cv)) <=
                    Bounds.max_transcript_len)) /\
                // TODO-A1: chain length bounds (1 <= .. <= 32768) needed by
                // build_certificate_from_credentials (mk_cert_witness's
                // Sem.certificate_entries postcondition is conditional).
                // Also, the deleted lemma_serialize_certificate_from_single_chain_len
                // provided the serialize-handshake-cert length equation.
                (kind == ST.LocalSendCertificate ==>
                 1 <= B.length (Ghost.reveal 'certificate_chain) /\
                 B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
                 B.length (TLS13.Wire.Spec.serialize_handshake
                   (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                   13 + B.length (Ghost.reveal 'certificate_chain)) /\
                server_local_event_input_ready_with_credentials
                  'st0
                  kind
                  (Ghost.reveal 'payload_bytes)
                  (Ghost.reveal 'certificate_chain)
                  (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_client_hello
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (lch:IM.client_hello)
  (#ch:erased GCH.clientHello)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           IM.is_valid_client_hello lch ch **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 SZ.v fragment_len <= Bounds.max_client_hello_len /\
                 Seq.equal
                  (Ghost.reveal 'fragment_bytes)
                  (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) /\
                 lch.IM.client_hello_has_server_name == CM.client_hello_has_sni ch /\
                 (lch.IM.client_hello_has_server_name ==>
                    CM.client_hello_server_name_len_for ch ==
                      lch.IM.client_hello_server_name_len) /\
                 CM.client_hello_cipher_suites_len_for ch ==
                  lch.IM.client_hello_cipher_suites_len /\
                 CM.client_hello_signature_schemes_len_for ch ==
                  lch.IM.client_hello_signature_schemes_len /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  B.length (TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch)) <=
                  Bounds.max_transcript_len /\
                 CS.legal_event
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                 CS.event_raw_delta_legal
                  'st0.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  (Ghost.reveal 'raw_bytes))
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
                  CM.received_client_hello_state
                    'st0
                    (Ghost.reveal ch)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.ClientHello ch))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_client_finished
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (lfin:IM.finished)
  (#fin:erased GFin.finished)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           IM.is_valid_finished lfin fin **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 CM.can_receive_client_finished
                   'st0
                   (Ghost.reveal fin)
                   (Ghost.reveal 'raw_bytes) /\
                 TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
                   'st0.CS.cs_model
                   (ST.received_message_event
                     (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
                   (Ghost.reveal 'raw_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 ==
                  CM.received_client_finished_state
                    'st0
                    (Ghost.reveal fin)
                    (Ghost.reveal 'raw_bytes) /\
                ST.server_network_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  (M.TlsHandshake (M.Finished (Ghost.reveal fin)))
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_network_bytes
  (s:server)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns buffer_resp:ST.server_buffer_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_network_bytes_end_to_end_correct
                  'st0
                  st1
                  buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes /\
                ST.server_network_consumed_input_projection
                   'st0
                   st1
                   buffer_resp
                   (Ghost.reveal 'raw_bytes)
                   network_out_bytes
                   app_out_bytes /\
                (buffer_resp.ST.response.ST.status == ST.NeedMoreInput ==>
                  W.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
                  W.parse_record_wire (Ghost.reveal 'raw_bytes) == None /\
                  Seq.equal network_out_bytes (Ghost.reveal 'old_network_out) /\
                  Seq.equal app_out_bytes (Ghost.reveal 'old_app_out)) /\
                 (buffer_resp.ST.response.ST.status == ST.StepOk ==>
                  0 < SZ.v buffer_resp.ST.consumed_len))
