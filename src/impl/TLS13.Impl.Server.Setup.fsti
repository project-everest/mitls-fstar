module TLS13.Impl.Server.Setup

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

fn process_start_server_local_event
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
                 kind == ST.LocalStartServer /\
                 Seq.equal (Ghost.reveal 'payload_bytes) B.empty /\
                 CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                st1 == CM.started_server_state 'st0 /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

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
                  // The runtime stores no group tag; since G2 stage S6.8d
                  // CR.server_selection_group_pinned records that the selected
                  // group is the one the stored ClientHello's accepted offer
                  // names, and the runtime reads it off the metadata box.
                  CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
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

fn process_select_server_parameters_with_private_from_array
  (s:server)
  (server_private_key:array U8.t)
  (#selection:erased CS.server_handshake_selection)
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
                  CM.can_select_server_parameters 'st0 selection /\
                  // The runtime stores no group tag; since G2 stage S6.8d
                  // CR.server_selection_group_pinned records that the selected
                  // group is the one the stored ClientHello's accepted offer
                  // names, and the runtime reads it off the metadata box.
                  CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
                  CR.server_selection_absent
                    'st0.CS.cs_model.CS.model_handshake /\
                  Some? selection.CS.server_key_share_private /\
                  Some?.v selection.CS.server_key_share_private ==
                    Ghost.reveal 'server_private_key_bytes)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to server_private_key 'server_private_key_bytes **
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
                    CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                    CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                    CS.server_selected_signature_scheme =
                      CryptoSpec.credential_signature_scheme
                        (cfg.CS.server_credential_identity);
                    CS.server_random = Ghost.reveal 'server_random_bytes;
                    CS.server_key_share_private = None;
                    CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                    CS.server_p256_private = None;
                    CS.server_p256_public = CS.server_p256_absent;
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
                      CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                      CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                      CS.server_selected_signature_scheme =
                        CryptoSpec.credential_signature_scheme
                          (cfg.CS.server_credential_identity);
                      CS.server_random = Ghost.reveal 'server_random_bytes;
                      CS.server_key_share_private = None;
                      CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                      CS.server_p256_private = None;
                      CS.server_p256_public = CS.server_p256_absent;
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
                   CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                   CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                   CS.server_selected_signature_scheme =
                     CryptoSpec.credential_signature_scheme
                       (cfg.CS.server_credential_identity);
                   CS.server_random = Ghost.reveal 'server_random_bytes;
                   CS.server_key_share_private =
                     Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                   CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_p256_public =
                     CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
                     CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                     CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                     CS.server_selected_signature_scheme =
                       CryptoSpec.credential_signature_scheme
                         (cfg.CS.server_credential_identity);
                     CS.server_random = Ghost.reveal 'server_random_bytes;
                     CS.server_key_share_private =
                       Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_key_share_public = Ghost.reveal 'server_key_share_bytes;
                     CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_p256_public =
                       CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
                   CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                   CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                   CS.server_selected_signature_scheme =
                     CryptoSpec.credential_signature_scheme
                       (cfg.CS.server_credential_identity);
                   CS.server_random = Ghost.reveal 'server_random_bytes;
                   CS.server_key_share_private =
                     Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_key_share_public =
                     CryptoSpec.x25519_public_from_private
                       (Ghost.reveal 'server_private_key_bytes);
                   CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                   CS.server_p256_public =
                     CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
                     CS.server_selected_cipher_suite = CM.server_selected_suite 'st0;
                     CS.server_selected_group = CM.named_group_of_kex_group (CM.client_hello_kex_group_for (ch));
                     CS.server_selected_signature_scheme =
                       CryptoSpec.credential_signature_scheme
                         (cfg.CS.server_credential_identity);
                     CS.server_random = Ghost.reveal 'server_random_bytes;
                     CS.server_key_share_private =
                       Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_key_share_public =
                       CryptoSpec.x25519_public_from_private
                         (Ghost.reveal 'server_private_key_bytes);
                     CS.server_p256_private = Some (Ghost.reveal 'server_private_key_bytes);
                     CS.server_p256_public =
                       CryptoSpec.p256_public_from_private (Ghost.reveal 'server_private_key_bytes);
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
