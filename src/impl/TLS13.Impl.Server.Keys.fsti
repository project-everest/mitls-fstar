module TLS13.Impl.Server.Keys

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

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
                    (* See TLS13.Impl.Server.Types.server_local_event_input_ready:
                       the ECDH is group-indexed in the specification but this
                       implementation still runs it at X25519 only. *)
                    CS.server_selected_kex_group selection == CM.stored_client_hello_kex_group 'st0 /\
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
                    (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                     | Some selection ->
                       (match CS.client_hello_kex
                                selection.CS.server_selected_client_hello
                                (CS.server_selected_kex_group selection) with
                        | Some ch_ks ->
                          TLS13.Crypto.Spec.kex_shared
                            (CS.server_selected_kex_group selection)
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
