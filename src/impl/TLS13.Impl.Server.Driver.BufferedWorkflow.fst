module TLS13.Impl.Server.Driver.BufferedWorkflow

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module CS = TLS13.Spec.StateMachine
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module DS = TLS13.Impl.Server.Driver.State
module BH = TLS13.Impl.Server.Driver.BufferedHandshake
module BL = TLS13.Impl.Server.Driver.BufferedLocal
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module SP = TLS13.Impl.Server.CanonicalProtocol
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SS = TLS13.Impl.Server.Send
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module M = TLS13.Messages

fn control_snapshot
  (d:DS.buffered_driver)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len
  returns snapshot:CR.control_snapshot
  ensures
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pure (CR.control_snapshot_matches snapshot 'st0)
{
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  rewrite
    (S.connection_exactly d.DS.buffered_driver_server 'st0)
    as
    (CR.connection_exactly d.DS.buffered_driver_server 'st0);
  let snapshot =
    CQ.get_control_snapshot d.DS.buffered_driver_server;
  rewrite
    (CR.connection_exactly d.DS.buffered_driver_server 'st0)
    as
    (S.connection_exactly d.DS.buffered_driver_server 'st0);
  fold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  fold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  snapshot
}

fn selection_ready
  (d:DS.buffered_driver)
  (#server_random:erased (b:B.bytes{B.length b == 32}))
  (#server_private_key:erased (b:B.bytes{B.length b == 32}))
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pure (
      'st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived)
  returns ready:bool
  ensures
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pure (
      ready ==>
      CR.server_selection_absent
        'st0.CS.cs_model.CS.model_handshake /\
      'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        None /\
      Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
      Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
      (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
             'st0.CS.cs_model.CS.model_config.CS.config_server with
       | Some ch, Some cfg ->
         CM.can_select_server_parameters 'st0 {
           CS.server_selected_client_hello = ch;
           CS.server_selected_cipher_suite =
             T.TLS_CHACHA20_POLY1305_SHA256;
           CS.server_selected_group = T.X25519;
           CS.server_selected_signature_scheme =
             T.Rsa_pss_rsae_sha256;
           CS.server_random = Ghost.reveal server_random;
           CS.server_key_share_private =
             Some (Ghost.reveal server_private_key);
           CS.server_key_share_public =
             CryptoSpec.x25519_public_from_private
               (Ghost.reveal server_private_key);
           CS.server_selected_credential =
             cfg.CS.server_credential_identity;
         }
       | _, _ -> False))
{
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_canonical_progress d 'st0);
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal d.DS.buffered_driver_initial)
    'st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
    'st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
    'st0));
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal d.DS.buffered_driver_initial)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  (Ghost.reveal
    (DS.buffered_driver_canonical d).SP.canonical_server_supported_profile)
    'st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
    'st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  fold (DS.buffered_driver_canonical_progress d 'st0);
  assert (pure (Some? 'st0.CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (
    match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
          'st0.CS.cs_model.CS.model_config.CS.config_server with
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
      CS.sni_policy_accepts
        cfg.CS.server_sni_policy
        (TLS13.Wire.Semantics.clientHello_server_name ch)
    | _, _ -> True));
  rewrite
    (S.connection_exactly d.DS.buffered_driver_server 'st0)
    as
    (CR.connection_exactly d.DS.buffered_driver_server 'st0);
  let ready =
    CQ.can_select_supported_server_parameters_runtime
      d.DS.buffered_driver_server
      #server_random
      #server_private_key;
  rewrite
    (CR.connection_exactly d.DS.buffered_driver_server 'st0)
    as
    (S.connection_exactly d.DS.buffered_driver_server 'st0);
  fold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  fold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  ready
}

fn rec drive_handshake
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (material_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (buffered_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to material_payload 'material_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'empty_payload_bytes == 0 /\
      B.length 'material_bytes == SZ.v DS.driver_material_capacity /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      network_out_len == DS.driver_network_out_capacity /\
      app_out_len == DS.driver_app_out_capacity)
  returns result:handshake_result
  ensures
    exists* st1 buffered_after material_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.handshake_pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to material_payload material_after **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.handshake_pending_len /\
        B.length material_after == SZ.v DS.driver_material_capacity /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        (result.handshake_status == HandshakeOk ==>
         st1.CS.cs_model.CS.model_control == CS.ControlApplicationData))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    {
      handshake_status = HandshakeExhausted;
      handshake_pending_len = buffered_len;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let snapshot = control_snapshot d;
    let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
    if app_ready {
      assert (pure (CR.control_snapshot_matches snapshot 'st0));
      assert (pure (
        'st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
      {
        handshake_status = HandshakeOk;
        handshake_pending_len = buffered_len;
      }
    } else {
      let failed = snapshot.CR.snapshot_control_tag = 5uy;
      if failed {
        {
          handshake_status = HandshakeStepFailed;
          handshake_pending_len = buffered_len;
        }
      } else {
        let client_hello_ready =
          (snapshot.CR.snapshot_control_tag = 1uy) &&
          (snapshot.CR.snapshot_handshake_stage_tag = 13uy);
        if client_hello_ready {
          assert (pure (CR.control_snapshot_matches snapshot 'st0));
          assert (pure (
            'st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived));
          let material_ok =
            Crypto.random_bytes
              material_payload
              DS.driver_material_capacity;
          with material_bytes.
            assert (pts_to material_payload material_bytes);
          if material_ok {
            assert (pure (B.length material_bytes == 64));
            Seq.lemma_len_slice material_bytes 0 32;
            Seq.lemma_len_slice material_bytes 32 64;
            let server_random : erased (b:B.bytes{B.length b == 32}) =
              Ghost.hide (TLS13.ConnectionLog.raw_slice material_bytes 0 32);
            let server_private_key : erased (b:B.bytes{B.length b == 32}) =
              Ghost.hide (TLS13.ConnectionLog.raw_slice material_bytes 32 64);
            let ready =
              selection_ready
                d
                #server_random
                #server_private_key;
            if ready {
              Seq.lemma_eq_elim
                (Ghost.reveal server_random)
                (TLS13.ConnectionLog.raw_slice material_bytes 0 32);
              Seq.lemma_eq_elim
                (Ghost.reveal server_private_key)
                (TLS13.ConnectionLog.raw_slice material_bytes 32 64);
              BH.lemma_select_server_parameters_input_ready_intro
                'st0
                material_bytes
                (Ghost.reveal server_random)
                (Ghost.reveal server_private_key);
              let differs =
                SS.server_random_differs_from_cst material_payload;
              if differs {
                SS.lemma_mk_server_hello_witness_bytesize
                  (TLS13.ConnectionLog.raw_slice material_bytes 0 32)
                  (CryptoSpec.x25519_public_from_private
                    (TLS13.ConnectionLog.raw_slice material_bytes 32 64))
                  (CM.stored_client_hello_session_id 'st0)
                  T.TLS_CHACHA20_POLY1305_SHA256;
                let flight =
                  BH.select_derive_send_server_hello_from_payload_once
                    d
                    material_payload
                    DS.driver_material_capacity
                    network_out
                    network_out_len
                    app_out
                    app_out_len;
                match flight {
                  BH.ServerFlightOk -> {
                    let next_fuel = SZ.sub fuel 1sz;
                    assert (pure (SZ.v next_fuel < SZ.v fuel));
                    drive_handshake
                      d
                      empty_payload
                      material_payload
                      network_out
                      network_out_len
                      app_out
                      app_out_len
                      buffered_len
                      local_fuel
                      next_fuel
                  }
                  _ -> {
                    {
                      handshake_status = HandshakeStepFailed;
                      handshake_pending_len = buffered_len;
                    }
                  }
                }
              } else {
                {
                  handshake_status = HandshakeSentinelCollision;
                  handshake_pending_len = buffered_len;
                }
              }
            } else {
              {
                handshake_status = HandshakeSelectionNotReady;
                handshake_pending_len = buffered_len;
              }
            }
          } else {
            {
              handshake_status = HandshakeRandomFailed;
              handshake_pending_len = buffered_len;
            }
          }
        } else {
          let local =
            BL.process_ready_empty_local_action_once
              d
              empty_payload
              network_out
              network_out_len
              app_out
              app_out_len;
          match local {
            BL.LocalProcessed -> {
              let next_fuel = SZ.sub fuel 1sz;
              assert (pure (SZ.v next_fuel < SZ.v fuel));
              drive_handshake
                d
                empty_payload
                material_payload
                network_out
                network_out_len
                app_out
                app_out_len
                buffered_len
                local_fuel
                next_fuel
            }
            BL.LocalNotReady -> {
              let network =
                BN.drive
                  d
                  network_out
                  network_out_len
                  app_out
                  app_out_len
                  buffered_len
                  local_fuel;
              match network.BN.completed_drive_outcome {
                BS.DriveYield _ _ _ _ -> {
                  let next_fuel = SZ.sub fuel 1sz;
                  assert (pure (SZ.v next_fuel < SZ.v fuel));
                  drive_handshake
                    d
                    empty_payload
                    material_payload
                    network_out
                    network_out_len
                    app_out
                    app_out_len
                    network.BN.completed_drive_pending_len
                    local_fuel
                    next_fuel
                }
                BS.DriveProgress _ _ _ -> {
                  let next_fuel = SZ.sub fuel 1sz;
                  assert (pure (SZ.v next_fuel < SZ.v fuel));
                  drive_handshake
                    d
                    empty_payload
                    material_payload
                    network_out
                    network_out_len
                    app_out
                    app_out_len
                    network.BN.completed_drive_pending_len
                    local_fuel
                    next_fuel
                }
                BS.DriveExhausted -> {
                  {
                    handshake_status = HandshakeExhausted;
                    handshake_pending_len =
                      network.BN.completed_drive_pending_len;
                  }
                }
                _ -> {
                  {
                    handshake_status = HandshakeStepFailed;
                    handshake_pending_len =
                      network.BN.completed_drive_pending_len;
                  }
                }
              }
            }
            _ -> {
              {
                handshake_status = HandshakeStepFailed;
                handshake_pending_len = buffered_len;
              }
            }
          }
        }
      }
    }
  }
}

fn run
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (material_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (buffered_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to material_payload 'material_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'buffered == SZ.v buffered_len /\
      B.length 'empty_payload_bytes == 0 /\
      B.length 'material_bytes == SZ.v DS.driver_material_capacity /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      network_out_len == DS.driver_network_out_capacity /\
      app_out_len == DS.driver_app_out_capacity /\
      CM.can_start_server 'st0)
  returns result:handshake_result
  ensures
    exists* st1 buffered_after material_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        buffered_after
        result.handshake_pending_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to material_payload material_after **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.handshake_pending_len /\
        B.length material_after == SZ.v DS.driver_material_capacity /\
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        (result.handshake_status == HandshakeOk ==>
         st1.CS.cs_model.CS.model_control == CS.ControlApplicationData))
{
  if (fuel = 0sz) {
    {
      handshake_status = HandshakeExhausted;
      handshake_pending_len = buffered_len;
    }
  } else {
    let _ =
      BH.start_server_once
        d
        empty_payload
        network_out
        network_out_len
        app_out
        app_out_len;
    let next_fuel = SZ.sub fuel 1sz;
    assert (pure (SZ.v next_fuel < SZ.v fuel));
    drive_handshake
      d
      empty_payload
      material_payload
      network_out
      network_out_len
      app_out
      app_out_len
      buffered_len
      local_fuel
      next_fuel
  }
}
