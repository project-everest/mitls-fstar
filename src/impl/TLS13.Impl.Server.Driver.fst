module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CT = TLS13.Impl.Client.Types
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module IO = TLS13.IO
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module DS = TLS13.Impl.Server.Driver.State
module DT = TLS13.Impl.Server.Driver.Transport
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DH = TLS13.Impl.Server.Driver.Handshake
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module RS = TLS13.Record.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

type server_driver = DS.server_driver

noextract
let server_driver_wire_logs_match = DS.server_driver_wire_logs_match

noextract
let server_driver_live = DS.server_driver_live

noextract
let server_driver_connected = DS.server_driver_connected

noextract
let server_driver_closed = DS.server_driver_closed

open TLS13.Impl.Server.Driver.State
open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local
open TLS13.Impl.Server.Driver.Handshake

let lemma_control_snapshot_app_ready
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 2uy)
      (ensures
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
=
  assert_norm (U8.v 2uy == 2);
  assert (U8.v snapshot.CR.snapshot_control_tag == 2);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlApplicationData -> ()
  | _ -> assert False

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity))
           | None ->
             emp)
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let erased_identity : erased CS.server_credential_identity =
        Ghost.hide credential_identity;
      let s =
        S.new_server_erased_credential_identity
          certificate_chain
          certificate_chain_len
          #erased_identity;
      assert (pure (Ghost.reveal erased_identity == credential_identity));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            (Ghost.reveal erased_identity)))
        as
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy driver_rx_capacity;
      let network_out = V.alloc 0uy driver_network_out_capacity;
      let material_payload = V.alloc 0uy driver_material_capacity;
      let cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy driver_signature_capacity;
      let app_out = V.alloc 0uy driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v driver_app_out_capacity));
      let d = {
        server_driver_server = s;
        server_driver_credentials = creds;
        server_driver_channel = channel;
        server_driver_buffered_len = buffered_len;
        server_driver_empty_payload = empty_payload;
        server_driver_raw = raw;
        server_driver_network_out = network_out;
        server_driver_material_payload = material_payload;
        server_driver_certificate_verify_input = cv_input;
        server_driver_signature = signature;
        server_driver_app_out = app_out;
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy))
        as
        (V.pts_to d.server_driver_material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy));
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (S.connection_exactly
          d.server_driver_server
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        as
        (O.is_server_credentials
          d.server_driver_credentials
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      fold (server_driver_buffers d B.empty 0sz);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
}

fn accept
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed d st1 'certificate_chain 'credential_identity
           | ServerWorkflowOk ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlApplicationData)
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent)
{
  let result =
    accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once
      d
      bind_host
      bind_host_len
      port
      network_fuel
      local_fuel;
  match result {
    ServerDriverAcceptServerHelloDrainListenFailed -> {
      close_live_without_transport d;
      ServerWorkflowClosed
    }
    ServerDriverAcceptServerHelloDrainAcceptFailed -> {
      close_live_without_transport d;
      ServerWorkflowClosed
    }
    ServerDriverAcceptServerHelloDrainClientHelloWait wait -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      if (wait.server_driver_client_hello_wait_exhausted) {
        ServerWorkflowExhausted
      } else {
        if (wait.server_driver_client_hello_wait_last.ST.response.ST.status = ST.NeedMoreInput) {
          ServerWorkflowNeedMoreInput
        } else {
          ServerWorkflowStepFailed
        }
      }
    }
    ServerDriverAcceptServerHelloDrainMaterialFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSelectionNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainDeriveFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSendNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainOk drain -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent);
      if (drain.server_driver_local_drain_exhausted) {
        ServerWorkflowExhausted
      } else {
        match drain.server_driver_local_drain_last {
          ServerDriverLocalExternalOrUnsupported -> {
            ServerWorkflowNeedExternalAction
          }
          ServerDriverLocalStepFailed -> {
            ServerWorkflowStepFailed
          }
          ServerDriverLocalNotReady -> {
            let net = DN.read_process_network_until_ready d network_fuel;
            with st_net received_net sent_net net_app_out.
              assert (server_driver_connected_with_app_out
                d
                st_net
                'certificate_chain
                'credential_identity
                received_net
                sent_net
                net_app_out);
            forget_server_driver_connected_app_out d;
            if (net.DN.server_driver_network_loop_exhausted) {
              ServerWorkflowExhausted
            } else {
              if (net.DN.server_driver_network_loop_last.ST.response.ST.status = ST.StepOk) {
                let drain_after_client_finished =
                  DL.drain_ready_empty_local_actions d local_fuel;
                with st2 received2 sent2.
                  assert (server_driver_connected
                    d
                    st2
                    'certificate_chain
                    'credential_identity
                    received2
                    sent2);
                if (drain_after_client_finished.DL.server_driver_local_drain_exhausted) {
                  ServerWorkflowExhausted
                } else {
                  match drain_after_client_finished.DL.server_driver_local_drain_last {
                    ServerDriverLocalExternalOrUnsupported -> {
                      ServerWorkflowNeedExternalAction
                    }
                    ServerDriverLocalStepFailed -> {
                      ServerWorkflowStepFailed
                    }
                    _ -> {
                      let snapshot = DN.server_driver_control_snapshot d;
                      with st3 received3 sent3.
                        assert (server_driver_connected
                          d
                          st3
                          'certificate_chain
                          'credential_identity
                          received3
                          sent3);
                      assert (pure (CR.control_snapshot_matches snapshot st3));
                      let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
                      if app_ready {
                        assert (pure (snapshot.CR.snapshot_control_tag == 2uy));
                        lemma_control_snapshot_app_ready snapshot st3;
                        assert (pure (
                          st3.CS.cs_model.CS.model_control ==
                            CS.ControlApplicationData));
                        ServerWorkflowOk
                      } else {
                        ServerWorkflowNeedMoreInput
                      }
                    }
                  }
                }
              } else {
                ServerWorkflowStepFailed
              }
            }
          }
          ServerDriverLocalProcessed -> {
            ServerWorkflowNeedMoreInput
          }
        }
      }
    }
  }
}

fn send
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns status:server_workflow_status
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_send_correct
            'st0
            st1
            status
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')
{
  let resp = send_application_data_once d payload payload_len;
  if (resp.ST.status = ST.StepOk) {
    ServerWorkflowOk
  } else {
    ServerWorkflowStepFailed
  }
}

fn receive
  (d:server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to out 'out_bytes **
           pure (B.length 'out_bytes == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* st1 received' sent' out_bytes.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.server_receive_len <= SZ.v out_len /\
                (exists loop app_out.
                  server_driver_receive_correct
                    'st0
                    st1
                    result
                    loop
                    (Ghost.reveal 'sent)
                    sent'
                    app_out
                    out_bytes))
{
  let loop = read_process_network_until_ready d network_fuel;
  with st1 received' sent' loop_app_out.
    assert (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      received'
      sent'
      loop_app_out **
      pure (loop.server_driver_network_loop_exhausted == false ==>
        loop.server_driver_network_loop_last.ST.response.ST.status <>
          ST.NeedMoreInput /\
        server_driver_network_process_correct
          'st0
          st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent' /\
          server_driver_network_process_correct_for_app_out
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'
            loop_app_out));
  if (loop.server_driver_network_loop_exhausted) {
    let result = {
      server_receive_status = ServerWorkflowExhausted;
      server_receive_len = 0sz;
    };
    assert (pure (server_driver_receive_correct
      'st0
      st1
      result
      loop
      (Ghost.reveal 'sent)
      sent'
      B.empty
      (Ghost.reveal 'out_bytes)));
    forget_server_driver_connected_app_out d;
    result
  } else {
    match loop.server_driver_network_loop_last.ST.response.ST.status {
      ST.StepOk -> {
        unfold (server_driver_connected_with_app_out
          d
          st1
          'certificate_chain
          'credential_identity
          received'
          sent'
          loop_app_out);
        with ch buffered buffered_len.
          assert (Box.pts_to d.server_driver_channel (Some ch) **
                  IO.is_channel ch received' sent' **
                  server_driver_buffers_with_app_out
                    d
                    buffered
                    buffered_len
                    loop_app_out);
        unfold (server_driver_buffers_with_app_out
          d
          buffered
          buffered_len
          loop_app_out);
        with empty_payload raw network_out material cv_input signature.
          assert (
            Box.pts_to d.server_driver_buffered_len buffered_len **
            V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.server_driver_raw #1.0R raw **
            V.pts_to d.server_driver_network_out #1.0R network_out **
            V.pts_to d.server_driver_material_payload #1.0R material **
            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
            V.pts_to d.server_driver_signature #1.0R signature **
            V.pts_to d.server_driver_app_out #1.0R loop_app_out);
        let copy_len = loop.server_driver_network_loop_last.ST.response.ST.app_out_len;
        let app_fits = SZ.lte copy_len out_len;
        let app_src_fits = SZ.lte copy_len driver_app_out_capacity;
        if (app_fits && app_src_fits) {
          V.to_array_pts_to d.server_driver_app_out;
          A.pts_to_len (V.vec_to_array d.server_driver_app_out);
          A.pts_to_len out;
          assert (pure (SZ.v copy_len <= SZ.v out_len));
          assert (pure (SZ.v copy_len <= SZ.v driver_app_out_capacity));
          assert (pure (B.length loop_app_out == SZ.v driver_app_out_capacity));
          assert (pure (A.length (V.vec_to_array d.server_driver_app_out) ==
            B.length loop_app_out));
          assert (pure (A.length out == SZ.v out_len));
          assert (pure (SZ.v copy_len <= A.length (V.vec_to_array d.server_driver_app_out)));
          assert (pure (SZ.v copy_len <= A.length out));
          let _ = A.memcpy_l copy_len (V.vec_to_array d.server_driver_app_out) out;
          with out_bytes.
            assert (pts_to out out_bytes);
          A.pts_to_len out;
          assert (pure (B.length out_bytes == SZ.v out_len));
          assert (pure (SZ.v copy_len <= B.length loop_app_out));
          assert (pure (Seq.equal
            (ST.response_app_out
              loop.server_driver_network_loop_last.ST.response
              loop_app_out)
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          Seq.lemma_len_slice out_bytes 0 (SZ.v copy_len);
          Seq.lemma_len_slice loop_app_out 0 (SZ.v copy_len);
          assert (pure (Seq.equal
            (Seq.slice out_bytes 0 (SZ.v copy_len))
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          V.to_vec_pts_to d.server_driver_app_out;
          fold (server_driver_buffers_with_app_out
            d
            buffered
            buffered_len
            loop_app_out);
          fold (server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent'
            loop_app_out);
          let result = {
            server_receive_status = ServerWorkflowOk;
            server_receive_len = copy_len;
          };
          assert (pure (server_driver_network_process_correct_for_app_out
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'
            loop_app_out));
          assert (pure (server_driver_receive_copyout_correct
            result
            loop.server_driver_network_loop_last.ST.response
            loop_app_out
            out_bytes));
          assert (pure (server_driver_receive_correct
            'st0
            st1
            result
            loop
            (Ghost.reveal 'sent)
            sent'
            loop_app_out
            out_bytes));
          forget_server_driver_connected_app_out d;
          result
        } else {
          fold (server_driver_buffers_with_app_out
            d
            buffered
            buffered_len
            loop_app_out);
          fold (server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent'
            loop_app_out);
          let result = {
            server_receive_status = ServerWorkflowStepFailed;
            server_receive_len = 0sz;
          };
          assert (pure (server_driver_receive_correct
            'st0
            st1
            result
            loop
            (Ghost.reveal 'sent)
            sent'
            loop_app_out
            (Ghost.reveal 'out_bytes)));
          forget_server_driver_connected_app_out d;
          result
        }
      }
      ST.NeedMoreInput -> {
        let result = {
          server_receive_status = ServerWorkflowNeedMoreInput;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
      _ -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
    }
  }
}

fn close
  (d:server_driver)
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns status:server_workflow_status
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity **
          pure (status == ServerWorkflowClosed)
{
  close_transport_once d;
  ServerWorkflowClosed
}
