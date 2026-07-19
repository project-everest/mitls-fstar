module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CTypes = TLS13.Impl.CanonicalTypes
module ES = TLS13.Spec.Endpoint.Server
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CT = TLS13.Impl.Client.Types
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module IM = TLS13.Impl.Messages
module IO = Common.TCP
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
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
module MR = Pulse.Lib.MonotonicGhostRef
module RS = TLS13.Record.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module SP = TLS13.Impl.Server.CanonicalProtocol
module SS = TLS13.Impl.Server.Send
module GSHbody = TLS13.Wire.Generated.ServerHello_body

type server_driver = DS.server_driver

noextract
let server_driver_canonical = DS.server_driver_canonical

noextract
let server_driver_canonical_progress = DS.server_driver_canonical_progress

noextract
let server_driver_wire_logs_match = DS.server_driver_wire_logs_match

noextract
let server_driver_live = DS.server_driver_live
noextract
let server_driver_connected = DS.server_driver_connected
noextract
let server_driver_closed = DS.server_driver_closed
let lemma_server_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures server_driver_received_log_exact_prefix st received)
=
  DS.lemma_server_driver_wire_logs_match_received_exact_prefix
    st
    received
    sent
    buffered
    buffered_len

let lemma_server_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures server_driver_received_no_read_ahead st received)
=
  DS.lemma_server_driver_wire_logs_match_received_no_read_ahead
    st
    received
    sent
    buffered
    buffered_len

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

let lemma_control_snapshot_closed
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 4uy)
      (ensures
        st.CS.cs_model.CS.model_control == CS.ControlClosed)
=
  assert_norm (U8.v 4uy == 4);
  assert (U8.v snapshot.CR.snapshot_control_tag == 4);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlClosed -> ()
  | _ -> assert False

let lemma_control_snapshot_not_closed
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag <> 4uy)
      (ensures
        st.CS.cs_model.CS.model_control <> CS.ControlClosed)
=
  assert_norm (U8.v 4uy == 4);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlClosed ->
    assert (U8.v snapshot.CR.snapshot_control_tag == 4);
    assert (snapshot.CR.snapshot_control_tag == 4uy);
    assert False
  | _ -> ()

let lemma_application_ready_close_notify_ready
  (st:CS.connection_state)
  : Lemma
    (requires server_driver_application_ready st)
    (ensures
      ST.server_local_event_input_ready
        st
        ST.LocalSendCloseNotify
        B.empty)
=
  Seq.lemma_eq_intro B.empty B.empty;
  assert (Seq.equal B.empty B.empty);
  assert (ST.server_end_to_end_invariant st);
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
    CS.ServerTraffic);
  assert (CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model);
  match st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic with
  | Some _ -> ()
  | None ->
    assert_norm (CS.traffic_material_for_label
      st.CS.cs_model.CS.model_handshake.CS.hs_keys
      CS.TrafficApplication
      CS.ServerTraffic ==
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
    assert False

let lemma_application_ready_send_ready
  (st:CS.connection_state)
  (payload:B.bytes)
  : Lemma
      (requires
        server_driver_application_ready st /\
        B.length payload <= SM.max_application_data_fragment_len)
      (ensures
        ST.server_local_event_input_ready
          st
          ST.LocalSendApplicationData
          payload)
=
  assert (ST.server_end_to_end_invariant st);
  assert (st.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    st.CS.cs_model);
  assert_norm (CS.traffic_label_for_endpoint_direction
    CS.ServerEndpoint
    CS.TrafficWrite == CS.ServerTraffic);
  match st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic with
  | Some _ -> ()
  | None -> assert False

(**
  One verified network-processing step, abstracting over the concrete buffer
  response and sent-log prefix/suffix.  This is the single-step relation whose
  reflexive-transitive closure is [server_driver_network_reaches].
**)
noextract
let server_driver_network_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  exists (r:ST.server_buffer_response) (s s':B.bytes).
    server_driver_network_process_correct st0 st1 r s s'

(**
  Concrete witness for [server_driver_network_reaches]: a path [st0 -> ... -> st1]
  where each hop is a verified network-processing step.  The empty path witnesses
  reflexivity ([st0 == st1]).
**)
noextract
let rec is_network_path
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (path:list CS.connection_state)
  : Tot prop (decreases path) =
  match path with
  | [] -> st0 == st1
  | hd :: tl -> server_driver_network_step st0 hd /\ is_network_path hd st1 tl

(* Realises the abstract [server_driver_network_reaches] from the interface. *)
let server_driver_network_reaches
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop =
  exists (path:list CS.connection_state). is_network_path st0 st1 path

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
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
                         credential_identity) /\
                     B.length 'certificate_chain_bytes <=
                       Bounds.max_server_certificate_chain_len /\
                     Ghost.reveal
                       (server_driver_canonical d).SP.canonical_server_initial ==
                       CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity)
           | None ->
             emp) **
          pure
           (not (B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len) ==>
            result == None)
{
  (* Totalization: accept an arbitrary-length certificate chain at the API
     boundary and reject (as [None], with all input resources preserved) any
     chain that exceeds the authoritative [max_server_certificate_chain_len]
     bound.  The check runs BEFORE any allocation or credential construction, so
     the oversized path frees nothing and simply returns the untouched inputs.
     On the in-bound path [within_bound == true] gives
     [SZ.v certificate_chain_len <= SZ.v max_server_certificate_chain_len_sz],
     and the [max_server_certificate_chain_len_sz] refinement rewrites the RHS to
     [max_server_certificate_chain_len]; together with the [requires] equation
     [B.length 'certificate_chain_bytes == SZ.v certificate_chain_len] this
     re-establishes the bound that the credential/state constructors and the
     strengthened [Some] postcondition rely on. *)
  let within_bound =
    SZ.lte certificate_chain_len Bounds.max_server_certificate_chain_len_sz;
  if within_bound {
  assert (pure (B.length 'certificate_chain_bytes <=
                Bounds.max_server_certificate_chain_len));
  let material_payload = V.alloc 0uy DS.driver_material_capacity;
  V.to_array_pts_to material_payload;
  let material_ok =
    Crypto.random_bytes
      (V.vec_to_array material_payload)
      DS.driver_material_capacity;
  with material_seed.
    assert (pts_to (V.vec_to_array material_payload) material_seed);
  V.to_vec_pts_to material_payload;
  if not material_ok {
    V.free material_payload;
    None
  } else {
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      V.free material_payload;
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
      let progress = MR.alloc #_ #(ES.server_progress_preorder #CTypes.server_local_event)
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      MR.take_snapshot
        progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy DS.driver_rx_capacity;
      let network_out = V.alloc 0uy DS.driver_network_out_capacity;
      let cv_input = V.alloc 0uy DS.driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy DS.driver_signature_capacity;
      let app_out = V.alloc 0uy DS.driver_app_out_capacity;
      let local_app_out = V.alloc 0uy DS.driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v DS.driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v DS.driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v DS.driver_app_out_capacity));
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
        server_driver_local_app_out = local_app_out;
        server_driver_progress = progress;
        server_driver_initial =
          Ghost.hide
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity);
        server_driver_supported_profile =
          Ghost.hide
            ((Ghost.reveal supported_profile_provider)
              (CR.server_initial_state
                (Ghost.reveal 'certificate_chain_bytes)
                credential_identity));
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v DS.driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v DS.driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R material_seed)
        as
        (V.pts_to d.server_driver_material_payload #1.0R material_seed);
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v DS.driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v DS.driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v DS.driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v DS.driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
      rewrite
        (V.pts_to local_app_out #1.0R (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_local_app_out #1.0R
          (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
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
      rewrite
        (MR.pts_to progress #1.0R
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.pts_to d.server_driver_progress #1.0R
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (MR.snapshot progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.snapshot d.server_driver_progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      assert (pure (Ghost.reveal d.server_driver_initial ==
        CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
      rewrite
        (MR.snapshot d.server_driver_progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.snapshot d.server_driver_progress
          (Ghost.reveal d.server_driver_initial));
      fold (server_driver_canonical_progress d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
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
  } else {
    (* Oversized certificate chain: nothing has been allocated yet, so return
       [None] with the (untouched) input resources preserved. *)
    None
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
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed d st1 'certificate_chain 'credential_identity **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | ServerWorkflowOk ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (server_driver_application_ready st1 /\
                    st1.CS.cs_model.CS.model_config ==
                      'st0.CS.cs_model.CS.model_config /\
                    server_driver_sent_log_exact st1 sent /\
                    server_driver_received_log_accounted st1 received /\
                    server_driver_received_log_exact_prefix st1 received /\
                    server_driver_received_no_read_ahead st1 received)
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config))
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
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
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
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
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
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
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
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
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
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainOk drain -> {
      with st1 received sent.
        assert (
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received
            sent **
          pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      if (drain.server_driver_local_drain_exhausted) {
        ServerWorkflowExhausted
      } else {
        match drain.server_driver_local_drain_last {
          ServerDriverLocalUnsupported -> {
            ServerWorkflowStepFailed
          }
          ServerDriverLocalStepFailed -> {
            ServerWorkflowStepFailed
          }
          ServerDriverLocalNotReady -> {
            let net = DN.read_process_network_until_ready d network_fuel;
            with st_net received_net sent_net net_app_out.
              assert (
                server_driver_connected_with_app_out
                  d
                  st_net
                  'certificate_chain
                  'credential_identity
                  received_net
                  sent_net
                  net_app_out **
                pure (st_net.CS.cs_model.CS.model_config ==
                  st1.CS.cs_model.CS.model_config));
            assert (pure (st_net.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            forget_server_driver_connected_app_out d;
            if (net.DN.server_driver_network_loop_exhausted) {
              ServerWorkflowExhausted
            } else {
              if (net.DN.server_driver_network_loop_last.ST.response.ST.status = ST.StepOk) {
                let drain_after_client_finished =
                  DL.drain_ready_empty_local_actions d local_fuel;
                with st2 received2 sent2.
                  assert (
                    server_driver_connected
                      d
                      st2
                      'certificate_chain
                      'credential_identity
                      received2
                      sent2 **
                    pure (st2.CS.cs_model.CS.model_config ==
                      st_net.CS.cs_model.CS.model_config));
                assert (pure (st2.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config));
                if (drain_after_client_finished.DL.server_driver_local_drain_exhausted) {
                  ServerWorkflowExhausted
                } else {
                  match drain_after_client_finished.DL.server_driver_local_drain_last {
                    ServerDriverLocalUnsupported -> {
                      ServerWorkflowStepFailed
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
                      assert (pure (st3.CS.cs_model.CS.model_config ==
                        st2.CS.cs_model.CS.model_config));
                      assert (pure (st3.CS.cs_model.CS.model_config ==
                        'st0.CS.cs_model.CS.model_config));
                      assert (pure (CR.control_snapshot_matches snapshot st3));
                      let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
                      if app_ready {
                        assert (pure (snapshot.CR.snapshot_control_tag == 2uy));
                        lemma_control_snapshot_app_ready snapshot st3;
                        assert (pure (
                          st3.CS.cs_model.CS.model_control ==
                            CS.ControlApplicationData));
                        unfold (server_driver_connected
                          d
                          st3
                          'certificate_chain
                          'credential_identity
                          received3
                          sent3);
                        with ch buffered buffered_len.
                          assert (Box.pts_to d.server_driver_channel (Some ch) **
                                  IO.is_channel ch received3 sent3 **
                                  server_driver_buffers d buffered buffered_len);
                        unfold (server_driver_buffers d buffered buffered_len);
                        with empty_payload raw network_out material cv_input signature app_out local_app_out.
                          assert (
                            Box.pts_to d.server_driver_buffered_len buffered_len **
                            V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
                            V.pts_to d.server_driver_raw #1.0R raw **
                            V.pts_to d.server_driver_network_out #1.0R network_out **
                            V.pts_to d.server_driver_material_payload #1.0R material **
                            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
                            V.pts_to d.server_driver_signature #1.0R signature **
                            V.pts_to d.server_driver_app_out #1.0R app_out **
                            V.pts_to d.server_driver_local_app_out #1.0R local_app_out);
                        let current_buffered_len = Box.(!d.server_driver_buffered_len);
                        assert (pure (current_buffered_len == buffered_len));
                        fold (server_driver_buffers d buffered buffered_len);
                        assert (pure (ST.server_end_to_end_invariant st3));
                        rewrite (S.connection_exactly d.server_driver_server st3) as
                          (CR.connection_exactly d.server_driver_server st3);
                        let app_keys_ready =
                          CQ.server_application_record_keys_installed_runtime
                            d.server_driver_server;
                        rewrite (CR.connection_exactly d.server_driver_server st3) as
                          (S.connection_exactly d.server_driver_server st3);
                        let retained_empty = current_buffered_len = 0sz;
                        if retained_empty {
                          assert (pure (buffered_len == 0sz));
                          if app_keys_ready {
                            assert (pure (CS.application_record_keys_installed_for_role
                              CS.ServerEndpoint
                              st3.CS.cs_model));
                            CSL.lemma_server_application_ready_stable_x25519_key_share_projection
                              st3;
                            assert (pure (server_driver_sent_log_exact st3 sent3));
                            lemma_server_driver_wire_logs_match_received_accounted
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_log_accounted st3 received3));
                            assert (pure (ST.server_connection_control_not_failed st3));
                            lemma_server_driver_wire_logs_match_received_exact_prefix
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_log_exact_prefix st3 received3));
                            lemma_server_driver_wire_logs_match_received_no_read_ahead
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_no_read_ahead st3 received3));
                            fold (server_driver_connected
                              d
                              st3
                              'certificate_chain
                              'credential_identity
                              received3
                              sent3);
                            assert (pure (server_driver_application_ready st3));
                            ServerWorkflowOk
                          } else {
                            fold (server_driver_connected
                              d
                              st3
                              'certificate_chain
                              'credential_identity
                              received3
                              sent3);
                            ServerWorkflowStepFailed
                          }
                        } else {
                          fold (server_driver_connected
                            d
                            st3
                            'certificate_chain
                            'credential_identity
                            received3
                            sent3);
                          ServerWorkflowNeedMoreInput
                        }
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
                 server_driver_application_ready 'st0)
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
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config /\
            server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
            server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
            server_driver_sent_log_exact st1 sent' /\
            server_driver_received_log_accounted st1 (Ghost.reveal 'received))
{
  unfold (server_driver_connected
     d
     'st0
     (Ghost.reveal 'certificate_chain)
     (Ghost.reveal 'credential_identity)
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
     assert (Box.pts_to d.server_driver_channel (Some ch0) **
             IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
             server_driver_buffers d buffered0 buffered_len0 **
             pure (server_driver_wire_logs_match
               'st0
               (Ghost.reveal 'received)
               (Ghost.reveal 'sent)
               buffered0
               buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
     'st0
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent)
     buffered0
     buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
     d
     'st0
     (Ghost.reveal 'certificate_chain)
     (Ghost.reveal 'credential_identity)
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent));
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let too_large = SZ.gt payload_len 16384sz;
  if too_large {
    assert (pure (SZ.v payload_len > SM.max_application_data_fragment_len));
    assert (pure (
      B.length (Ghost.reveal 'payload_bytes) >
        SM.max_application_data_fragment_len));
    assert (pure (
      server_driver_payload_too_large (Ghost.reveal 'payload_bytes)));
    assert (pure (server_driver_send_correct
      'st0
      'st0
      ServerWorkflowPayloadTooLarge
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal 'sent)
      (Ghost.reveal 'sent)));
    ServerWorkflowPayloadTooLarge
  } else {
  assert (pure (SZ.v payload_len <= SM.max_application_data_fragment_len));
  lemma_application_ready_send_ready
    'st0
    (Ghost.reveal 'payload_bytes);
  let resp = send_application_data_once d payload payload_len;
  with st1 sent'.
    assert (server_driver_connected
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent');
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    ST.LocalSendApplicationData
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    sent';
  unfold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received)
    sent');
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received) sent' **
            server_driver_buffers d buffered buffered_len **
            pure (server_driver_wire_logs_match st1 (Ghost.reveal 'received) sent' buffered buffered_len));
  assert (pure (server_driver_sent_log_exact st1 sent'));
  lemma_server_driver_wire_logs_match_received_accounted
    st1
    (Ghost.reveal 'received)
    sent'
    buffered
    buffered_len;
  assert (pure (server_driver_received_log_accounted st1 (Ghost.reveal 'received)));
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received)
    sent');
  if (resp.ST.status = ST.StepOk) {
    ServerWorkflowOk
  } else {
    ServerWorkflowStepFailed
  }
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
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                server_driver_sent_log_exact st1 sent' /\
                server_driver_received_log_accounted st1 received' /\
                (server_driver_application_ready 'st0 /\
                 (result.server_receive_status == ServerWorkflowExhausted \/
                  result.server_receive_status == ServerWorkflowNeedMoreInput) ==>
                 server_driver_application_ready st1) /\
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
  unfold (server_driver_connected
    d
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
    assert (Box.pts_to d.server_driver_channel (Some ch0) **
            IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
            server_driver_buffers d buffered0 buffered_len0 **
            pure (server_driver_wire_logs_match
              'st0
              (Ghost.reveal 'received)
              (Ghost.reveal 'sent)
              buffered0
              buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    buffered0
    buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
    d
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
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
      pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config /\
      (loop.server_driver_network_loop_exhausted == true ==>
        st1 == 'st0 /\
        Seq.equal sent' (Ghost.reveal 'sent)) /\
      (loop.server_driver_network_loop_exhausted == false ==>
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
            loop_app_out)));
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
            server_driver_buffers_with_app_out d buffered buffered_len loop_app_out **
            pure (server_driver_wire_logs_match st1 received' sent' buffered buffered_len));
  assert (pure (server_driver_sent_log_exact st1 sent'));
  lemma_server_driver_wire_logs_match_received_accounted
    st1
    received'
    sent'
    buffered
    buffered_len;
  assert (pure (server_driver_received_log_accounted st1 received'));
  rewrite (S.connection_exactly d.server_driver_server st1)
    as (CR.connection_exactly d.server_driver_server st1);
  let control_snapshot = CQ.get_control_snapshot d.server_driver_server;
  rewrite (CR.connection_exactly d.server_driver_server st1)
    as (S.connection_exactly d.server_driver_server st1);
  assert (pure (CR.control_snapshot_matches control_snapshot st1));
  fold (server_driver_connected_with_app_out
    d
    st1
    'certificate_chain
    'credential_identity
    received'
    sent'
    loop_app_out);
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
    let closed = control_snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
      assert (pure (control_snapshot.CR.snapshot_control_tag == 4uy));
      lemma_control_snapshot_closed control_snapshot st1;
      assert (pure (st1.CS.cs_model.CS.model_control == CS.ControlClosed));
      let result = {
        server_receive_status = ServerWorkflowClosed;
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
    } else {
    assert (pure (control_snapshot.CR.snapshot_control_tag <> 4uy));
    lemma_control_snapshot_not_closed control_snapshot st1;
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
        with empty_payload raw network_out material cv_input signature local_app_out.
          assert (
            Box.pts_to d.server_driver_buffered_len buffered_len **
            V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.server_driver_raw #1.0R raw **
            V.pts_to d.server_driver_network_out #1.0R network_out **
            V.pts_to d.server_driver_material_payload #1.0R material **
            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
            V.pts_to d.server_driver_signature #1.0R signature **
            V.pts_to d.server_driver_app_out #1.0R loop_app_out **
            V.pts_to d.server_driver_local_app_out #1.0R local_app_out);
        let copy_len = loop.server_driver_network_loop_last.ST.response.ST.app_out_len;
        let app_fits = SZ.lte copy_len out_len;
        let app_src_fits = SZ.lte copy_len DS.driver_app_out_capacity;
        if (app_fits && app_src_fits) {
          V.to_array_pts_to d.server_driver_app_out;
          A.pts_to_len (V.vec_to_array d.server_driver_app_out);
          A.pts_to_len out;
          assert (pure (SZ.v copy_len <= SZ.v out_len));
          assert (pure (SZ.v copy_len <= SZ.v DS.driver_app_out_capacity));
          assert (pure (B.length loop_app_out == SZ.v DS.driver_app_out_capacity));
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
            out_bytes
            (Seq.append
              (Seq.slice loop_app_out 0 (SZ.v copy_len))
              (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out)))));
          Seq.lemma_len_slice loop_app_out 0 (SZ.v copy_len);
          assert (pure (Seq.length (Seq.slice loop_app_out 0 (SZ.v copy_len)) == SZ.v copy_len));
          SeqP.append_slices
            (Seq.slice loop_app_out 0 (SZ.v copy_len))
            (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out));
          Seq.lemma_eq_elim
            out_bytes
            (Seq.append
              (Seq.slice loop_app_out 0 (SZ.v copy_len))
              (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out)));
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
      ST.DecodeError -> {
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
      ST.IllegalTransition -> {
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
      ST.OutputBufferTooSmall -> {
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
      ST.ConnectionFailed -> {
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
}

(**
  Reflexive-transitive-closure lemmas for [server_driver_network_reaches].  They
  are proved once here, in pure F*, so the Pulse [close] workflow only needs to
  chain lemma calls rather than reason about the existential path witness.
**)
let server_driver_network_reaches_refl (st:CS.connection_state)
  : Lemma (ensures server_driver_network_reaches st st)
=
  introduce exists (path:list CS.connection_state). is_network_path st st path
  with [] and ()

let server_driver_network_step_intro
  (st0 st1:CS.connection_state)
  (r:ST.server_buffer_response)
  (s s':B.bytes)
  : Lemma
      (requires server_driver_network_process_correct st0 st1 r s s')
      (ensures server_driver_network_step st0 st1)
=
  introduce
    exists (r0:ST.server_buffer_response) (s0 s0':B.bytes).
      server_driver_network_process_correct st0 st1 r0 s0 s0'
  with r s s' and ()

#push-options "--split_queries always"
let server_driver_network_reaches_step
  (st0 st1 st2:CS.connection_state)
  : Lemma
      (requires server_driver_network_step st0 st1 /\
                server_driver_network_reaches st1 st2)
      (ensures server_driver_network_reaches st0 st2)
=
  eliminate exists (path:list CS.connection_state). is_network_path st1 st2 path
  returns server_driver_network_reaches st0 st2
  with _. (
    introduce
      exists (path':list CS.connection_state). is_network_path st0 st2 path'
    with (st1 :: path) and ()
  )
#pop-options

(**
  Constructs [server_driver_close_final_correct] for the [close] workflow:
  [st_cn] is the close_notify state, [st_final] is reached from it by verified
  network processing, and when the caller did not ask to wait the two coincide,
  recovering the historical exact-state guarantee.
**)
let lemma_close_final_correct
  (wait_for_peer:bool)
  (st0 st_cn st_final:CS.connection_state)
  (sent:B.bytes)
  : Lemma
      (requires
        server_driver_close_correct st0 st_cn sent /\
        server_driver_network_reaches st_cn st_final /\
        (wait_for_peer == false ==> st_final == st_cn))
      (ensures server_driver_close_final_correct wait_for_peer st0 st_final sent)
=
  introduce
    exists st_close_notify.
      server_driver_close_correct st0 st_close_notify sent /\
      server_driver_network_reaches st_close_notify st_final
  with st_cn and ()

(**
  Drains the peer's records looking for its close_notify, reporting a status.

  The status is one of [ServerWorkflowClosed] (the peer's close_notify was
  observed, so the connection reached [CS.ControlClosed]),
  [ServerWorkflowExhausted] (the network fuel ran out first) or
  [ServerWorkflowStepFailed] (a nonrecoverable control-failure state or a
  nonrecoverable record-processing failure was observed).

  Liveness/regression fix: the helper snapshots the control state *before* every
  read.  If the connection is already closed or already in a control-failure
  state it stops without issuing another (potentially blocking) read.  After a
  read-and-process step it only recurses when the step status is recoverable
  ([ST.StepOk] or [ST.NeedMoreInput]); any other status is a nonrecoverable
  failure and is reported as [ServerWorkflowStepFailed] rather than being
  ignored and collapsed into [ServerWorkflowExhausted].
**)
fn rec wait_for_peer_close_notify
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns status:server_workflow_status
  ensures exists* st1 received' sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_network_reaches 'st0 st1 /\
                (status == ServerWorkflowClosed \/
                 status == ServerWorkflowExhausted \/
                 status == ServerWorkflowStepFailed) /\
                (SZ.v fuel == 0 ==> status == ServerWorkflowExhausted) /\
                (status == ServerWorkflowClosed ==>
                  st1.CS.cs_model.CS.model_control == CS.ControlClosed))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    server_driver_network_reaches_refl 'st0;
    ServerWorkflowExhausted
  } else {
    let snapshot = server_driver_control_snapshot d;
    assert (pure (CR.control_snapshot_matches snapshot 'st0));
    let closed = snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
      assert (pure (snapshot.CR.snapshot_control_tag == 4uy));
      lemma_control_snapshot_closed snapshot 'st0;
      assert (pure ('st0.CS.cs_model.CS.model_control == CS.ControlClosed));
      server_driver_network_reaches_refl 'st0;
      ServerWorkflowClosed
    } else {
      let failed = snapshot.CR.snapshot_control_tag = 5uy;
      if failed {
        (* The connection is already in a nonrecoverable control-failure state
           (e.g. a fatal alert was received). Report the failure without issuing
           another blocking read. *)
        server_driver_network_reaches_refl 'st0;
        ServerWorkflowStepFailed
      } else {
        assert (pure (0 < SZ.v fuel));
        let step = read_and_process_network_once d;
        with st1 received' sent' step_app_out.
          assert (server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent'
            step_app_out **
          pure (server_driver_network_process_correct
            'st0
            st1
            step
            (Ghost.reveal 'sent)
            sent'));
        lemma_server_driver_network_process_correct_preserves_config
          'st0
          st1
          step
          (Ghost.reveal 'sent)
          sent';
        assert (pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        server_driver_network_step_intro
          'st0
          st1
          step
          (Ghost.reveal 'sent)
          sent';
        assert (pure (server_driver_network_step 'st0 st1));
        forget_server_driver_connected_app_out d;
        let step_ok = step.ST.response.ST.status = ST.StepOk;
        let step_need_more = step.ST.response.ST.status = ST.NeedMoreInput;
        let recoverable = step_ok || step_need_more;
        if recoverable {
          let next_fuel = SZ.sub fuel 1sz;
          assert (pure (SZ.v next_fuel < SZ.v fuel));
          let status = wait_for_peer_close_notify d next_fuel;
          with st2 received2 sent2.
            assert (server_driver_connected
              d
              st2
              'certificate_chain
              'credential_identity
              received2
              sent2 **
            pure (st2.CS.cs_model.CS.model_config ==
              st1.CS.cs_model.CS.model_config /\
            server_driver_network_reaches st1 st2 /\
            (status == ServerWorkflowClosed \/
             status == ServerWorkflowExhausted \/
             status == ServerWorkflowStepFailed) /\
            (status == ServerWorkflowClosed ==>
              st2.CS.cs_model.CS.model_control == CS.ControlClosed)));
          assert (pure (st2.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
          server_driver_network_reaches_step 'st0 st1 st2;
          assert (pure (server_driver_network_reaches 'st0 st2));
          status
        } else {
          (* Nonrecoverable failure while processing the peer's record. Stop
             immediately instead of blocking on another read. *)
          server_driver_network_reaches_refl st1;
          server_driver_network_reaches_step 'st0 st1 st1;
          assert (pure (server_driver_network_reaches 'st0 st1));
          ServerWorkflowStepFailed
        }
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
              'sent **
           pure (server_driver_application_ready 'st0)
  returns status:server_workflow_status
  ensures exists* st1.
          server_driver_closed d st1 'certificate_chain 'credential_identity **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                server_driver_close_final_correct
                  wait_for_peer
                  'st0
                  st1
                  (Ghost.reveal 'sent) /\
                server_driver_close_status_correct wait_for_peer status /\
                server_driver_close_wait_correct wait_for_peer status st1 /\
                server_driver_close_fuel_correct wait_for_peer network_fuel status)
{
  unfold (server_driver_connected
   d
   'st0
   (Ghost.reveal 'certificate_chain)
   (Ghost.reveal 'credential_identity)
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
   assert (Box.pts_to d.server_driver_channel (Some ch0) **
           IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
           server_driver_buffers d buffered0 buffered_len0 **
           pure (server_driver_wire_logs_match
             'st0
             (Ghost.reveal 'received)
             (Ghost.reveal 'sent)
             buffered0
             buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
   'st0
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent)
   buffered0
   buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
   d
   'st0
   (Ghost.reveal 'certificate_chain)
   (Ghost.reveal 'credential_identity)
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent));
  lemma_application_ready_close_notify_ready 'st0;
  let resp = DL.send_close_notify_once d;
  with st_cn sent'.
    assert (server_driver_connected
      d
      st_cn
      'certificate_chain
      'credential_identity
      'received
      sent');
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st_cn
    resp
    ST.LocalSendCloseNotify
    B.empty
    (Ghost.reveal 'sent)
    sent';
  assert (pure (st_cn.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (server_driver_close_correct
    'st0
    st_cn
    (Ghost.reveal 'sent)));
  if wait_for_peer {
    let status = wait_for_peer_close_notify d network_fuel;
    with st_wait received_w sent_w.
      assert (server_driver_connected
        d
        st_wait
        'certificate_chain
        'credential_identity
        received_w
        sent_w **
      pure (st_wait.CS.cs_model.CS.model_config ==
              st_cn.CS.cs_model.CS.model_config /\
            server_driver_network_reaches st_cn st_wait /\
            (status == ServerWorkflowClosed \/
             status == ServerWorkflowExhausted \/
             status == ServerWorkflowStepFailed) /\
            (SZ.v network_fuel == 0 ==> status == ServerWorkflowExhausted) /\
            (status == ServerWorkflowClosed ==>
              st_wait.CS.cs_model.CS.model_control == CS.ControlClosed)));
    assert (pure (st_wait.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    lemma_close_final_correct
      wait_for_peer
      'st0
      st_cn
      st_wait
      (Ghost.reveal 'sent);
    assert (pure (server_driver_close_final_correct
      wait_for_peer 'st0 st_wait (Ghost.reveal 'sent)));
    close_transport_once d;
    assert (server_driver_closed d st_wait 'certificate_chain 'credential_identity);
    if (status = ServerWorkflowClosed) {
      assert (pure (st_wait.CS.cs_model.CS.model_control == CS.ControlClosed));
      assert (pure (server_driver_close_status_correct wait_for_peer ServerWorkflowClosed));
      assert (pure (server_driver_close_wait_correct wait_for_peer ServerWorkflowClosed st_wait));
      assert (pure (SZ.v network_fuel <> 0));
      assert (pure (server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowClosed));
      assert (exists* st1.
        server_driver_closed d st1 'certificate_chain 'credential_identity **
        pure (st1.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config /\
              server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
              server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
              server_driver_close_final_correct wait_for_peer 'st0 st1 (Ghost.reveal 'sent) /\
              server_driver_close_status_correct wait_for_peer ServerWorkflowClosed /\
              server_driver_close_wait_correct wait_for_peer ServerWorkflowClosed st1 /\
              server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowClosed));
      ServerWorkflowClosed
    } else if (status = ServerWorkflowExhausted) {
      assert (pure (server_driver_close_status_correct wait_for_peer ServerWorkflowExhausted));
      assert (pure (server_driver_close_wait_correct wait_for_peer ServerWorkflowExhausted st_wait));
      assert (pure (server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowExhausted));
      assert (exists* st1.
        server_driver_closed d st1 'certificate_chain 'credential_identity **
        pure (st1.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config /\
              server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
              server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
              server_driver_close_final_correct wait_for_peer 'st0 st1 (Ghost.reveal 'sent) /\
              server_driver_close_status_correct wait_for_peer ServerWorkflowExhausted /\
              server_driver_close_wait_correct wait_for_peer ServerWorkflowExhausted st1 /\
              server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowExhausted));
      ServerWorkflowExhausted
    } else {
      (* The only remaining possibility is [ServerWorkflowStepFailed]: a
         nonrecoverable failure was observed while draining the peer. Because the
         waiting helper reports [Exhausted] on zero fuel, [StepFailed] implies
         nonzero network fuel, so the fuel-boundary guarantee still holds. *)
      assert (pure (status == ServerWorkflowStepFailed));
      assert (pure (SZ.v network_fuel <> 0));
      assert (pure (server_driver_close_status_correct wait_for_peer ServerWorkflowStepFailed));
      assert (pure (server_driver_close_wait_correct wait_for_peer ServerWorkflowStepFailed st_wait));
      assert (pure (server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowStepFailed));
      assert (exists* st1.
        server_driver_closed d st1 'certificate_chain 'credential_identity **
        pure (st1.CS.cs_model.CS.model_config ==
                'st0.CS.cs_model.CS.model_config /\
              server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
              server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
              server_driver_close_final_correct wait_for_peer 'st0 st1 (Ghost.reveal 'sent) /\
              server_driver_close_status_correct wait_for_peer ServerWorkflowStepFailed /\
              server_driver_close_wait_correct wait_for_peer ServerWorkflowStepFailed st1 /\
              server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowStepFailed));
      ServerWorkflowStepFailed
    }
  } else {
    server_driver_network_reaches_refl st_cn;
    lemma_close_final_correct
      wait_for_peer
      'st0
      st_cn
      st_cn
      (Ghost.reveal 'sent);
    assert (pure (server_driver_close_final_correct
      wait_for_peer 'st0 st_cn (Ghost.reveal 'sent)));
    close_transport_once d;
    assert (server_driver_closed d st_cn 'certificate_chain 'credential_identity);
    assert (pure (server_driver_close_status_correct wait_for_peer ServerWorkflowClosed));
    assert (pure (server_driver_close_wait_correct wait_for_peer ServerWorkflowClosed st_cn));
    assert (pure (server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowClosed));
    assert (exists* st1.
      server_driver_closed d st1 'certificate_chain 'credential_identity **
      pure (st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config /\
            server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
            server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
            server_driver_close_final_correct wait_for_peer 'st0 st1 (Ghost.reveal 'sent) /\
            server_driver_close_status_correct wait_for_peer ServerWorkflowClosed /\
            server_driver_close_wait_correct wait_for_peer ServerWorkflowClosed st1 /\
            server_driver_close_fuel_correct wait_for_peer network_fuel ServerWorkflowClosed));
    ServerWorkflowClosed
  }
}

fn abort
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity
{
  close_transport_once d;
}
