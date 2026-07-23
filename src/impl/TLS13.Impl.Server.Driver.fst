module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BL = TLS13.Impl.Server.Driver.BufferedLifecycle
module BH = TLS13.Impl.Server.Driver.BufferedHandshake
module BLoc = TLS13.Impl.Server.Driver.BufferedLocal
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module BW = TLS13.Impl.Server.Driver.BufferedWorkflow
module BTH = TLS13.Impl.Server.Driver.BufferedTopHandshake
module BC = TLS13.Impl.Server.Driver.BufferedChannel
module BA = TLS13.Impl.Server.Driver.BufferedAccept
module BSnd = TLS13.Impl.Server.Driver.BufferedSend
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
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
module ID = FStar.IndefiniteDescription
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SMLog = TLS13.Spec.StateMachine.Log
module S = TLS13.Impl.Server
module DS = TLS13.Impl.Server.Driver.State
module DT = TLS13.Impl.Server.Driver.Transport
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DH = TLS13.Impl.Server.Driver.Handshake
module ET = TLS13.Impl.Endpoint.Types
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
module SChannel = TLS13.Impl.Server.ChannelImplementation
module SS = TLS13.Impl.Server.Send
module TChannel = TLS13.Impl.Channel
module GSHbody = TLS13.Wire.Generated.ServerHello_body

noextract
let server_driver_canonical = DS.server_driver_canonical

noextract
let server_driver_canonical_progress = DS.server_driver_canonical_progress

noextract
let server_driver_wire_logs_match = DS.server_driver_wire_logs_match

noextract
let server_driver_live = DS.server_driver_live

let lemma_server_initial_can_start
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (CM.can_start_server
        (CR.server_initial_state certificate_chain credential_identity))
=
  ()

let lemma_server_application_keys_control_not_failed
  (st:CS.connection_state)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures ST.server_connection_control_not_failed st)
=
  ()

noextract
let server_driver_connected = DS.server_driver_connected
noextract
let server_driver_closed = DS.server_driver_closed
noextract
let server_driver_released
  (d:server_driver)
  (st:CS.connection_state)
  : slprop =
  CR.connection_released d.DS.server_driver_server st **
  DS.server_driver_canonical_progress d st **
  (exists* h. MR.pts_to d.DS.server_driver_tcp_history #1.0R h)

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

fn new_server_listener
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns result: option server_listener
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | Some listener -> IO.is_listener listener 'bind_host_bytes port
           | None -> emp)
{
  IO.listen_tcp bind_host bind_host_len port
}

fn free_server_listener (listener:server_listener)
  requires IO.is_listener listener 'bind_host_bytes 'port
  ensures emp
{
  IO.close_listener listener
}

fn new_server_credentials
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_credentials
  ensures exists* credential_identity.
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some credentials ->
             O.is_server_credentials
               credentials
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity
           | None -> emp)
{
  O.server_credentials_new
    certificate_chain
    certificate_chain_len
    private_key
    private_key_len
}

fn free_server_credentials (credentials:server_credentials)
  requires O.is_server_credentials
    credentials
    'certificate_chain
    'credential_identity
  ensures emp
{
  O.server_credentials_free credentials
}

fn new_server_with_credentials
  (credentials:server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires (exists* credential_identity.
             O.is_server_credentials
               credentials
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity) **
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                B.length 'private_key_bytes == SZ.v private_key_len /\
                B.length 'certificate_chain_bytes <=
                  Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (exists* credential_identity.
            O.is_server_credentials
              credentials
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity **
            (match result with
             | Some d ->
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
             | None -> emp))
{
  with credential_identity.
    assert (O.is_server_credentials
      credentials
      (Ghost.reveal 'certificate_chain_bytes)
      credential_identity);
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
      let creds = O.server_credentials_clone credentials;
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
      let tcp_history =
        MR.alloc
          #_
          #CI.io_history_preorder
          (DS.server_driver_history B.empty B.empty);
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
        server_driver_tcp_history = tcp_history;
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
      rewrite
        (MR.pts_to tcp_history #1.0R
          (DS.server_driver_history B.empty B.empty))
        as
        (MR.pts_to d.server_driver_tcp_history #1.0R
          (DS.server_driver_history B.empty B.empty));
      fold (DS.server_driver_io_history d B.empty B.empty);
      DS.lemma_initial_wire_logs_match
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      assert (pure (ST.server_end_to_end_invariant
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)));
      assert (pure (DS.server_driver_config_matches_credentials
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity));
      assert (pure (DS.server_driver_supported_profile_selection
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        credential_identity));
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
      lemma_server_initial_can_start
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity;
      assert (pure (ST.server_state_correct
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)));
      assert (pure (CM.can_start_server
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)));
      assert (pure (ST.server_end_to_end_invariant
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)));
      assert (pure (Ghost.reveal
        (server_driver_canonical d).SP.canonical_server_initial ==
        CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
      Some d
  }
}

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
           | None -> emp) **
          pure
           (not (B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len) ==>
            result == None)
{
  let within_bound =
    SZ.lte certificate_chain_len Bounds.max_server_certificate_chain_len_sz;
  if within_bound {
    assert (pure (B.length 'certificate_chain_bytes <=
                  Bounds.max_server_certificate_chain_len));
    let credentials_opt =
      new_server_credentials
        certificate_chain
        certificate_chain_len
        private_key
        private_key_len;
    match credentials_opt {
      None -> { None }
      Some credentials -> {
        with credential_identity.
          assert (O.is_server_credentials
            credentials
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity);
        let result =
          new_server_with_credentials
            credentials
            certificate_chain
            certificate_chain_len
            private_key
            private_key_len
            #supported_profile_provider;
        match result {
          None -> {
            free_server_credentials credentials;
            None
          }
          Some d -> {
            free_server_credentials credentials;
            Some d
          }
        }
      }
    }
  } else {
    None
  }
}

fn accept_connected
  (d:server_driver)
  (source:DT.server_transport_source)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires DT.owns_server_transport_source source 'bind_host_bytes port **
           server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
  ensures DT.owns_server_transport_source source 'bind_host_bytes port **
          pts_to bind_host 'bind_host_bytes **
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
      source
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
                            lemma_server_application_keys_control_not_failed st3;
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

fn accept_from_source
  (d:server_driver)
  (source:DT.server_transport_source)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires DT.owns_server_transport_source source 'bind_host_bytes port **
           server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
  ensures DT.owns_server_transport_source source 'bind_host_bytes port **
          pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowOk ->
            exists* wire_received wire_sent pending app_log.
              DS.server_channel_inv
                d wire_received wire_sent pending app_log
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed
                 d st1 'certificate_chain 'credential_identity
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
  let status =
    accept_connected
      d source bind_host bind_host_len port local_fuel network_fuel;
  match status {
    ServerWorkflowOk -> {
      with st1 received sent.
        assert (server_driver_connected
          d st1 'certificate_chain 'credential_identity received sent);
      SChannel.pack_connected_channel
        d
        (Ghost.hide st1)
        (Ghost.hide (Ghost.reveal 'certificate_chain))
        (Ghost.hide (Ghost.reveal 'credential_identity))
        (Ghost.hide received)
        (Ghost.hide sent);
      ServerWorkflowOk
    }
    ServerWorkflowNeedMoreInput -> { ServerWorkflowNeedMoreInput }
    ServerWorkflowStepFailed -> { ServerWorkflowStepFailed }
    ServerWorkflowExhausted -> { ServerWorkflowExhausted }
    ServerWorkflowClosed -> { ServerWorkflowClosed }
    ServerWorkflowPayloadTooLarge -> { ServerWorkflowPayloadTooLarge }
    ServerWorkflowOutputBufferTooSmall -> {
      ServerWorkflowOutputBufferTooSmall
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
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowOk ->
             exists* wire_received wire_sent pending app_log.
               DS.server_channel_inv d wire_received wire_sent pending app_log
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed
                 d st1 'certificate_chain 'credential_identity
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
  fold (DT.owns_server_transport_source None 'bind_host_bytes port);
  let status =
    accept_from_source
      d None bind_host bind_host_len port local_fuel network_fuel;
  unfold (DT.owns_server_transport_source None 'bind_host_bytes port);
  status
}

fn accept_with_listener
  (d:server_driver)
  (listener:server_listener)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires IO.is_listener listener 'bind_host_bytes port **
           server_driver_live d 'st0 'certificate_chain 'credential_identity **
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
  ensures IO.is_listener listener 'bind_host_bytes port **
          pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowOk ->
            exists* wire_received wire_sent pending app_log.
              DS.server_channel_inv
                d wire_received wire_sent pending app_log
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed
                 d st1 'certificate_chain 'credential_identity
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
  rewrite (IO.is_listener listener 'bind_host_bytes port) as
    (DT.owns_server_transport_source
      (Some listener) 'bind_host_bytes port);
  let status =
    accept_from_source
      d (Some listener) bind_host bind_host_len port local_fuel network_fuel;
  rewrite
    (DT.owns_server_transport_source
      (Some listener) 'bind_host_bytes port) as
    (IO.is_listener listener 'bind_host_bytes port);
  status
}

let lemma_local_send_application_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  (network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp ST.LocalSendApplicationData payload network_out app_out)
      (ensures
        TChannel.application_log st1 ==
          (if resp.ST.status == ST.StepOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  assert (ST.legal_handled_local_response
    st0 st1 resp ST.LocalSendApplicationData payload network_out app_out);
  if resp.ST.status == ST.StepOk then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp ST.LocalSendApplicationData payload ev
            raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0 st1 resp ST.LocalSendApplicationData payload ev
            raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0 st1 resp ST.LocalSendApplicationData payload ev
            raw_sent raw_received network_out app_out) in
    ST.lemma_legal_response_for_event_app_log_delta
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (SMLog.conn_event_app_sent_delta ev == [payload]);
    assert (SMLog.conn_event_app_received_delta ev == [])
  ) else (
    assert (ST.unexpected_message_response
      st0 st1 resp network_out app_out);
    ST.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out
  )

let lemma_driver_send_application_log
  (st0 st1:CS.connection_state)
  (status:server_workflow_status)
  (payload sent0 sent1:B.bytes)
  : Lemma
      (requires
        server_driver_send_correct st0 st1 status payload sent0 sent1)
      (ensures
        TChannel.application_log st1 ==
          (if status == ServerWorkflowOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  if status == ServerWorkflowPayloadTooLarge then   ()

  else (
    let resp =
      ID.indefinite_description_ghost
        ST.server_response
        (fun resp ->
          DL.server_driver_local_write_correct
            st0 st1 resp ST.LocalSendApplicationData payload sent0 sent1 /\
          server_driver_send_status_correct status resp) in
    let network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun network_out -> exists app_out.
          ST.server_local_event_end_to_end_correct
            st0 st1 resp ST.LocalSendApplicationData payload
            network_out app_out /\
          Seq.equal sent1
            (B.append sent0 (ST.response_network_out resp network_out))) in
    let app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun app_out ->
          ST.server_local_event_end_to_end_correct
            st0 st1 resp ST.LocalSendApplicationData payload
            network_out app_out /\
          Seq.equal sent1
            (B.append sent0 (ST.response_network_out resp network_out))) in
    lemma_local_send_application_log
      st0 st1 resp payload network_out app_out
  )

let lemma_server_send_correct_from_local
  (st0 st1:CS.connection_state)
  (status:server_workflow_status)
  (resp:ST.server_response)
  (payload sent sent':B.bytes)
  : Lemma
      (requires
        status <> ServerWorkflowPayloadTooLarge /\
        DL.server_driver_local_write_correct
          st0 st1 resp ST.LocalSendApplicationData payload sent sent' /\
        server_driver_send_status_correct status resp)
      (ensures
        server_driver_send_correct st0 st1 status payload sent sent')
=
  FStar.Classical.exists_intro
    (fun response ->
      DL.server_driver_local_write_correct
        st0 st1 response ST.LocalSendApplicationData payload sent sent' /\
      server_driver_send_status_correct status response)
    resp

let server_workflow_status_of_response
  (resp:ST.server_response)
  : server_workflow_status =
  match resp.ST.status with
  | ST.StepOk -> ServerWorkflowOk
  | _ -> ServerWorkflowStepFailed

let lemma_server_workflow_status_of_response_correct
  (resp:ST.server_response)
  : Lemma
      (server_workflow_status_of_response resp <>
         ServerWorkflowPayloadTooLarge /\
       server_driver_send_status_correct
         (server_workflow_status_of_response resp)
         resp)
=
  match resp.ST.status with
  | ST.StepOk -> ()
  | ST.NeedMoreInput -> ()
  | ST.DecodeError -> ()
  | ST.IllegalTransition -> ()
  | ST.OutputBufferTooSmall -> ()
  | ST.ConnectionFailed -> ()

let lemma_channel_send_log
  (status:server_workflow_status)
  (payload:B.bytes)
  (base_log old_log new_log:CI.application_log B.bytes)
  : Lemma
      (requires
        old_log == base_log /\
        new_log ==
          (if status == ServerWorkflowOk
           then CI.append_sent base_log payload
           else base_log))
      (ensures
        new_log ==
          (if channel_send_succeeded status
           then
             CI.append_sent old_log (channel_message_of_bytes payload)
           else old_log))
=
  match status with
  | ServerWorkflowOk -> ()
  | ServerWorkflowNeedMoreInput -> ()
  | ServerWorkflowStepFailed -> ()
  | ServerWorkflowExhausted -> ()
  | ServerWorkflowClosed -> ()
  | ServerWorkflowPayloadTooLarge -> ()
  | ServerWorkflowOutputBufferTooSmall -> ()

let lemma_server_send_transition_intro
  (status:server_workflow_status)
  (payload old_received old_sent:B.bytes)
  (old_log:CI.application_log B.bytes)
  (new_received new_sent:B.bytes)
  (new_log:CI.application_log B.bytes)
  : Lemma
      (requires
        CPI.histories_ahead
          old_received old_sent new_received new_sent /\
        new_log ==
          (if channel_send_succeeded status
           then
             CI.append_sent old_log (channel_message_of_bytes payload)
           else old_log))
      (ensures
        CI.send_transition
          channel_message_of_bytes
          channel_send_succeeded
          status
          payload
          old_received
          old_sent
          old_log
          new_received
          new_sent
          new_log)
=
  ()

let lemma_slice_from_zero_length
  (bytes:B.bytes)
  (len:nat)
  : Lemma
      (requires len <= B.length bytes)
      (ensures B.length (Seq.slice bytes 0 len) == len)
=
  Seq.lemma_len_slice bytes 0 len

let lemma_server_receive_correct_exists
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent0 sent1 app_out out_bytes:B.bytes)
  : Lemma
      (requires
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes)
      (ensures
        exists loop' app_out'.
          server_driver_receive_correct
            st0 st1 result loop' sent0 sent1 app_out' out_bytes)
=
  FStar.Classical.exists_intro
    (fun app_out' ->
      server_driver_receive_correct
        st0 st1 result loop sent0 sent1 app_out' out_bytes)
    app_out;
  FStar.Classical.exists_intro
    (fun loop' -> exists app_out'.
      server_driver_receive_correct
        st0 st1 result loop' sent0 sent1 app_out' out_bytes)
    loop

let lemma_server_receive_nonretry_ready_implication
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  : Lemma
      (requires
        (result.server_receive_status == ServerWorkflowOk \/
         result.server_receive_status == ServerWorkflowStepFailed \/
         result.server_receive_status == ServerWorkflowClosed \/
         result.server_receive_status == ServerWorkflowPayloadTooLarge \/
         result.server_receive_status == ServerWorkflowOutputBufferTooSmall))
      (ensures
        server_driver_application_ready st0 /\
        (result.server_receive_status == ServerWorkflowExhausted \/
         result.server_receive_status == ServerWorkflowNeedMoreInput) ==>
        server_driver_application_ready st1)
=
  match result.server_receive_status with
  | ServerWorkflowOk -> ()
  | ServerWorkflowNeedMoreInput -> ()
  | ServerWorkflowStepFailed -> ()
  | ServerWorkflowExhausted -> ()
  | ServerWorkflowClosed -> ()
  | ServerWorkflowPayloadTooLarge -> ()
  | ServerWorkflowOutputBufferTooSmall -> ()

let lemma_server_receive_endpoint_failed_correct
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent0 sent1 app_out out_bytes:B.bytes)
  : Lemma
      (requires
        loop.DN.server_driver_network_loop_exhausted == false /\
        st1.CS.cs_model.CS.model_control <> CS.ControlClosed /\
        (loop.DN.server_driver_network_loop_last.ST.response.ST.status ==
           ST.DecodeError \/
         loop.DN.server_driver_network_loop_last.ST.response.ST.status ==
           ST.IllegalTransition \/
         loop.DN.server_driver_network_loop_last.ST.response.ST.status ==
           ST.OutputBufferTooSmall \/
         loop.DN.server_driver_network_loop_last.ST.response.ST.status ==
           ST.ConnectionFailed) /\
        result.server_receive_status == ServerWorkflowStepFailed /\
        result.server_receive_len == 0sz /\
        B.length app_out >= SZ.v DState.driver_app_out_capacity /\
        B.length app_out <= B.length out_bytes /\
        DN.server_driver_network_process_correct
          st0
          st1
          loop.DN.server_driver_network_loop_last
          sent0
          sent1 /\
        DN.server_driver_network_process_correct_for_app_out
          st0
          st1
          loop.DN.server_driver_network_loop_last
          sent0
          sent1
          app_out)
      (ensures
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes)
=
  match loop.DN.server_driver_network_loop_last.ST.response.ST.status with
  | ST.StepOk -> ()
  | ST.NeedMoreInput -> ()
  | ST.DecodeError -> ()
  | ST.IllegalTransition -> ()
  | ST.OutputBufferTooSmall -> ()
  | ST.ConnectionFailed -> ()

let lemma_server_receive_closed_correct
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent0 sent1 app_out out_bytes:B.bytes)
  : Lemma
      (requires
        loop.DN.server_driver_network_loop_exhausted == false /\
        st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
        result.server_receive_status == ServerWorkflowClosed /\
        result.server_receive_len == 0sz /\
        B.length app_out >= SZ.v DState.driver_app_out_capacity /\
        B.length app_out <= B.length out_bytes /\
        DN.server_driver_network_process_correct
          st0
          st1
          loop.DN.server_driver_network_loop_last
          sent0
          sent1 /\
        DN.server_driver_network_process_correct_for_app_out
          st0
          st1
          loop.DN.server_driver_network_loop_last
          sent0
          sent1
          app_out)
      (ensures
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes)
=
  ()

let lemma_server_receive_exhausted_correct
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent0 sent1 app_out out_bytes:B.bytes)
  : Lemma
      (requires
        loop.DN.server_driver_network_loop_exhausted == true /\
        result.server_receive_status == ServerWorkflowExhausted /\
        result.server_receive_len == 0sz /\
        st1 == st0 /\
        Seq.equal sent1 sent0 /\
        B.length app_out >= SZ.v DState.driver_app_out_capacity /\
        B.length app_out <= B.length out_bytes)
      (ensures
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes)
=
  ()

let lemma_server_receive_copyout_ok
  (result:server_receive_result)
  (resp:ST.server_response)
  (app_out out_bytes:B.bytes)
  : Lemma
      (requires
        result.server_receive_status == ServerWorkflowOk /\
        SZ.v result.server_receive_len <= B.length out_bytes /\
        result.server_receive_len == resp.ST.app_out_len /\
        Seq.equal
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
          (ST.response_app_out resp app_out))
      (ensures
        server_driver_receive_copyout_correct
          result resp app_out out_bytes)
=
  ()

let lemma_server_receive_status_ok
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (st1:CS.connection_state)
  (app_out out_bytes:B.bytes)
  : Lemma
      (requires
        loop.DN.server_driver_network_loop_exhausted == false /\
        st1.CS.cs_model.CS.model_control <> CS.ControlClosed /\
        loop.DN.server_driver_network_loop_last.ST.response.ST.status ==
          ST.StepOk /\
        SZ.v
          loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length out_bytes /\
        SZ.v
          loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length app_out /\
        result.server_receive_status == ServerWorkflowOk /\
        result.server_receive_len ==
          loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len)
      (ensures
        server_driver_receive_status_correct
          result loop st1 app_out out_bytes)
=
  ()

fn sizet_gt_refined (x y:SZ.t)
  requires emp
  returns b:bool
  ensures pure (b == (SZ.v x > SZ.v y))
{
  SZ.gt x y
}

let lemma_legal_response_observable_receive_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent raw_received network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        SMLog.conn_event_app_sent_delta ev == [])
      (ensures
        (let output = ST.response_app_out resp app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output)))
=
  ST.lemma_legal_response_for_event_app_log_delta
    st0 st1 resp ev raw_sent raw_received network_out app_out;
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData _ ->
       assert False
     | CL.Received, M.TlsApplicationData bytes ->
       assert (Seq.equal (ST.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _, _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalDeliverApplicationData bytes ->
       assert (Seq.equal (ST.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])

let lemma_server_network_process_application_log
  (st0 st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (sent0 sent1 app_out:B.bytes)
  : Lemma
      (requires
        DN.server_driver_network_process_correct_for_app_out
          st0 st1 buffer_resp sent0 sent1 app_out)
      (ensures
        (let output = ST.response_app_out buffer_resp.ST.response app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output) /\
         (st1.CS.cs_model.CS.model_control == CS.ControlClosed ==>
           B.length output == 0)))
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        Seq.equal sent1
          (B.append sent0
            (ST.response_network_out buffer_resp.ST.response network_out))) in
  let network_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        Seq.equal sent1
          (B.append sent0
            (ST.response_network_out buffer_resp.ST.response network_out))) in
  let resp = buffer_resp.ST.response in
  match resp.ST.status with
  | ST.StepOk ->
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal
            st0 msg (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.server_decoded_message_event_projection
            st0 st1 resp msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else ST.server_protected_record_decode_correct
             st0 (ST.server_network_consumed_prefix buffer_resp input) msg)) in
    if ST.legal_network_response
         st0
         st1
         resp
         msg
         (ST.server_network_consumed_prefix buffer_resp input)
         network_out
         app_out
    then (
      lemma_legal_response_observable_receive_log
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      if st1.CS.cs_model.CS.model_control == CS.ControlClosed then
        ST.lemma_legal_response_closed_app_out_empty
          st0
          st1
          resp
          (ST.received_message_event msg)
          B.empty
          (ST.server_network_consumed_prefix buffer_resp input)
          network_out
          app_out
    )
    else (
      assert (ST.unexpected_message_response
        st0 st1 resp network_out app_out);
      assert False
    )
  | ST.ConnectionFailed ->
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 == CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
            st0.CS.cs_model
            (ST.received_message_event (M.TlsAlert alert))
            raw_received) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 == CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0 st1 resp (M.TlsAlert alert) raw_received network_out app_out /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
            st0.CS.cs_model
            (ST.received_message_event (M.TlsAlert alert))
            raw_received) in
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out;
    if st1.CS.cs_model.CS.model_control == CS.ControlClosed then
      ST.lemma_legal_response_closed_app_out_empty
        st0
        st1
        resp
        (ST.received_message_event (M.TlsAlert alert))
        B.empty
        raw_received
        network_out
        app_out
  | ST.DecodeError ->
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    if st1.CS.cs_model.CS.model_control == CS.ControlClosed then
      ST.lemma_legal_response_closed_app_out_empty
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
        B.empty
        B.empty
        network_out
        app_out
  | ST.NeedMoreInput -> assert (st1 == st0)
  | ST.IllegalTransition -> assert (st1 == st0)
  | ST.OutputBufferTooSmall -> assert False

let lemma_driver_receive_application_log
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent0 sent1 app_out out_bytes:B.bytes)
  : Lemma
      (requires
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes /\
        B.length out_bytes >= SZ.v DS.driver_app_out_capacity)
      (ensures
        TChannel.application_log st1 ==
          (if channel_receive_succeeded result
           then
             CI.append_received
               (TChannel.application_log st0)
               (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
           else TChannel.application_log st0))
=
  if loop.DN.server_driver_network_loop_exhausted then
    assert (st1 == st0)
  else (
    lemma_server_network_process_application_log
      st0
      st1
      loop.DN.server_driver_network_loop_last
      sent0
      sent1
      app_out;
    let resp = loop.DN.server_driver_network_loop_last.ST.response in
    if result.server_receive_status == ServerWorkflowOk then (
      assert (resp.ST.status == ST.StepOk);
      assert (result.server_receive_len == resp.ST.app_out_len);
      assert (Seq.equal
        (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
        (ST.response_app_out resp app_out));
      if B.length (ST.response_app_out resp app_out) = 0 then (
        assert (SZ.v result.server_receive_len <= B.length out_bytes);
        lemma_slice_from_zero_length
          out_bytes (SZ.v result.server_receive_len);
        assert (B.length
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len)) ==
          SZ.v result.server_receive_len);
        Seq.lemma_eq_elim
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
          (ST.response_app_out resp app_out);
        assert (B.length
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len)) == 0);
        assert (B.length
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len)) ==
          SZ.v result.server_receive_len);
        assert (SZ.v result.server_receive_len == 0)
      ) else (
        lemma_slice_from_zero_length
          out_bytes
          (SZ.v result.server_receive_len);
        Seq.lemma_eq_elim
          (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
          (ST.response_app_out resp app_out)
      )
    ) else (
      assert (resp.ST.status <> ST.StepOk \/
        st1.CS.cs_model.CS.model_control == CS.ControlClosed);
      match resp.ST.status with
      | ST.StepOk ->
        assert (st1.CS.cs_model.CS.model_control == CS.ControlClosed);
        assert (B.length (ST.response_app_out resp app_out) == 0)
      | _ ->
        assert (B.length (ST.response_app_out resp app_out) == 0)
    )
  )

let lemma_driver_receive_exists_application_log
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (sent0 sent1 out_bytes:B.bytes)
  : Lemma
      (requires
        (exists loop app_out.
          server_driver_receive_correct
            st0 st1 result loop sent0 sent1 app_out out_bytes) /\
        B.length out_bytes >= SZ.v DS.driver_app_out_capacity)
      (ensures
        TChannel.application_log st1 ==
          (if channel_receive_succeeded result
           then
             CI.append_received
               (TChannel.application_log st0)
               (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
           else TChannel.application_log st0))
=
  let loop =
    ID.indefinite_description_ghost
      DN.server_driver_network_loop_result
      (fun loop -> exists app_out.
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes) in
  let app_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out ->
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes) in
  lemma_driver_receive_application_log
    st0 st1 result loop sent0 sent1 app_out out_bytes

fn send_connected
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
  let too_large = sizet_gt_refined payload_len 16384sz;
  if too_large {
    assert (pure (SZ.v payload_len > 16384));
    assert_norm (SM.max_application_data_fragment_len == 16384);
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
  let status = server_workflow_status_of_response resp;
  lemma_server_workflow_status_of_response_correct resp;
  lemma_server_send_correct_from_local
    'st0
    st1
    status
    resp
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    sent';
  status
  }
}

(**
  Helper lemmas (private to this module) establishing that the *usable*
  send/receive outcomes leave the control state non-failed.  These are the
  facts required to repackage [server_channel_inv] (the live invariant, which
  demands a non-failed protocol control state) after [send_connected] /
  [receive_connected].  The hard-failed ([ServerWorkflowStepFailed]) outcomes
  instead pack [server_channel_terminal], which makes no such claim.
**)

(* Sending application data from [ControlApplicationData] preserves control. *)
let lemma_step_sent_app_data_control
  (model0 model1:CS.connection_model)
  (bytes:B.bytes)
  : Lemma
      (requires
        model0.CS.model_control == CS.ControlApplicationData /\
        CS.step_tls_message model0 CL.Sent (M.TlsApplicationData bytes) ==
          Some model1)
      (ensures model1.CS.model_control == CS.ControlApplicationData)
=
  ()

(* Each of the five StepOk [received_*] states is non-failed (given a
   non-failed predecessor for the two that keep the control state). *)
let lemma_received_step_ok_not_failed
  (st0 st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  : Lemma
      (requires
        ST.server_network_step_ok_consumed_prefix st0 st1 resp input /\
        resp.ST.response.ST.status == ST.StepOk /\
        ST.server_connection_control_not_failed st0)
      (ensures ST.server_connection_control_not_failed st1)
=
  ()

(* A StepOk local-send of application data keeps control == ControlApplicationData. *)
let lemma_local_send_application_data_control
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp ST.LocalSendApplicationData payload network_out app_out /\
        resp.ST.status == ST.StepOk /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
=
  assert (ST.legal_handled_local_response
    st0 st1 resp ST.LocalSendApplicationData payload network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  assert (ST.local_event_kind_matches ST.LocalSendApplicationData payload ev);
  assert (CS.legal_connection_delta
    st0
    ({ CS.delta_event = ev;
       CS.delta_raw_sent = raw_sent;
       CS.delta_raw_received = raw_received })
    st1);
  assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes ->
       assert (msg.CL.message_direction == CL.Sent);
       assert (CS.step_tls_message st0.CS.cs_model CL.Sent
                 (M.TlsApplicationData bytes) == Some st1.CS.cs_model);
       lemma_step_sent_app_data_control st0.CS.cs_model st1.CS.cs_model bytes
     | _ -> assert False)
  | _ -> assert False

(* Any usable (non-StepFailed) send outcome leaves the state non-failed. *)
let lemma_driver_send_usable_not_failed
  (st0 st1:CS.connection_state)
  (status:server_workflow_status)
  (payload sent0 sent1:B.bytes)
  : Lemma
      (requires
        server_driver_send_correct st0 st1 status payload sent0 sent1 /\
        server_driver_application_ready st0 /\
        status <> ServerWorkflowStepFailed)
      (ensures ST.server_connection_control_not_failed st1)
=
  if status = ServerWorkflowPayloadTooLarge then (
    assert (st1 == st0);
    lemma_server_application_keys_control_not_failed st1
  ) else (
    let resp =
      ID.indefinite_description_ghost
        ST.server_response
        (fun resp ->
          DL.server_driver_local_write_correct
            st0 st1 resp ST.LocalSendApplicationData payload sent0 sent1 /\
          server_driver_send_status_correct status resp) in
    assert (resp.ST.status == ST.StepOk);
    let network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun network_out -> exists app_out.
          ST.server_local_event_end_to_end_correct
            st0 st1 resp ST.LocalSendApplicationData payload network_out app_out /\
          Seq.equal sent1
            (B.append sent0 (ST.response_network_out resp network_out))) in
    let app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun app_out ->
          ST.server_local_event_end_to_end_correct
            st0 st1 resp ST.LocalSendApplicationData payload network_out app_out /\
          Seq.equal sent1
            (B.append sent0 (ST.response_network_out resp network_out))) in
    lemma_local_send_application_data_control
      st0 st1 resp payload network_out app_out;
    lemma_server_application_keys_control_not_failed st1
  )

(* Any usable (non-StepFailed) receive outcome leaves the state non-failed. *)
#push-options "--split_queries always"
let lemma_driver_receive_usable_not_failed
  (st0 st1:CS.connection_state)
  (result:server_receive_result)
  (sent0 sent1 out_bytes:B.bytes)
  : Lemma
      (requires
        (exists loop app_out.
          server_driver_receive_correct
            st0 st1 result loop sent0 sent1 app_out out_bytes) /\
        ST.server_connection_control_not_failed st0 /\
        result.server_receive_status <> ServerWorkflowStepFailed)
      (ensures ST.server_connection_control_not_failed st1)
=
  let loop =
    ID.indefinite_description_ghost
      DN.server_driver_network_loop_result
      (fun loop -> exists app_out.
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes) in
  let app_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out ->
        server_driver_receive_correct
          st0 st1 result loop sent0 sent1 app_out out_bytes) in
  if loop.DN.server_driver_network_loop_exhausted then (
    assert (st1 == st0)
  ) else (
    if st1.CS.cs_model.CS.model_control = CS.ControlClosed then (
      ()
    ) else (
      let resp = loop.DN.server_driver_network_loop_last in
      let input =
        ID.indefinite_description_ghost
          B.bytes
          (fun input -> exists net app2.
            ST.server_network_bytes_end_to_end_correct st0 st1 resp input net app2 /\
            ST.server_network_consumed_input_projection st0 st1 resp input net app2 /\
            Seq.equal sent1
              (B.append sent0 (ST.response_network_out resp.ST.response net))) in
      let net =
        ID.indefinite_description_ghost
          B.bytes
          (fun net -> exists app2.
            ST.server_network_bytes_end_to_end_correct st0 st1 resp input net app2 /\
            ST.server_network_consumed_input_projection st0 st1 resp input net app2 /\
            Seq.equal sent1
              (B.append sent0 (ST.response_network_out resp.ST.response net))) in
      let app2 =
        ID.indefinite_description_ghost
          B.bytes
          (fun app2 ->
            ST.server_network_bytes_end_to_end_correct st0 st1 resp input net app2 /\
            ST.server_network_consumed_input_projection st0 st1 resp input net app2 /\
            Seq.equal sent1
              (B.append sent0 (ST.response_network_out resp.ST.response net))) in
      match resp.ST.response.ST.status with
      | ST.StepOk -> lemma_received_step_ok_not_failed st0 st1 resp input
      | ST.NeedMoreInput -> ()
      | _ -> ()
    )
  )
#pop-options


fn send
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DS.server_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:server_workflow_status
  ensures exists* wire_received1 wire_sent1 pending1 app_log1.
          (if channel_send_usable status
           then
             DS.server_channel_inv
               d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.server_channel_terminal
               d wire_received1 wire_sent1 app_log1) **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  SChannel.take_channel_snapshot d wire_received0 wire_sent0 pending0 app_log0;
  SChannel.open_channel_invariant d wire_received0 wire_sent0 pending0 app_log0;
  with st0 certificate_chain credential_identity.
    assert (server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  assert (pure ((Ghost.reveal app_log0) == TChannel.application_log st0));
  unfold (server_driver_connected
    d st0 certificate_chain credential_identity
    (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  with ch buffered buffered_len.
    assert (S.connection_exactly d.server_driver_server st0);
  rewrite (S.connection_exactly d.server_driver_server st0)
    as (CR.connection_exactly d.server_driver_server st0);
  let control_snapshot = CQ.get_control_snapshot d.server_driver_server;
  let app_keys_ready =
    CQ.server_application_record_keys_installed_runtime
      d.server_driver_server;
  rewrite (CR.connection_exactly d.server_driver_server st0)
    as (S.connection_exactly d.server_driver_server st0);
  fold (server_driver_connected
    d st0 certificate_chain credential_identity
    (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  let ready =
    control_snapshot.CR.snapshot_control_tag = 2uy && app_keys_ready;
  if ready {
    lemma_control_snapshot_app_ready control_snapshot st0;
    assert (pure (CS.application_record_keys_installed_for_role
      CS.ServerEndpoint
      st0.CS.cs_model));
    assert (pure (server_driver_application_ready st0));
    let status = send_connected d payload payload_len;
    with st1 sent1.
      assert (server_driver_connected
        d st1 certificate_chain credential_identity
        (Ghost.reveal wire_received0) sent1 **
        pts_to payload (Ghost.reveal payload_bytes));
    lemma_driver_send_application_log
      st0 st1 status (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_sent0) sent1;
    lemma_channel_send_log
      status
      (Ghost.reveal payload_bytes)
      (TChannel.application_log st0)
      (Ghost.reveal app_log0)
      (TChannel.application_log st1);
    if (status <> ServerWorkflowOk && status <> ServerWorkflowPayloadTooLarge) {
      SChannel.pack_connected_channel_terminal
        d (Ghost.hide st1) (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity) wire_received0 (Ghost.hide sent1);
      SChannel.recall_channel_snapshot_terminal
        d wire_received0 wire_sent0 app_log0
        wire_received0 (Ghost.hide sent1)
        (Ghost.hide (TChannel.application_log st1));
      lemma_server_send_transition_intro
        status (Ghost.reveal payload_bytes)
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0)
        (Ghost.reveal wire_received0) sent1 (TChannel.application_log st1);
      drop_ (DS.server_channel_snapshot
        d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0));
      rewrite (DS.server_channel_terminal
                 d (Ghost.reveal wire_received0) sent1
                 (TChannel.application_log st1))
        as (if channel_send_usable status
            then DS.server_channel_inv
                   d (Ghost.reveal wire_received0) sent1
                   (Ghost.reveal pending0) (TChannel.application_log st1)
            else DS.server_channel_terminal
                   d (Ghost.reveal wire_received0) sent1
                   (TChannel.application_log st1));
      status
    } else {
      lemma_driver_send_usable_not_failed
        st0 st1 status (Ghost.reveal payload_bytes)
        (Ghost.reveal wire_sent0) sent1;
      SChannel.pack_connected_channel_invariant
        d (Ghost.hide st1) (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity) wire_received0 (Ghost.hide sent1);
      with pending1.
        assert (DS.server_channel_inv
          d (Ghost.reveal wire_received0) sent1 pending1
          (TChannel.application_log st1));
      SChannel.recall_channel_snapshot
        d wire_received0 wire_sent0 app_log0
        wire_received0 (Ghost.hide sent1) (Ghost.hide pending1)
        (Ghost.hide (TChannel.application_log st1));
      lemma_server_send_transition_intro
        status (Ghost.reveal payload_bytes)
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0)
        (Ghost.reveal wire_received0) sent1 (TChannel.application_log st1);
      drop_ (DS.server_channel_snapshot
        d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0));
      rewrite (DS.server_channel_inv
                 d (Ghost.reveal wire_received0) sent1 pending1
                 (TChannel.application_log st1))
        as (if channel_send_usable status
            then DS.server_channel_inv
                   d (Ghost.reveal wire_received0) sent1 pending1
                   (TChannel.application_log st1)
            else DS.server_channel_terminal
                   d (Ghost.reveal wire_received0) sent1
                   (TChannel.application_log st1));
      status
    }
  } else {
    SChannel.pack_connected_channel_terminal
      d (Ghost.hide st0) (Ghost.hide certificate_chain)
      (Ghost.hide credential_identity) wire_received0 wire_sent0;
    SChannel.recall_channel_snapshot_terminal
      d wire_received0 wire_sent0 app_log0
      wire_received0 wire_sent0
      (Ghost.hide (TChannel.application_log st0));
    lemma_channel_send_log
      ServerWorkflowStepFailed (Ghost.reveal payload_bytes)
      (TChannel.application_log st0) (Ghost.reveal app_log0)
      (TChannel.application_log st0);
    lemma_server_send_transition_intro
      ServerWorkflowStepFailed (Ghost.reveal payload_bytes)
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0)
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
      (TChannel.application_log st0);
    drop_ (DS.server_channel_snapshot
      d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
      (Ghost.reveal app_log0));
    rewrite (DS.server_channel_terminal
               d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
               (TChannel.application_log st0))
      as (if channel_send_usable ServerWorkflowStepFailed
          then DS.server_channel_inv
                 d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
                 (Ghost.reveal pending0) (TChannel.application_log st0)
          else DS.server_channel_terminal
                 d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
                 (TChannel.application_log st0));
    ServerWorkflowStepFailed
  }
}


fn receive_connected
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
           pure (
             B.length 'out_bytes == SZ.v out_len /\
             SZ.v DS.driver_app_out_capacity <= SZ.v out_len)
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
  redirect_server_driver_connected_output d out out_len;
  let loop =
    read_process_network_until_ready_into d out out_len network_fuel;
  with st1 received' sent' loop_app_out.
    assert (server_driver_connected_with_output
      d
      st1
      'certificate_chain
      'credential_identity
      received'
      sent'
      out
      out_len
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
  unfold (server_driver_connected_with_output
    d
    st1
    'certificate_chain
    'credential_identity
    received'
    sent'
    out
    out_len
    loop_app_out);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch received' sent' **
            server_driver_buffers_with_output
              d buffered buffered_len out out_len loop_app_out **
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
  fold (server_driver_connected_with_output
    d
    st1
    'certificate_chain
    'credential_identity
    received'
    sent'
    out
    out_len
    loop_app_out);
  if (loop.server_driver_network_loop_exhausted) {
    let result = {
      server_receive_status = ServerWorkflowExhausted;
      server_receive_len = 0sz;
    };
    assert_norm (
      result.server_receive_status == ServerWorkflowExhausted);
    assert_norm (result.server_receive_len == 0sz);
    assert (pure (
      loop.server_driver_network_loop_exhausted == true));
    assert (pure (st1 == 'st0));
    assert (pure (Seq.equal sent' (Ghost.reveal 'sent)));
    assert (pure (
      B.length loop_app_out >= SZ.v DS.driver_app_out_capacity));
    lemma_server_receive_exhausted_correct
      'st0
      st1
      result
      loop
      (Ghost.reveal 'sent)
      sent'
      loop_app_out
      loop_app_out;
    release_server_driver_connected_output d out out_len;
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
      assert_norm (
        result.server_receive_status == ServerWorkflowClosed);
      assert_norm (result.server_receive_len == 0sz);
      assert (pure (
        loop.server_driver_network_loop_exhausted == false));
      assert (pure (
        B.length loop_app_out >= SZ.v DS.driver_app_out_capacity));
      assert (pure (server_driver_network_process_correct
        'st0
        st1
        loop.server_driver_network_loop_last
        (Ghost.reveal 'sent)
        sent'));
      assert (pure (server_driver_network_process_correct_for_app_out
        'st0
        st1
        loop.server_driver_network_loop_last
        (Ghost.reveal 'sent)
        sent'
        loop_app_out));
      lemma_server_receive_closed_correct
        'st0
        st1
        result
        loop
        (Ghost.reveal 'sent)
        sent'
        loop_app_out
        loop_app_out;
      release_server_driver_connected_output d out out_len;
      result
    } else {
    assert (pure (control_snapshot.CR.snapshot_control_tag <> 4uy));
    lemma_control_snapshot_not_closed control_snapshot st1;
    match loop.server_driver_network_loop_last.ST.response.ST.status {
      ST.StepOk -> {
        let copy_len = loop.server_driver_network_loop_last.ST.response.ST.app_out_len;
        let app_fits = SZ.lte copy_len out_len;
        if app_fits {
          assert (pure (SZ.v copy_len <= SZ.v out_len));
          assert (pure (SZ.v copy_len <= B.length loop_app_out));
          assert (pure (Seq.equal
            (ST.response_app_out
              loop.server_driver_network_loop_last.ST.response
              loop_app_out)
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          Seq.lemma_len_slice loop_app_out 0 (SZ.v copy_len);
          assert (pure (Seq.equal
            (Seq.slice loop_app_out 0 (SZ.v copy_len))
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          let result = {
            server_receive_status = ServerWorkflowOk;
            server_receive_len = copy_len;
          };
          assert_norm (
            result.server_receive_status == ServerWorkflowOk);
          assert_norm (result.server_receive_len == copy_len);
          assert (pure (
            result.server_receive_len ==
              loop.server_driver_network_loop_last.ST.response.ST.app_out_len));
          assert (pure (
            loop.server_driver_network_loop_exhausted == false));
          assert (pure (
            st1.CS.cs_model.CS.model_control <> CS.ControlClosed));
          lemma_server_receive_status_ok
            result loop st1 loop_app_out loop_app_out;
          assert (pure (
            B.length loop_app_out >= SZ.v DS.driver_app_out_capacity));
          assert (pure (
            SZ.v result.server_receive_len <= B.length loop_app_out));
          assert (pure (server_driver_network_process_correct
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'));
          assert (pure (server_driver_network_process_correct_for_app_out
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'
            loop_app_out));
          lemma_server_receive_copyout_ok
            result
            loop.server_driver_network_loop_last.ST.response
            loop_app_out
            loop_app_out;
          assert (pure (server_driver_receive_correct
            'st0
            st1
            result
            loop
            (Ghost.reveal 'sent)
            sent'
            loop_app_out
            loop_app_out));
          release_server_driver_connected_output d out out_len;
          result
        } else {
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
            loop_app_out));
          release_server_driver_connected_output d out out_len;
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
          loop_app_out));
        release_server_driver_connected_output d out out_len;
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
          loop_app_out));
        release_server_driver_connected_output d out out_len;
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
          loop_app_out));
        release_server_driver_connected_output d out out_len;
        result
      }
      ST.IllegalTransition -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert_norm (
          result.server_receive_status == ServerWorkflowStepFailed);
        assert_norm (result.server_receive_len == 0sz);
        assert (pure (
          loop.server_driver_network_loop_exhausted == false));
        assert (pure (
          st1.CS.cs_model.CS.model_control <> CS.ControlClosed));
        assert_norm (
          loop.server_driver_network_loop_last.ST.response.ST.status ==
            ST.IllegalTransition);
        assert (pure (
          B.length loop_app_out >= SZ.v DS.driver_app_out_capacity));
        assert (pure (server_driver_network_process_correct
          'st0
          st1
          loop.server_driver_network_loop_last
          (Ghost.reveal 'sent)
          sent'));
        assert (pure (server_driver_network_process_correct_for_app_out
          'st0
          st1
          loop.server_driver_network_loop_last
          (Ghost.reveal 'sent)
          sent'
          loop_app_out));
        lemma_server_receive_endpoint_failed_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          loop_app_out;
        release_server_driver_connected_output d out out_len;
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
          loop_app_out));
        release_server_driver_connected_output d out out_len;
        result
      }
    }
    }
  }
}

fn receive
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires DS.server_channel_inv
             d
             (Ghost.reveal wire_received0)
             (Ghost.reveal wire_sent0)
             (Ghost.reveal pending0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* wire_received1 wire_sent1 pending1 app_log1 output.
          (if channel_receive_usable result
           then
             DS.server_channel_inv
               d wire_received1 wire_sent1 pending1 app_log1
           else
             DS.server_channel_terminal
               d wire_received1 wire_sent1 app_log1) **
          pts_to out output **
          pure (
            B.length output == SZ.v out_len /\
            SZ.v result.server_receive_len <= SZ.v out_len /\
            CI.receive_transition
              channel_message_of_bytes
              channel_receive_succeeded
              channel_receive_length
              result
              output
              (Ghost.reveal wire_received0)
              (Ghost.reveal wire_sent0)
              (Ghost.reveal app_log0)
              wire_received1
              wire_sent1
              app_log1)
{
  let output_fits = SZ.lte DS.driver_app_out_capacity out_len;
  if output_fits {
    SChannel.take_channel_snapshot d wire_received0 wire_sent0 pending0 app_log0;
    SChannel.open_channel_invariant d wire_received0 wire_sent0 pending0 app_log0;
    with st0 certificate_chain credential_identity.
      assert (server_driver_connected
        d st0 certificate_chain credential_identity
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
    assert (pure (SZ.v DS.driver_app_out_capacity <= SZ.v out_len));
    let result = receive_connected d out out_len local_fuel network_fuel;
    with st1 received1 sent1 output.
      assert (server_driver_connected
                d st1 certificate_chain credential_identity received1 sent1 **
              pts_to out output);
    assert (pure (exists loop app_out.
      server_driver_receive_correct
        st0 st1 result loop (Ghost.reveal wire_sent0) sent1 app_out output));
    assert (pure (B.length output >= SZ.v DS.driver_app_out_capacity));
    lemma_driver_receive_exists_application_log
      st0 st1 result (Ghost.reveal wire_sent0) sent1 output;
    if (result.server_receive_status <> ServerWorkflowOk
        && result.server_receive_status <> ServerWorkflowNeedMoreInput
        && result.server_receive_status <> ServerWorkflowExhausted
        && result.server_receive_status <> ServerWorkflowOutputBufferTooSmall) {
      SChannel.pack_connected_channel_terminal
        d (Ghost.hide st1) (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity)
        (Ghost.hide received1) (Ghost.hide sent1);
      SChannel.recall_channel_snapshot_terminal
        d wire_received0 wire_sent0 app_log0
        (Ghost.hide received1) (Ghost.hide sent1)
        (Ghost.hide (TChannel.application_log st1));
      drop_ (DS.server_channel_snapshot
        d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0));
      rewrite (DS.server_channel_terminal
                 d received1 sent1 (TChannel.application_log st1))
        as (if channel_receive_usable result
            then DS.server_channel_inv
                   d received1 sent1 (Ghost.reveal pending0)
                   (TChannel.application_log st1)
            else DS.server_channel_terminal
                   d received1 sent1 (TChannel.application_log st1));
      result
    } else {
      lemma_driver_receive_usable_not_failed
        st0 st1 result (Ghost.reveal wire_sent0) sent1 output;
      SChannel.pack_connected_channel_invariant
        d (Ghost.hide st1) (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity)
        (Ghost.hide received1) (Ghost.hide sent1);
      with pending1.
        assert (DS.server_channel_inv
          d received1 sent1 pending1 (TChannel.application_log st1));
      SChannel.recall_channel_snapshot
        d wire_received0 wire_sent0 app_log0
        (Ghost.hide received1) (Ghost.hide sent1) (Ghost.hide pending1)
        (Ghost.hide (TChannel.application_log st1));
      drop_ (DS.server_channel_snapshot
        d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
        (Ghost.reveal app_log0));
      rewrite (DS.server_channel_inv
                 d received1 sent1 pending1 (TChannel.application_log st1))
        as (if channel_receive_usable result
            then DS.server_channel_inv
                   d received1 sent1 pending1 (TChannel.application_log st1)
            else DS.server_channel_terminal
                   d received1 sent1 (TChannel.application_log st1));
      result
    }
  } else {
    let result = {
      server_receive_status = ServerWorkflowOutputBufferTooSmall;
      server_receive_len = 0sz;
    };
    assert (pure (CPI.histories_ahead
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)));
    rewrite (DS.server_channel_inv
               d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
               (Ghost.reveal pending0) (Ghost.reveal app_log0))
      as (if channel_receive_usable result
          then DS.server_channel_inv
                 d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
                 (Ghost.reveal pending0) (Ghost.reveal app_log0)
          else DS.server_channel_terminal
                 d (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
                 (Ghost.reveal app_log0));
    result
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
  step.  If the connection is already closed or already in a control-failure
  state it stops without issuing another (potentially blocking) read.  Each
  step processes an already-buffered record before reading from the socket and
  only recurses when the step status is recoverable
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
        let step = process_buffered_or_read_network_once d;
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

fn close_connected
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

fn abort_connected
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

fn close
  (d:server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires DS.server_channel_inv
             d
             (Ghost.reveal wire_received)
             (Ghost.reveal wire_sent)
             (Ghost.reveal pending)
             (Ghost.reveal app_log)
  returns status:server_workflow_status
  ensures exists* st1 certificate_chain credential_identity.
          server_driver_closed d st1 certificate_chain credential_identity
{
  SChannel.open_channel_invariant d wire_received wire_sent pending app_log;
  with st0 certificate_chain credential_identity.
    assert (server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  unfold (server_driver_connected
    d st0 certificate_chain credential_identity
    (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  with ch buffered buffered_len.
    assert (S.connection_exactly d.server_driver_server st0);
  rewrite (S.connection_exactly d.server_driver_server st0)
    as (CR.connection_exactly d.server_driver_server st0);
  let control_snapshot = CQ.get_control_snapshot d.server_driver_server;
  let app_keys_ready =
    CQ.server_application_record_keys_installed_runtime
      d.server_driver_server;
  rewrite (CR.connection_exactly d.server_driver_server st0)
    as (S.connection_exactly d.server_driver_server st0);
  fold (server_driver_connected
    d st0 certificate_chain credential_identity
    (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  let ready =
    control_snapshot.CR.snapshot_control_tag = 2uy && app_keys_ready;
  if ready {
    lemma_control_snapshot_app_ready control_snapshot st0;
    assert (pure (CS.application_record_keys_installed_for_role
      CS.ServerEndpoint
      st0.CS.cs_model));
    assert (pure (server_driver_application_ready st0));
    close_connected d wait_for_peer network_fuel
  } else {
    abort_connected d;
    ServerWorkflowClosed
  }
}

fn abort
  (d:server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DS.server_channel_inv
             d
             (Ghost.reveal wire_received)
             (Ghost.reveal wire_sent)
             (Ghost.reveal pending)
             (Ghost.reveal app_log)
  ensures exists* st certificate_chain credential_identity.
          server_driver_closed d st certificate_chain credential_identity
{
  SChannel.open_channel_invariant d wire_received wire_sent pending app_log;
  with st certificate_chain credential_identity.
    assert (server_driver_connected
      d st certificate_chain credential_identity
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  abort_connected d
}

fn abort_terminal
  (d:server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DS.server_channel_terminal
             d
             (Ghost.reveal wire_received)
             (Ghost.reveal wire_sent)
             (Ghost.reveal app_log)
  ensures exists* st certificate_chain credential_identity.
          server_driver_closed d st certificate_chain credential_identity
{
  SChannel.open_terminal_invariant d wire_received wire_sent app_log;
  with st certificate_chain credential_identity.
    assert (server_driver_connected
      d st certificate_chain credential_identity
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  abort_connected d
}

inline_for_extraction
fn free_server_driver_buffers
  (d:server_driver)
  requires exists* buffered buffered_len.
    DS.server_driver_buffers d buffered buffered_len
  ensures emp
{
  with buffered buffered_len.
    unfold (DS.server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out local_app_out. _;
  V.free d.DS.server_driver_empty_payload;
  V.free d.DS.server_driver_raw;
  V.free d.DS.server_driver_network_out;
  V.free d.DS.server_driver_material_payload;
  V.free d.DS.server_driver_certificate_verify_input;
  V.free d.DS.server_driver_signature;
  V.free d.DS.server_driver_app_out;
  V.free d.DS.server_driver_local_app_out;
  Box.free d.DS.server_driver_buffered_len;
}

fn free
  (d:server_driver)
  requires server_driver_closed d 'st 'certificate_chain 'credential_identity
  ensures server_driver_released d 'st
{
  unfold (server_driver_closed d 'st 'certificate_chain 'credential_identity);
  with received sent. _;
  unfold (DS.server_driver_io_history d received sent);
  rewrite (S.connection_exactly d.DS.server_driver_server 'st)
    as (CR.connection_exactly d.DS.server_driver_server 'st);
  CR.free_connection d.DS.server_driver_server;
  O.server_credentials_free d.DS.server_driver_credentials;
  Box.free d.DS.server_driver_channel;
  free_server_driver_buffers d;
  fold (server_driver_released d 'st);
}

noextract
let server_channel_implementation
  : CI.channel_implementation
      server_driver
      SP.canonical_server
      CS.connection_state
      TLS13.Spec.Endpoint.Wire.wire_message
      CTypes.server_local_event
      TLS13.Spec.Endpoint.API.local_output
      B.bytes
      server_workflow_status
      server_receive_result
      SP.server_protocol_implementation
  =
  {
    CI.ci_protocol_impl = DS.server_driver_canonical;
    CI.ci_project = TChannel.application_log;
    CI.ci_message_of_bytes = channel_message_of_bytes;
    CI.ci_channel_inv = DS.server_channel_inv;
    CI.ci_terminal_inv = DS.server_channel_terminal;
    CI.ci_snapshot = DS.server_channel_snapshot;
    CI.ci_send_succeeded = channel_send_succeeded;
    CI.ci_send_usable = channel_send_usable;
    CI.ci_receive_succeeded = channel_receive_succeeded;
    CI.ci_receive_usable = channel_receive_usable;
    CI.ci_receive_length = channel_receive_length;
    CI.ci_invariant_valid = SChannel.channel_invariant_valid;
    CI.ci_take_snapshot = SChannel.take_channel_snapshot;
    CI.ci_recall_snapshot = SChannel.recall_channel_snapshot;
    CI.ci_send = send;
    CI.ci_receive = receive;
  }
