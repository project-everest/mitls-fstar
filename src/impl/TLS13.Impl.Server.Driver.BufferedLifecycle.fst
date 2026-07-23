module TLS13.Impl.Server.Driver.BufferedLifecycle

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CI = Common.ChannelImplementation
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CTypes = TLS13.Impl.CanonicalTypes
module Crypto = TLS13.Crypto
module DS = TLS13.Impl.Server.Driver.State
module ES = TLS13.Spec.Endpoint.Server
module IM = TLS13.Impl.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

inline_for_extraction
fn free_top_server_driver_buffers
  (d:DS.top_server_driver)
  requires DS.top_server_driver_buffers d
  ensures emp
{
  unfold (DS.top_server_driver_buffers d);
  with empty_payload network_out material cv_input signature app_out local_app_out. _;
  V.free d.top_server_driver_empty_payload;
  V.free d.top_server_driver_network_out;
  V.free d.top_server_driver_material_payload;
  V.free d.top_server_driver_certificate_verify_input;
  V.free d.top_server_driver_signature;
  V.free d.top_server_driver_app_out;
  V.free d.top_server_driver_local_app_out
}

fn new_server_with_credentials
  (credentials:O.server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (#supported_profile_provider:erased SP.server_supported_profile_provider)
  requires
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity) **
    pts_to certificate_chain 'certificate_chain_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'certificate_chain_bytes <=
        Bounds.max_server_certificate_chain_len)
  returns result:option DS.top_server_driver
  ensures
    pts_to certificate_chain 'certificate_chain_bytes **
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity **
      (match result with
       | Some d ->
         DS.top_server_driver_live
           d
           (CR.server_initial_state
             (Ghost.reveal 'certificate_chain_bytes)
             credential_identity)
           (Ghost.reveal 'certificate_chain_bytes)
           credential_identity **
         pure (
           ST.server_state_correct
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity) /\
           ST.server_end_to_end_invariant
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity))
       | None -> emp))
{
  with credential_identity.
    assert (O.is_server_credentials
      credentials
      (Ghost.reveal 'certificate_chain_bytes)
      credential_identity);
  let material = V.alloc 0uy DS.driver_material_capacity;
  V.to_array_pts_to material;
  let material_ok =
    Crypto.random_bytes
      (V.vec_to_array material)
      DS.driver_material_capacity;
  with material_seed.
    assert (pts_to (V.vec_to_array material) material_seed);
  V.to_vec_pts_to material;
  if not material_ok {
    V.free material;
    None
  } else {
    let cloned_credentials = O.server_credentials_clone credentials;
    let erased_identity : erased CS.server_credential_identity =
      Ghost.hide credential_identity;
    let server =
      S.new_server_erased_credential_identity
        certificate_chain
        certificate_chain_len
        #erased_identity;
    rewrite
      (S.connection_exactly
        server
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          (Ghost.reveal erased_identity)))
      as
      (S.connection_exactly
        server
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    let progress =
      MR.alloc
        #_
        #(ES.server_progress_preorder #CTypes.server_local_event)
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
    let storage = BT.alloc_storage DS.driver_rx_capacity;
    with storage_model.
      assert (BT.is_storage storage storage_model);
    let channel = Box.alloc DS.no_buffered_channel;
    let empty_payload = V.alloc 0uy 0sz;
    let network_out = V.alloc 0uy DS.driver_network_out_capacity;
    let cv_input = V.alloc 0uy DS.driver_certificate_verify_input_capacity;
    let signature = V.alloc 0uy DS.driver_signature_capacity;
    let app_out = V.alloc 0uy DS.driver_app_out_capacity;
    let local_app_out = V.alloc 0uy DS.driver_app_out_capacity;
    let d = {
      DS.top_server_driver_server = server;
      DS.top_server_driver_credentials = cloned_credentials;
      DS.top_server_driver_channel = channel;
      DS.top_server_driver_storage = storage;
      DS.top_server_driver_empty_payload = empty_payload;
      DS.top_server_driver_network_out = network_out;
      DS.top_server_driver_material_payload = material;
      DS.top_server_driver_certificate_verify_input = cv_input;
      DS.top_server_driver_signature = signature;
      DS.top_server_driver_app_out = app_out;
      DS.top_server_driver_local_app_out = local_app_out;
      DS.top_server_driver_progress = progress;
      DS.top_server_driver_tcp_history = tcp_history;
      DS.top_server_driver_initial =
        Ghost.hide
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity);
      DS.top_server_driver_supported_profile =
        Ghost.hide
          ((Ghost.reveal supported_profile_provider)
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity));
    };
    rewrite
      (S.connection_exactly
        server
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (S.connection_exactly
        d.top_server_driver_server
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    rewrite
      (O.is_server_credentials
        cloned_credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      as
      (O.is_server_credentials
        d.top_server_driver_credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    rewrite
      (Box.pts_to channel DS.no_buffered_channel)
      as
      (Box.pts_to
        d.top_server_driver_channel
        DS.no_buffered_channel);
    rewrite
      (BT.is_storage storage storage_model)
      as
      (BT.is_storage d.top_server_driver_storage storage_model);
    rewrite
      (MR.pts_to tcp_history #1.0R
        (DS.server_driver_history B.empty B.empty))
      as
      (MR.pts_to d.top_server_driver_tcp_history #1.0R
        (DS.server_driver_history B.empty B.empty));
    rewrite
      (MR.pts_to progress #1.0R
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (MR.pts_to d.top_server_driver_progress #1.0R
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
    rewrite
      (MR.snapshot progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity))
      as
      (MR.snapshot d.top_server_driver_progress
        (Ghost.reveal d.top_server_driver_initial));
    rewrite
      (V.pts_to empty_payload #1.0R (Seq.create 0 0uy))
      as
      (V.pts_to d.top_server_driver_empty_payload #1.0R
        (Seq.create 0 0uy));
    rewrite
      (V.pts_to network_out #1.0R
        (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy))
      as
      (V.pts_to d.top_server_driver_network_out #1.0R
        (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy));
    rewrite
      (V.pts_to material #1.0R material_seed)
      as
      (V.pts_to d.top_server_driver_material_payload #1.0R material_seed);
    rewrite
      (V.pts_to cv_input #1.0R
        (Seq.create
          (SZ.v DS.driver_certificate_verify_input_capacity)
          0uy))
      as
      (V.pts_to d.top_server_driver_certificate_verify_input #1.0R
        (Seq.create
          (SZ.v DS.driver_certificate_verify_input_capacity)
          0uy));
    rewrite
      (V.pts_to signature #1.0R
        (Seq.create (SZ.v DS.driver_signature_capacity) 0uy))
      as
      (V.pts_to d.top_server_driver_signature #1.0R
        (Seq.create (SZ.v DS.driver_signature_capacity) 0uy));
    rewrite
      (V.pts_to app_out #1.0R
        (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
      as
      (V.pts_to d.top_server_driver_app_out #1.0R
        (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
    rewrite
      (V.pts_to local_app_out #1.0R
        (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
      as
      (V.pts_to d.top_server_driver_local_app_out #1.0R
        (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
    fold (DS.top_server_driver_buffers d);
    fold (DS.top_server_driver_canonical_progress
      d
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity));
    DS.lemma_initial_wire_logs_match
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
    assert (pure (DS.server_driver_wire_logs_match_witness
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      B.empty
      B.empty
      B.empty
      B.empty
      0sz));
    fold (DS.top_server_driver_live
      d
      (CR.server_initial_state
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity)
      (Ghost.reveal 'certificate_chain_bytes)
      credential_identity);
    Some d
  }
}

fn free
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_closed
      d 'st 'certificate_chain 'credential_identity
  ensures DS.top_server_driver_released d 'st
{
  unfold (DS.top_server_driver_closed
    d 'st 'certificate_chain 'credential_identity);
  with storage_model.
    assert (BT.is_storage d.top_server_driver_storage storage_model);
  with history.
    assert (MR.pts_to d.top_server_driver_tcp_history #1.0R history);
  BT.free_storage d.top_server_driver_storage;
  O.server_credentials_free d.top_server_driver_credentials;
  Box.free d.top_server_driver_channel;
  free_top_server_driver_buffers d;
  rewrite
    (S.connection_exactly d.top_server_driver_server 'st)
    as
    (CR.connection_exactly d.top_server_driver_server 'st);
  CR.free_connection d.top_server_driver_server;
  fold (DS.top_server_driver_released d 'st)
}
