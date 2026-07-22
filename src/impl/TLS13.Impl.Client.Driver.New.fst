module TLS13.Impl.Client.Driver.New

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module EC = TLS13.Spec.Endpoint.Client
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Sem = TLS13.Wire.Semantics
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.State
fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          client_driver_live
            result
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_state_correct
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) /\
                CT.client_end_to_end_invariant
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))
{
  let initial : Ghost.erased EC.client_initial_state = Ghost.hide (
    CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  let auth =
    O.auth_context_new
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  let progress =
    MR.alloc #_ #(EC.client_progress_preorder #CTypes.client_local_event) (Ghost.reveal initial);
  MR.take_snapshot progress (Ghost.reveal initial);
  let c =
    C.new_client
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  rewrite
    (CR.connection_exactly
      c
      (Ghost.reveal initial))
    as
    (C.connection_exactly
      c
      (Ghost.reveal initial));
  let channel = Box.alloc no_channel;
  let buffered_len = Box.alloc 0sz;
  let empty_payload = V.alloc 0uy 0sz;
  let raw = V.alloc 0uy driver_rx_capacity;
  let network_out = V.alloc 0uy driver_network_out_capacity;
  let auth_leaf_der = V.alloc 0uy driver_auth_leaf_der_capacity;
  let auth_payload = V.alloc 0uy driver_public_key_payload_capacity;
  let auth_cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
  let auth_signature = V.alloc 0uy driver_signature_capacity;
  let app_out = V.alloc 0uy driver_app_out_capacity;
  let local_app_out = V.alloc 0uy driver_app_out_capacity;
  assert (pure (Bounds.max_handshake_flight_len <= SZ.v driver_auth_leaf_der_capacity));
  assert (pure (SZ.v driver_public_key_payload_capacity <= Bounds.max_public_key_len));
  assert (pure (Bounds.max_certificate_verify_input_len <= SZ.v driver_certificate_verify_input_capacity));
  assert (pure (L.max_signature_len <= SZ.v driver_signature_capacity));
  assert (pure (L.max_record_fragment_len <= SZ.v driver_app_out_capacity));
  let d = {
    client_driver_client = c;
    client_driver_progress = progress;
    client_driver_initial = initial;
    client_driver_auth = auth;
    client_driver_channel = channel;
    client_driver_buffered_len = buffered_len;
    client_driver_empty_payload = empty_payload;
    client_driver_raw = raw;
        client_driver_network_out = network_out;
        client_driver_auth_leaf_der = auth_leaf_der;
        client_driver_auth_payload = auth_payload;
        client_driver_auth_cv_input = auth_cv_input;
        client_driver_auth_signature = auth_signature;
        client_driver_app_out = app_out;
        client_driver_local_app_out = local_app_out;
      };
      rewrite
         (MR.pts_to progress #1.0R (Ghost.reveal initial))
         as
         (MR.pts_to d.client_driver_progress #1.0R (Ghost.reveal initial));
      rewrite
         (MR.snapshot progress (Ghost.reveal initial))
         as
         (MR.snapshot d.client_driver_progress (Ghost.reveal initial));
      assert (pure (Ghost.reveal d.client_driver_initial == Ghost.reveal initial));
      rewrite
         (MR.pts_to d.client_driver_progress #1.0R (Ghost.reveal initial))
         as
         (MR.pts_to
           d.client_driver_progress
           #1.0R
           (Ghost.reveal d.client_driver_initial));
      rewrite
         (MR.snapshot d.client_driver_progress (Ghost.reveal initial))
         as
         (MR.snapshot
           d.client_driver_progress
           (Ghost.reveal d.client_driver_initial));
      fold (client_driver_canonical_progress d (Ghost.reveal initial));
      rewrite (Box.pts_to channel no_channel) as
         (Box.pts_to d.client_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.client_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.client_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.client_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy));
      rewrite
        (V.pts_to auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy));
      rewrite
        (V.pts_to auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (V.pts_to local_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_local_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (C.connection_exactly
          c
          (Ghost.reveal initial))
        as
        (C.connection_exactly
          d.client_driver_client
          (Ghost.reveal initial));
      rewrite (O.is_auth_context auth) as (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d B.empty 0sz);
      assert (pure (client_driver_wire_logs_match
        (Ghost.reveal initial)
        B.empty
        B.empty
        B.empty
        0sz));
      assert (pure (Seq.equal B.empty (Ghost.reveal initial).CS.cs_wire_log.CL.raw_received));
      assert (pure (Seq.equal B.empty (Ghost.reveal initial).CS.cs_wire_log.CL.raw_sent));
      assert (pure (CP.client_invariant_pure
        (Ghost.reveal initial)
        B.empty
        B.empty
        (Ghost.reveal initial)));
      fold
        (client_driver_live
          d
          (Ghost.reveal initial));
      rewrite
        (client_driver_live d (Ghost.reveal initial))
        as
        (client_driver_live
          d
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds));
      d
}
