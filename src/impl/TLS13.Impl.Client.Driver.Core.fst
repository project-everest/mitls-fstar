module TLS13.Impl.Client.Driver.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module BT = Common.BufferedTCP
module BS = Common.BufferedStream
module C = TLS13.Impl.Client
module CChannel = TLS13.Impl.Client.ChannelImplementation
module CP = TLS13.Impl.Client.CanonicalProtocol
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Drain
module CTypes = TLS13.Impl.CanonicalTypes
module EC = TLS13.Spec.Endpoint.Client
module ID = FStar.IndefiniteDescription
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
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
module BN = TLS13.Impl.Client.Driver.BufferedNetwork
open TLS13.Impl.Client.Driver.State

noextract
let driver_connection_frame
  (d:driver)
  (st:CS.connection_state)
  (buffered:B.bytes)
  (pending_len:SZ.t)
  : slprop =
  exists* model received committed sent.
    buffered_driver_canonical_progress (driver_as_buffered d) st **
    BT.is_buffered d.driver_channel model received committed sent **
    MR.pts_to d.driver_tcp_history #1.0R (wire_history received sent) **
    pure (
      BT.same_storage d.driver_channel d.driver_storage /\
      BT.capacity model == SZ.v driver_rx_capacity /\
      client_driver_wire_logs_match_witness
        st received sent committed buffered pending_len /\
      Seq.equal buffered (BT.pending model) /\
      SZ.v pending_len == B.length (BT.pending model))

ghost
fn open_driver_connection
  (d:driver)
  requires driver_exactly d 'st 'buffered 'pending_len
  ensures
    C.connection_exactly d.driver_client 'st **
    driver_connection_frame d 'st 'buffered 'pending_len
{
  unfold (driver_exactly d 'st 'buffered 'pending_len);
  unfold (buffered_driver_exactly
    (driver_as_buffered d) 'st 'buffered 'pending_len);
  with model received committed sent.
    assert (buffered_driver_indexed
      (driver_as_buffered d)
      'st
      'buffered
      'pending_len
      model
      received
      committed
      sent);
  unfold (buffered_driver_indexed
    (driver_as_buffered d)
    'st
    'buffered
    'pending_len
    model
    received
    committed
    sent);
  fold (driver_connection_frame d 'st 'buffered 'pending_len);
}

ghost
fn close_driver_connection
  (d:driver)
  requires
    C.connection_exactly d.driver_client 'st **
    driver_connection_frame d 'st 'buffered 'pending_len
  ensures driver_exactly d 'st 'buffered 'pending_len
{
  unfold (driver_connection_frame d 'st 'buffered 'pending_len);
  with model received committed sent.
    assert (
      buffered_driver_canonical_progress (driver_as_buffered d) 'st **
      BT.is_buffered d.driver_channel model received committed sent **
      MR.pts_to d.driver_tcp_history #1.0R (wire_history received sent));
  fold (buffered_driver_indexed
    (driver_as_buffered d)
    'st
    'buffered
    'pending_len
    model
    received
    committed
    sent);
  fold (buffered_driver_exactly
    (driver_as_buffered d) 'st 'buffered 'pending_len);
  fold (driver_exactly d 'st 'buffered 'pending_len);
}

noextract
let client_buffer_read_decision
  (resp:CT.client_buffer_response)
  =
  if resp.CT.response.CT.status == CT.NeedMoreInput
  then (BS.NeedMore <: BS.classification unit unit)
  else (BS.Reject () <: BS.classification unit unit)

let lemma_client_buffered_network_io_step_correct_intro
  (st0 st1:CS.connection_state)
  (result:buffered_network_io_result)
  (input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        D.drained_network_bytes_end_to_end_correct
          st0
          st1
          result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures
        client_buffered_network_io_step_correct
          st1 result network_out app_out)
=
  FStar.Classical.exists_intro
    (fun old_app_out' ->
      D.drained_network_bytes_end_to_end_correct
        st0 st1
        result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        input old_network_out network_out old_app_out' app_out)
    old_app_out;
  FStar.Classical.exists_intro
    (fun old_network_out' ->
      exists old_app_out'.
        D.drained_network_bytes_end_to_end_correct
          st0 st1
          result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input old_network_out' network_out old_app_out' app_out)
    old_network_out;
  FStar.Classical.exists_intro
    (fun input' ->
      exists old_network_out' old_app_out'.
        D.drained_network_bytes_end_to_end_correct
          st0 st1
          result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input' old_network_out' network_out old_app_out' app_out)
    input;
  FStar.Classical.exists_intro
    (fun st_before ->
      exists input' old_network_out' old_app_out'.
        D.drained_network_bytes_end_to_end_correct
          st_before st1
          result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input' old_network_out' network_out old_app_out' app_out)
    st0

fn driver_control_snapshot
  (d:driver)
  requires driver_exactly d 'st0 'buffered 'pending_len
  returns snapshot:CR.control_snapshot
  ensures driver_exactly d 'st0 'buffered 'pending_len **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot = C.control_snapshot d.driver_client;
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  snapshot
}

(** Is the pending protected-handshake buffer drained?  See
    [TLS13.Impl.Client.protected_handshake_buffer_empty]. *)
fn driver_protected_handshake_buffer_empty
  (d:driver)
  requires driver_exactly d 'st0 'buffered 'pending_len
  returns empty:bool
  ensures driver_exactly d 'st0 'buffered 'pending_len **
          pure (empty ==>
            CS.protected_handshake_buffer_empty 'st0.CS.cs_model)
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let empty = C.protected_handshake_buffer_empty d.driver_client;
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  empty
}

fn driver_copy_certificate_leaf_der
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                 | Some leaf ->
                   SZ.v copied_len == B.length leaf /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                 | None -> False))
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_leaf_der
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  copied_len
}

(** Copy the peer's certificate chain out of the connection so the external
    validator can use the intermediates for chain building.  The chain layout
    (entry [i] at [chain_out[offsets[i] .. offsets[i] + lens[i])], entry 0 the
    leaf) is the one [C.copy_certificate_chain] establishes.

    Nothing downstream depends on the returned snapshot's relation to the
    connection state -- the chain is only a hint to the validator -- so this
    wrapper deliberately keeps a weak postcondition. *)
fn driver_copy_certificate_chain
  (d:driver)
  (chain_out:array U8.t)
  (chain_out_len:SZ.t)
  (offsets_out:array SZ.t)
  (offsets_out_len:SZ.t)
  (lens_out:array SZ.t)
  (lens_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to chain_out 'old_chain_out **
           pts_to offsets_out 'old_offsets_out **
           pts_to lens_out 'old_lens_out **
           pure (B.length 'old_chain_out == SZ.v chain_out_len /\
                 Seq.length 'old_offsets_out == SZ.v offsets_out_len /\
                 Seq.length 'old_lens_out == SZ.v lens_out_len /\
                 SZ.v chain_out_len == L.max_certificate_chain_bytes /\
                 SZ.v offsets_out_len == L.max_certificate_chain_entries /\
                 SZ.v lens_out_len == L.max_certificate_chain_entries /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate)
  returns snapshot:CR.certificate_chain_snapshot
  ensures exists* chain_bytes offsets lens.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to chain_out chain_bytes **
          pts_to offsets_out offsets **
          pts_to lens_out lens **
          pure (B.length chain_bytes == SZ.v chain_out_len /\
                Seq.length offsets == SZ.v offsets_out_len /\
                Seq.length lens == SZ.v lens_out_len /\
                SZ.v snapshot.CR.certificate_chain_bytes_len <=
                  B.length chain_bytes /\
                SZ.v snapshot.CR.certificate_chain_cert_count <=
                  Seq.length offsets)
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot =
    C.copy_certificate_chain
      d.driver_client
      chain_out
      chain_out_len
      offsets_out
      offsets_out_len
      lens_out
      lens_out_len;
  with chain_bytes offsets lens.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to chain_out chain_bytes **
            pts_to offsets_out offsets **
            pts_to lens_out lens);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  snapshot
}

fn driver_copy_certificate_verify_input
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                 | Some input ->
                   SZ.v copied_len == B.length input /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                 | None -> False))
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_verify_input
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  copied_len
}

fn driver_copy_certificate_verify_signature
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                 | Some cv ->
                   L.signature_scheme_matches snapshot.CR.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                   SZ.v snapshot.CR.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                     (Sem.certificateVerify_signature_bytes cv)
                 | None -> False))
{
  open_driver_connection d;
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot =
    C.copy_certificate_verify_signature
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  close_driver_connection d;
  snapshot
}

fn process_ready_internal_local_action_once
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
          pts_to empty_payload 'empty_payload_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'empty_payload_bytes == 0 /\
                B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  unfold (top_driver_exactly
    d
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  unfold (driver_exactly
    d.top_driver_core
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  unfold (buffered_driver_exactly
    (driver_as_buffered d.top_driver_core)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  with model received committed sent.
    assert (buffered_driver_indexed
      (driver_as_buffered d.top_driver_core)
      'st0
      (Ghost.reveal 'buffered)
      (Ghost.reveal 'pending_len)
      model
      received
      committed
      sent);
  unfold (buffered_driver_indexed
    (driver_as_buffered d.top_driver_core)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)
    model
    received
    committed
    sent);
  rewrite
    (C.connection_exactly d.top_driver_core.driver_client 'st0)
    as
    (CR.connection_exactly d.top_driver_core.driver_client 'st0);
  let action =
    C.next_local_action
      d.top_driver_core.driver_client
      network_out_len
      certificate_public_key_len
      server_finished_payload_len;
  rewrite
    (CR.connection_exactly d.top_driver_core.driver_client 'st0)
    as
    (C.connection_exactly d.top_driver_core.driver_client 'st0);
  fold (buffered_driver_indexed
    (driver_as_buffered d.top_driver_core)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)
    model
    received
    committed
    sent);
  fold (buffered_driver_exactly
    (driver_as_buffered d.top_driver_core)
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  fold (driver_exactly
    d.top_driver_core
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  fold (top_driver_exactly
    d
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len));
  assert (pure (C.next_local_action_sound
    'st0
    network_out_len
    certificate_public_key_len
    server_finished_payload_len
    action));
  assert (pure (forall (i:nat{i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i == Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let ready = action.CT.next_local_ready;
  if ready {
    assert (pure (action.CT.next_local_ready == true));
    let needs_external_payload =
      action.CT.next_local_kind = CT.LocalValidateCertificate ||
      action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
    if needs_external_payload {
      assert (pure ('st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure ('st0 == 'st0));
      {
        ready_local_action = action;
        ready_local_processed = false;
        ready_local_resp = no_op_resp;
        ready_local_written = 0sz;
      }
    } else {
      assert (pure (C.next_local_action_internal_input_ready 'st0 action));
      assert (pure (internal_local_action_kind action.CT.next_local_kind));
      lemma_ready_internal_action_empty_payload_wf
        'st0
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        action
        (Ghost.reveal 'empty_payload_bytes);
      assert (pure (CT.local_input_wf
        'st0
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)));
      rewrite
        (top_driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len))
        as
        (top_buffered_driver_exactly
          (top_driver_as_buffered d)
          'st0
          (Ghost.reveal 'buffered)
          (Ghost.reveal 'pending_len));
      let write_result =
        BN.process_local_event
          (top_driver_as_buffered d)
          action.CT.next_local_kind
          empty_payload
          0sz
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 network_out_bytes app_out_bytes.
        assert (top_buffered_driver_exactly
                  (top_driver_as_buffered d)
                  st1
                  (Ghost.reveal 'buffered)
                  (Ghost.reveal 'pending_len) **
                pts_to empty_payload 'empty_payload_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      rewrite
        (top_buffered_driver_exactly
          (top_driver_as_buffered d)
          st1
          (Ghost.reveal 'buffered)
          (Ghost.reveal 'pending_len))
        as
        (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
      assert (pure (CT.local_event_end_to_end_correct
        'st0
        st1
        write_result.local_write_resp
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)
        network_out_bytes
        app_out_bytes));
      CT.lemma_local_event_end_to_end_correct_preserves_config
        'st0
        st1
        write_result.local_write_resp
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)
        network_out_bytes
        app_out_bytes;
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (write_result.local_write_resp.CT.status == CT.StepOk ==>
        SZ.v write_result.local_write_written <=
        SZ.v write_result.local_write_resp.CT.network_out_len));
      {
        ready_local_action = action;
        ready_local_processed = true;
        ready_local_resp = write_result.local_write_resp;
        ready_local_written = write_result.local_write_written;
      }
    }
  } else {
    assert (pure ('st0.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ('st0 == 'st0));
    {
      ready_local_action = action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    }
  }
}

let lemma_ready_local_action_progress
  (st0 st1:CS.connection_state)
  (result:ready_local_action_result)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        (result.ready_local_processed ==>
          CT.local_event_end_to_end_correct
            st0
            st1
            result.ready_local_resp
            result.ready_local_action.CT.next_local_kind
            payload
            network_out
            app_out) /\
        (result.ready_local_processed == false ==> st1 == st0))
      (ensures
        EC.client_progress_preorder #CTypes.client_local_event st0 st1)
=
  if result.ready_local_processed then
    CP.lemma_client_local_progress
      st0
      st1
      {
        CTypes.client_local_kind = result.ready_local_action.CT.next_local_kind;
        CTypes.client_local_payload = payload;
      }
      result.ready_local_resp
      network_out
      app_out
  else
    assert (EC.client_progress_preorder #CTypes.client_local_event st0 st1)

fn driver_handshake_step
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  let result =
    process_ready_internal_local_action_once
      d
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  lemma_ready_local_action_result_preserves_config
    'st0
    st1
    result
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  result
}

fn rec driver_drain_local_actions
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: driver_drain_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 (result.driver_drain_last.ready_local_processed \/
                  result.driver_drain_last.ready_local_written == 0sz) /\
                 (result.driver_drain_exhausted ==>
                  result.driver_drain_last.ready_local_processed == false /\
                  result.driver_drain_last.ready_local_written == 0sz))
  decreases (SZ.v fuel)
{
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_last = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    assert (pure (false == false /\ 0sz == 0sz));
    {
      driver_drain_last = no_op_last;
      driver_drain_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step =
      driver_handshake_step
        d
        empty_payload
        network_out
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        app_out
        app_out_len;
    with st1 network_out_bytes app_out_bytes.
      assert (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
              pts_to empty_payload 'empty_payload_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (B.length app_out_bytes == SZ.v app_out_len));
    assert (pure (step.ready_local_processed \/
      step.ready_local_written == 0sz));
    let proceed =
      step.ready_local_processed &&
      step.ready_local_resp.CT.status = CT.StepOk;
    if proceed {
      let next_fuel = SZ.sub fuel 1sz;
      assert (pure (SZ.v next_fuel < SZ.v fuel));
      let result =
        driver_drain_local_actions
          d
          empty_payload
          network_out
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          app_out
          app_out_len
          next_fuel;
      result
    } else {
      {
        driver_drain_last = step;
        driver_drain_exhausted = false;
      }
    }
  }
}

fn driver_progress_buffered_network_step
  (d:top_driver)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (
             B.length 'old_network_out == SZ.v network_out_len /\
             B.length 'old_app_out == SZ.v app_out_len /\
             L.max_record_fragment_len <= SZ.v app_out_len)
  returns result:BN.completed_drive
  ensures exists* st1 buffered_after network_out_bytes app_out_bytes.
           top_driver_exactly
             d
             st1
             buffered_after
             result.BN.completed_drive_pending_len **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (
             B.length buffered_after ==
               SZ.v result.BN.completed_drive_pending_len /\
             B.length network_out_bytes == SZ.v network_out_len /\
             B.length app_out_bytes == SZ.v app_out_len /\
             st1.CS.cs_model.CS.model_config ==
               'st0.CS.cs_model.CS.model_config /\
             (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st1) /\
             BN.completed_drive_correct
               'st0
               st1
               'old_network_out
               network_out_bytes
               'old_app_out
               app_out_bytes
               result)
{
  rewrite
    (top_driver_exactly d 'st0 'buffered buffered_len)
    as
    (top_buffered_driver_exactly
      (top_driver_as_buffered d)
      'st0
      'buffered
      buffered_len);
  let result =
    BN.drive
      (top_driver_as_buffered d)
      network_out
      network_out_len
      app_out
      app_out_len
      buffered_len
      fuel;
  with st1 buffered_after network_out_bytes app_out_bytes.
    assert (
      top_buffered_driver_exactly
        (top_driver_as_buffered d)
        st1
        buffered_after
        result.BN.completed_drive_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  rewrite
    (top_buffered_driver_exactly
      (top_driver_as_buffered d)
      st1
      buffered_after
      result.BN.completed_drive_pending_len)
    as
    (top_driver_exactly
      d
      st1
      buffered_after
      result.BN.completed_drive_pending_len);
  result
}

fn top_driver_process_one_local_action
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (certificate_public_key_len:SZ.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 (result.ready_local_processed ==>
                  (CT.client_end_to_end_invariant 'st0 ==>
                   CT.client_end_to_end_invariant st1)) /\
                 (result.ready_local_processed == false ==> st1 == 'st0) /\
                 TChannel.application_log st1 ==
                   TChannel.application_log 'st0)
{
  let step =
    driver_handshake_step
      d
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  unfold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (step.ready_local_processed ==>
    (CT.client_end_to_end_invariant 'st0 ==>
     CT.client_end_to_end_invariant st1)));
  assert (pure (step.ready_local_processed == false ==> st1 == 'st0));
  assert (pure (step.ready_local_processed ==>
    step.ready_local_action.CT.next_local_kind <>
      CT.LocalDeliverApplicationData /\
    step.ready_local_action.CT.next_local_kind <>
      CT.LocalSendApplicationData));
  CChannel.lemma_optional_receive_local_application_log
    'st0
    st1
    step.ready_local_processed
    step.ready_local_resp
    step.ready_local_action.CT.next_local_kind
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (
    TChannel.application_log st1 == TChannel.application_log 'st0));
  if step.ready_local_processed {
    fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
    step
  } else {
    assert (pure (step.ready_local_written == 0sz));
    assert (pure (st1 == 'st0));
    let ready = step.ready_local_action.CT.next_local_ready;
    if ready {
      let validate =
        step.ready_local_action.CT.next_local_kind = CT.LocalValidateCertificate;
      if validate {
        assert (pure (C.next_local_action_sound
          'st0
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          step.ready_local_action));
        assert (pure (Some?
          'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        assert (pure (Some?
          st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        assert (pure (Some?
          st1.CS.cs_model.CS.model_handshake.CS.hs_certificate));
        // Hand the validator the whole chain the peer sent.  Public CAs sign
        // end-entity certificates with intermediates, so without these the
        // leaf has no path to any configured anchor and every real server is
        // rejected.  The buffers are scratch for one call; the validator
        // copies what it keeps.
        let chain_scratch = V.alloc 0uy L.max_certificate_chain_bytes_sz;
        let offsets_scratch = V.alloc 0sz L.max_certificate_chain_entries_sz;
        let lens_scratch = V.alloc 0sz L.max_certificate_chain_entries_sz;
        V.to_array_pts_to chain_scratch;
        V.to_array_pts_to offsets_scratch;
        V.to_array_pts_to lens_scratch;
        let chain_snapshot =
          driver_copy_certificate_chain
            d.top_driver_core
            (V.vec_to_array chain_scratch)
            L.max_certificate_chain_bytes_sz
            (V.vec_to_array offsets_scratch)
            L.max_certificate_chain_entries_sz
            (V.vec_to_array lens_scratch)
            L.max_certificate_chain_entries_sz;
        O.set_peer_certificate_chain
          d.top_driver_auth
          (V.vec_to_array chain_scratch)
          L.max_certificate_chain_bytes_sz
          chain_snapshot.CR.certificate_chain_bytes_len
          (V.vec_to_array offsets_scratch)
          (V.vec_to_array lens_scratch)
          L.max_certificate_chain_entries_sz
          chain_snapshot.CR.certificate_chain_cert_count;
        V.to_vec_pts_to chain_scratch;
        V.to_vec_pts_to offsets_scratch;
        V.to_vec_pts_to lens_scratch;
        V.free chain_scratch;
        V.free offsets_scratch;
        V.free lens_scratch;
        let leaf_len =
          driver_copy_certificate_leaf_der
            d.top_driver_core
            auth_leaf_der
            auth_leaf_der_len;
        with auth_leaf_der_bytes.
          assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                  pts_to auth_leaf_der auth_leaf_der_bytes);
        let leaf_fits = SZ.lte leaf_len certificate_public_key_len;
        if leaf_fits {
          assert (pure (SZ.v leaf_len <= SZ.v certificate_public_key_len));
          A.pts_to_len auth_payload;
          assert (pure (A.length auth_payload == SZ.v certificate_public_key_len));
          A.to_mask auth_payload;
          with auth_payload_mask.
            assert (A.pts_to_mask auth_payload #1.0R auth_payload_mask (fun _ -> True));
          assert (pure (Seq.length auth_payload_mask == SZ.v certificate_public_key_len));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_mask ==>
            Some? (Seq.index auth_payload_mask i)));
          let auth_payload_prefix =
            A.sub auth_payload #1.0R #(fun _ -> True) 0sz (SZ.v leaf_len);
          with auth_payload_prefix_mask.
            assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask (fun _ -> True));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask ==>
            Some? (Seq.index auth_payload_prefix_mask i)));
          A.from_mask auth_payload_prefix;
          with auth_payload_prefix_bytes_before.
            assert (pts_to auth_payload_prefix auth_payload_prefix_bytes_before);
          assert (pure (B.length auth_payload_prefix_bytes_before == SZ.v leaf_len));
          let ok =
            O.validate_certificate_for_local_event
              d.top_driver_auth
              #(st1)
              auth_leaf_der
              auth_leaf_der_len
              leaf_len
              auth_payload_prefix
              leaf_len;
          with auth_payload_prefix_bytes.
            assert (O.is_auth_context d.top_driver_auth **
                    pts_to auth_payload_prefix auth_payload_prefix_bytes);
          assert (pure (B.length auth_payload_prefix_bytes == SZ.v leaf_len));
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes));
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            rewrite
              (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len))
              as
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st1
                (Ghost.reveal 'buffered)
                (Ghost.reveal 'pending_len));
            let write_result =
              BN.process_local_event
                (top_driver_as_buffered d)
                CT.LocalValidateCertificate
                auth_payload_prefix
                leaf_len
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (top_buffered_driver_exactly
                        (top_driver_as_buffered d)
                        st2
                        (Ghost.reveal 'buffered)
                        (Ghost.reveal 'pending_len) **
                      pts_to auth_payload_prefix auth_payload_prefix_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            rewrite
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st2
                (Ghost.reveal 'buffered)
                (Ghost.reveal 'pending_len))
              as
              (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            unfold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            CChannel.lemma_receive_local_application_log
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2;
            assert (pure (
              TChannel.application_log st2 ==
                TChannel.application_log 'st0));
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      } else {
        let verify =
          step.ready_local_action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
        if verify {
          assert (pure (C.next_local_action_sound
            'st0
            network_out_len
            certificate_public_key_len
            server_finished_payload_len
            step.ready_local_action));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          let input_len =
            driver_copy_certificate_verify_input
              d.top_driver_core
              auth_cv_input
              auth_cv_input_len;
          with auth_cv_input_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_cv_input auth_cv_input_bytes);
          let signature_snapshot =
            driver_copy_certificate_verify_signature
              d.top_driver_core
              auth_signature
              auth_signature_len;
          with auth_signature_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_signature auth_signature_bytes);
          let ok =
            O.verify_certificate_signature_for_local_event
              d.top_driver_auth
              #(st1)
              auth_cv_input
              auth_cv_input_len
              input_len
              signature_snapshot.CR.cv_signature_scheme
              auth_signature
              auth_signature_len
              signature_snapshot.CR.cv_signature_len;
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalVerifyCertificateSignature
              B.empty));
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            rewrite
              (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len))
              as
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st1
                (Ghost.reveal 'buffered)
                (Ghost.reveal 'pending_len));
            let write_result =
              BN.process_local_event
                (top_driver_as_buffered d)
                CT.LocalVerifyCertificateSignature
                empty_payload
                0sz
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (top_buffered_driver_exactly
                        (top_driver_as_buffered d)
                        st2
                        (Ghost.reveal 'buffered)
                        (Ghost.reveal 'pending_len) **
                      pts_to empty_payload 'empty_payload_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            rewrite
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st2
                (Ghost.reveal 'buffered)
                (Ghost.reveal 'pending_len))
              as
              (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            unfold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            CChannel.lemma_receive_local_application_log
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2;
            assert (pure (
              TChannel.application_log st2 ==
                TChannel.application_log 'st0));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      }
    } else {
      fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
      step
    }
  }
}

fn rec driver_handshake
  (d:top_driver)
  (empty_payload:array U8.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'buffered == SZ.v buffered_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1) /\
                 (result.driver_workflow_status == DriverWorkflowOk ==>
                  st1.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                  CS.protected_handshake_buffer_empty st1.CS.cs_model))
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let snapshot = driver_control_snapshot d.top_driver_core;
    with st_snapshot.
      assert (driver_exactly d.top_driver_core st_snapshot 'buffered buffered_len);
    assert (pure (st_snapshot.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    // Reaching ControlApplicationData is not on its own the end of the
    // handshake: a coalesced record can leave protected-handshake plaintext
    // still buffered, and that plaintext is internal work the driver owes.
    // Report Ok only once it is drained, so that `client_driver_application_ready`
    // really does mean "nothing left to do".
    let buffer_drained = driver_protected_handshake_buffer_empty d.top_driver_core;
    fold (top_driver_exactly d st_snapshot 'buffered buffered_len);
    let app_ready = snapshot.CR.snapshot_control_tag = 2uy && buffer_drained;
    if app_ready {
      assert (pure (CR.control_snapshot_matches snapshot st_snapshot));
      assert (pure (st_snapshot.CS.cs_model.CS.model_control == CS.ControlApplicationData));
      assert (pure (CS.protected_handshake_buffer_empty st_snapshot.CS.cs_model));
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len = buffered_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = no_op_io;
      }
    } else {
      let failed = snapshot.CR.snapshot_control_tag = 5uy;
      if failed {
        {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len = buffered_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = no_op_io;
        }
      } else {
        let local =
          top_driver_process_one_local_action
            d
            empty_payload
            network_out
            network_out_len
            auth_leaf_der
            auth_leaf_der_len
            auth_payload
            certificate_public_key_len
            auth_cv_input
            auth_cv_input_len
            auth_signature
            auth_signature_len
            server_finished_payload_len
            app_out
            app_out_len;
        with st_local network_out_local auth_leaf_der_local auth_payload_local auth_cv_input_local auth_signature_local app_out_local.
          assert (top_driver_exactly d st_local 'buffered buffered_len **
                  pts_to network_out network_out_local **
                  pts_to auth_leaf_der auth_leaf_der_local **
                  pts_to auth_payload auth_payload_local **
                  pts_to auth_cv_input auth_cv_input_local **
                  pts_to auth_signature auth_signature_local **
                  pts_to app_out app_out_local);
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          st_snapshot.CS.cs_model.CS.model_config));
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        if local.ready_local_processed {
          assert (pure (local.ready_local_processed == true));
          assert (pure (local.ready_local_processed == true ==>
            (CT.client_end_to_end_invariant 'st0 ==>
             CT.client_end_to_end_invariant st_local)));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        } else {
          assert (pure (st_local == 'st0));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        };
        if local.ready_local_processed {
          let ok = local.ready_local_resp.CT.status = CT.StepOk;
          let wrote_all =
            local.ready_local_written = local.ready_local_resp.CT.network_out_len;
          if (ok && wrote_all) {
            // A local event can unblock handshake messages still sitting in the
            // pending protected-handshake buffer: `CertificateVerify` only
            // becomes legal once `LocalValidateCertificate` has run.  Servers
            // routinely coalesce their whole encrypted flight into one record,
            // so those messages have already arrived and no further socket read
            // will ever produce them.  Drain here, between local events, rather
            // than only when a record arrives.
            rewrite
              (top_driver_exactly d st_local (Ghost.reveal 'buffered) buffered_len)
              as
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st_local
                (Ghost.reveal 'buffered)
                buffered_len);
            BN.drain_pending_internal (top_driver_as_buffered d);
            with st_drained. assert (
              top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st_drained
                (Ghost.reveal 'buffered)
                buffered_len);
            rewrite
              (top_buffered_driver_exactly
                (top_driver_as_buffered d)
                st_drained
                (Ghost.reveal 'buffered)
                buffered_len)
              as
              (top_driver_exactly d st_drained (Ghost.reveal 'buffered) buffered_len);
            D.lemma_drained_facts st_local st_drained;
            assert (pure (st_drained.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st_drained));
            let next_fuel = SZ.sub fuel 1sz;
            assert (pure (SZ.v next_fuel < SZ.v fuel));
            driver_handshake
              d
              empty_payload
              buffered_len
              network_out
              network_out_len
              auth_leaf_der
              auth_leaf_der_len
              auth_payload
              auth_cv_input
              auth_cv_input_len
              auth_signature
              auth_signature_len
              certificate_public_key_len
              server_finished_payload_len
              app_out
              app_out_len
              local_fuel
              next_fuel
          } else {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          }
        } else {
          let still_ready = local.ready_local_action.CT.next_local_ready;
          if still_ready {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          } else {
            let network =
              driver_progress_buffered_network_step
                d
                buffered_len
                network_out
                network_out_len
                app_out
                app_out_len
                fuel;
            with st_network buffered_network network_out_network app_out_network.
              assert (
                top_driver_exactly
                  d
                  st_network
                  buffered_network
                  network.BN.completed_drive_pending_len **
                pts_to network_out network_out_network **
                pts_to app_out app_out_network);
            match network.BN.completed_drive_outcome {
              BS.DriveYield network_result consumed output fuel_left -> {
                let next_fuel = SZ.sub fuel 1sz;
                assert (pure (SZ.v next_fuel < SZ.v fuel));
                driver_handshake
                  d
                  empty_payload
                  network.BN.completed_drive_pending_len
                  network_out
                  network_out_len
                  auth_leaf_der
                  auth_leaf_der_len
                  auth_payload
                  auth_cv_input
                  auth_cv_input_len
                  auth_signature
                  auth_signature_len
                  certificate_public_key_len
                  server_finished_payload_len
                  app_out
                  app_out_len
                  local_fuel
                  next_fuel
              }
              BS.DriveProgress network_result consumed fuel_left -> {
                let next_fuel = SZ.sub fuel 1sz;
                assert (pure (SZ.v next_fuel < SZ.v fuel));
                driver_handshake
                  d
                  empty_payload
                  network.BN.completed_drive_pending_len
                  network_out
                  network_out_len
                  auth_leaf_der
                  auth_leaf_der_len
                  auth_payload
                  auth_cv_input
                  auth_cv_input_len
                  auth_signature
                  auth_signature_len
                  certificate_public_key_len
                  server_finished_payload_len
                  app_out
                  app_out_len
                  local_fuel
                  next_fuel
              }
              BS.DriveReject network_result status fuel_left -> {
                {
                  driver_workflow_status = DriverWorkflowStepFailed;
                  driver_workflow_rx_len =
                    network.BN.completed_drive_pending_len;
                  driver_workflow_local = {
                    driver_drain_last = local;
                    driver_drain_exhausted = false;
                  };
                  driver_workflow_network = {
                    buffered_network_io_read_len = 0sz;
                    buffered_network_io_buffered = network_result;
                  };
                }
              }
              BS.DriveBufferFull network_result fuel_left -> {
                {
                  driver_workflow_status = DriverWorkflowStepFailed;
                  driver_workflow_rx_len =
                    network.BN.completed_drive_pending_len;
                  driver_workflow_local = {
                    driver_drain_last = local;
                    driver_drain_exhausted = false;
                  };
                  driver_workflow_network = {
                    buffered_network_io_read_len = 0sz;
                    buffered_network_io_buffered = network_result;
                  };
                }
              }
              BS.DriveExhausted -> {
                {
                  driver_workflow_status = DriverWorkflowExhausted;
                  driver_workflow_rx_len =
                    network.BN.completed_drive_pending_len;
                  driver_workflow_local = {
                    driver_drain_last = local;
                    driver_drain_exhausted = false;
                  };
                  driver_workflow_network = {
                    buffered_network_io_read_len = 0sz;
                    buffered_network_io_buffered = {
                      buffered_network_read = no_op_read;
                      buffered_network_new_len =
                        network.BN.completed_drive_pending_len;
                    };
                  };
                }
              }
            }
          }
        }
      }
    }
  }
}
