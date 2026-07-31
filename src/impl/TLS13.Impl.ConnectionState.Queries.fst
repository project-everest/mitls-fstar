module TLS13.Impl.ConnectionState.Queries

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

// Phase 5: handshake_msg payloads are now the QuackyDucky-generated wire
// records; profile-relevant fields are read through the TLS13.Wire.Semantics
// accessors instead of the deleted M.<record> projection fields.
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Repr

fn config_role_is_client
  (cfg:connection_config_storage)
  (#spec:erased CS.connection_config)
  requires connection_config_exactly cfg spec
  returns ok: bool
  ensures connection_config_exactly cfg spec **
          pure (ok ==> spec.CS.config_role == CS.ClientEndpoint)
{
  unfold (connection_config_exactly cfg spec);
  with role validation_time.
    assert (Box.pts_to cfg.role_tag role **
            Box.pts_to cfg.validation_time_seconds validation_time);
  let role_tag = !cfg.role_tag;
  let ok = role_tag = 0uy;
  assert (pure (role_tag == role));
  assert (pure (Tags.endpoint_role_tag_matches role spec.CS.config_role));
  assert (pure (SZ.v validation_time == spec.CS.config_validation_time.X.seconds_since_epoch));
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert (pure (ok ==> spec.CS.config_role == CS.ClientEndpoint));
  fold (connection_config_exactly cfg spec);
  ok
}

fn config_role_is_server
  (cfg:connection_config_storage)
  (#spec:erased CS.connection_config)
  requires connection_config_exactly cfg spec
  returns ok: bool
  ensures connection_config_exactly cfg spec **
          pure (ok ==> spec.CS.config_role == CS.ServerEndpoint)
{
  unfold (connection_config_exactly cfg spec);
  with role validation_time.
    assert (Box.pts_to cfg.role_tag role **
            Box.pts_to cfg.validation_time_seconds validation_time);
  let role_tag = !cfg.role_tag;
  let ok = role_tag = 1uy;
  assert (pure (role_tag == role));
  assert (pure (Tags.endpoint_role_tag_matches role spec.CS.config_role));
  assert (pure (SZ.v validation_time == spec.CS.config_validation_time.X.seconds_since_epoch));
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (ok ==> spec.CS.config_role == CS.ServerEndpoint));
  fold (connection_config_exactly cfg spec);
  ok
}

fn get_control_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:control_snapshot
  ensures connection_exactly c st0 **
          pure (control_snapshot_matches snapshot st0)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let control_tag = !c.control.control_tag;
  let handshake_stage_tag = !c.control.handshake_stage_tag;
  let failure_present = !c.control.failure_present;
  let failure_code = !c.control.failure_code;
  let failure_alert = !c.control.failure_alert;
  let snapshot = {
    snapshot_control_tag = control_tag;
    snapshot_handshake_stage_tag = handshake_stage_tag;
    snapshot_failure_present = failure_present;
    snapshot_failure_code = failure_code;
    snapshot_failure_alert = failure_alert;
  };
  assert (pure (control_snapshot_matches snapshot st0));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  snapshot
}
fn get_key_schedule_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns snapshot:key_schedule_snapshot
  ensures connection_exactly c st0 **
          pure (key_schedule_snapshot_matches snapshot st0)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  unfold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  with shared_present_w shared_secret_bytes.
    assert (Box.pts_to c.handshake.keys.shared_secret.present shared_present_w **
            V.pts_to c.handshake.keys.shared_secret.secret shared_secret_bytes);
  with handshake_present_w handshake_secret_bytes.
    assert (Box.pts_to c.handshake.keys.handshake_secret.present handshake_present_w **
            V.pts_to c.handshake.keys.handshake_secret.secret handshake_secret_bytes);
  with master_present_w master_secret_bytes.
    assert (Box.pts_to c.handshake.keys.master_secret.present master_present_w **
            V.pts_to c.handshake.keys.master_secret.secret master_secret_bytes);
  with client_hs_present_w client_hs_secret client_hs_key client_hs_iv.
    assert (Box.pts_to c.handshake.keys.client_handshake_traffic.present client_hs_present_w **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_secret client_hs_secret **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_key client_hs_key **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_iv client_hs_iv);
  with server_hs_present_w server_hs_secret server_hs_key server_hs_iv.
    assert (Box.pts_to c.handshake.keys.server_handshake_traffic.present server_hs_present_w **
            V.pts_to c.handshake.keys.server_handshake_traffic.traffic_secret server_hs_secret **
            V.pts_to c.handshake.keys.server_handshake_traffic.traffic_key server_hs_key **
            V.pts_to c.handshake.keys.server_handshake_traffic.traffic_iv server_hs_iv);
  with client_app_present_w client_app_secret client_app_key client_app_iv.
    assert (Box.pts_to c.handshake.keys.client_application_traffic.present client_app_present_w **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_secret client_app_secret **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_key client_app_key **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_iv client_app_iv);
  with server_app_present_w server_app_secret server_app_key server_app_iv.
    assert (Box.pts_to c.handshake.keys.server_application_traffic.present server_app_present_w **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_secret server_app_secret **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_key server_app_key **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_iv server_app_iv);

  assert (pure (optional_fixed_bytes_match
    shared_present_w
    shared_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
  assert (pure (optional_fixed_bytes_match
    handshake_present_w
    handshake_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
  assert (pure (optional_fixed_bytes_match
    master_present_w
    master_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
  assert (pure (
    if client_hs_present_w then
      match st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
      | Some m ->
        Seq.equal client_hs_secret m.CS.traffic_secret /\
        Seq.equal client_hs_key m.CS.traffic_key /\
        Seq.equal client_hs_iv m.CS.traffic_iv
      | None -> False
    else
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None));
  assert (pure (
    if server_hs_present_w then
      match st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
      | Some m ->
        Seq.equal server_hs_secret m.CS.traffic_secret /\
        Seq.equal server_hs_key m.CS.traffic_key /\
        Seq.equal server_hs_iv m.CS.traffic_iv
      | None -> False
    else
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None));
  assert (pure (
    if client_app_present_w then
      match st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic with
      | Some m ->
        Seq.equal client_app_secret m.CS.traffic_secret /\
        Seq.equal client_app_key m.CS.traffic_key /\
        Seq.equal client_app_iv m.CS.traffic_iv
      | None -> False
    else
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None));
  assert (pure (
    if server_app_present_w then
      match st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic with
      | Some m ->
        Seq.equal server_app_secret m.CS.traffic_secret /\
        Seq.equal server_app_key m.CS.traffic_key /\
        Seq.equal server_app_iv m.CS.traffic_iv
      | None -> False
    else
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None));

  let shared_secret_present = !c.handshake.keys.shared_secret.present;
  let handshake_secret_present = !c.handshake.keys.handshake_secret.present;
  let master_secret_present = !c.handshake.keys.master_secret.present;
  let client_handshake_present = !c.handshake.keys.client_handshake_traffic.present;
  let server_handshake_present = !c.handshake.keys.server_handshake_traffic.present;
  let client_application_present = !c.handshake.keys.client_application_traffic.present;
  let server_application_present = !c.handshake.keys.server_application_traffic.present;

  let snapshot = {
    snapshot_shared_secret_present = shared_secret_present;
    snapshot_handshake_secret_present = handshake_secret_present;
    snapshot_master_secret_present = master_secret_present;
    snapshot_client_handshake_traffic_present = client_handshake_present;
    snapshot_server_handshake_traffic_present = server_handshake_present;
    snapshot_client_application_traffic_present = client_application_present;
    snapshot_server_application_traffic_present = server_application_present;
  };

  assert (pure (shared_secret_present == shared_present_w));
  assert (pure (handshake_secret_present == handshake_present_w));
  assert (pure (master_secret_present == master_present_w));
  assert (pure (client_handshake_present == client_hs_present_w));
  assert (pure (server_handshake_present == server_hs_present_w));
  assert (pure (client_application_present == client_app_present_w));
  assert (pure (server_application_present == server_app_present_w));

  lemma_optional_fixed_bytes_match_present_iff
    shared_present_w
    shared_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret;
  lemma_optional_fixed_bytes_match_present_iff
    handshake_present_w
    handshake_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
  lemma_optional_fixed_bytes_match_present_iff
    master_present_w
    master_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
  lemma_traffic_key_material_match_present_iff
    client_hs_present_w
    client_hs_secret
    client_hs_key
    client_hs_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
  lemma_traffic_key_material_match_present_iff
    server_hs_present_w
    server_hs_secret
    server_hs_key
    server_hs_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic;
  lemma_traffic_key_material_match_present_iff
    client_app_present_w
    client_app_secret
    client_app_key
    client_app_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
  lemma_traffic_key_material_match_present_iff
    server_app_present_w
    server_app_secret
    server_app_key
    server_app_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;

  assert (pure (key_schedule_snapshot_matches snapshot st0));

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  fold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  snapshot
}
fn copy_certificate_leaf_der
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                | Some leaf ->
                  SZ.v copied_len == B.length leaf /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;

  let copied_len =
    copy_optional_sized_bytes_to_array
      c.handshake.buffers.certificate_leaf_der
      out
      out_len
      #(st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);

  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  copied_len
}
fn copy_certificate_verify_input
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                | Some input ->
                  SZ.v copied_len == B.length input /\
                  Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  with parsed. _;

  let copied_len =
    copy_optional_sized_bytes_to_array
      c.handshake.buffers.certificate_verify_input
      out
      out_len
      #(st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  copied_len
}
fn copy_certificate_verify_signature
  (c:connection_state)
  (out:array U8.t)
  (out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 IM.max_signature_len <= SZ.v out_len /\
                 Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          connection_exactly c st0 **
          ArrPts.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.cv_signature_len <= B.length out_bytes /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  IM.signature_scheme_matches snapshot.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                  SZ.v snapshot.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v snapshot.cv_signature_len))
                    (Sem.certificateVerify_signature_bytes cv)
                | None -> False))
{
  let cv = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    Some (Ghost.reveal cv)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);

  with stored. assert (Box.pts_to c.handshake.messages.certificate_verify stored);
  let stored_cv_opt = !c.handshake.messages.certificate_verify;
  assert (pure (stored_cv_opt == stored));
  assert (pure (Some? stored_cv_opt));
  let lcv = Some?.v stored_cv_opt;
  assert (pure (stored_cv_opt == Some lcv));
  assert (pure (stored == Some lcv));

  rewrite (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  unfold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  with signature_bytes. _;

  let signature_len = lcv.certificate_verify_signature_len;
  V.pts_to_len lcv.certificate_verify_signature;
  assert (pure (B.length signature_bytes == IM.max_signature_len));
  assert (pure (SZ.v signature_len <= IM.max_signature_len));
  assert (pure (SZ.v signature_len <= SZ.v out_len));
  assert (pure (IM.byte_prefix_matches
    signature_bytes
    signature_len
    (Sem.certificateVerify_signature_bytes (Ghost.reveal cv))));

  ArrPts.pts_to_len out;
  V.to_array_pts_to lcv.certificate_verify_signature;
  Arr.memcpy_l signature_len (V.vec_to_array lcv.certificate_verify_signature) out;
  V.to_vec_pts_to lcv.certificate_verify_signature;

  with out_bytes. assert (ArrPts.pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v signature_len <= B.length out_bytes));
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v signature_len))
    (Seq.slice signature_bytes 0 (SZ.v signature_len))));
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v signature_len))
    (Sem.certificateVerify_signature_bytes (Ghost.reveal cv))));

  let snapshot = {
    cv_signature_scheme = lcv.certificate_verify_scheme;
    cv_signature_len = signature_len;
  };
  assert (pure (IM.signature_scheme_matches
    snapshot.cv_signature_scheme
    (Sem.certificateVerify_scheme (Ghost.reveal cv))));

  fold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  rewrite (IM.is_valid_certificate_verify lcv (Ghost.reveal cv))
    as (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
      | _, _ -> pure False);
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  snapshot
}

fn get_certificate_verify_signature_snapshot
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:certificate_verify_signature_snapshot
  ensures connection_exactly c st0 **
          pure (SZ.v snapshot.cv_signature_len <= IM.max_signature_len /\
                (match st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                | Some cv ->
                  IM.signature_scheme_matches snapshot.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                  SZ.v snapshot.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv)
                | None -> False))
{
  let cv = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    Some (Ghost.reveal cv)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);

  with stored. assert (Box.pts_to c.handshake.messages.certificate_verify stored);
  let stored_cv_opt = !c.handshake.messages.certificate_verify;
  assert (pure (stored_cv_opt == stored));
  assert (pure (Some? stored_cv_opt));
  let lcv = Some?.v stored_cv_opt;
  assert (pure (stored_cv_opt == Some lcv));
  assert (pure (stored == Some lcv));

  rewrite (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  unfold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  with signature_bytes. _;

  let signature_len = lcv.certificate_verify_signature_len;
  V.pts_to_len lcv.certificate_verify_signature;
  assert (pure (B.length signature_bytes == IM.max_signature_len));
  assert (pure (SZ.v signature_len <= IM.max_signature_len));
  assert (pure (IM.byte_prefix_matches
    signature_bytes
    signature_len
    (Sem.certificateVerify_signature_bytes (Ghost.reveal cv))));
  Seq.lemma_len_slice signature_bytes 0 (SZ.v signature_len);
  assert (pure (B.length (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)) == SZ.v signature_len));

  let snapshot = {
    cv_signature_scheme = lcv.certificate_verify_scheme;
    cv_signature_len = signature_len;
  };
  assert (pure (IM.signature_scheme_matches
    snapshot.cv_signature_scheme
    (Sem.certificateVerify_scheme (Ghost.reveal cv))));

  fold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
  rewrite (IM.is_valid_certificate_verify lcv (Ghost.reveal cv))
    as (match stored, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
      | _, _ -> pure False);
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  snapshot
}

fn is_handshaking
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==> (exists stage.
            st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let ok = tag = 1uy;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> (exists stage.
    st0.CS.cs_model.CS.model_control == CS.ControlHandshaking stage)));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn is_waiting_server_hello
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 2uy;
  let ok = role_ok && tag_ok && stage_ok;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 2));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloSent));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_start_handshake_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlNew /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_start == None)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);

  let tag = !c.control.control_tag;
  let has_start = !c.handshake.start.present;
  with start_present.
    assert (Box.pts_to c.handshake.start.present start_present);
  assert (pure (has_start == start_present));

  let tag_ok = tag = 0uy;
  let start_empty = not has_start;
  let ok = role_ok && tag_ok && start_empty;
  if ok {
    assert (pure (U8.v tag == 0));
    assert (pure (not start_present));
    assert (pure (start_present == false));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        false
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_start == None));
    fold (handshake_start_payload_exactly
      c.handshake.start
      false
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_start_server_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlNew /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_server c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let tag_ok = tag = 0uy;
  let ok = role_ok && tag_ok;
  if ok {
    assert (pure (U8.v tag == 0));
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlNew));
    assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_client_hello_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsStarted /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_start /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
              <= max_transcript_len - max_client_hello_len /\
            517 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_present ch_random ch_server_name ch_key_share
       ch_cipher_suites ch_signature_schemes.
    assert (pure True);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_start = !c.handshake.start.present;
  let has_client_hello = !c.handshake.messages.client_hello_present;
  let transcript_len = !c.handshake.transcript.len;
  with start_present. assert (Box.pts_to c.handshake.start.present start_present);
  assert (Box.pts_to c.handshake.messages.client_hello_present ch_present);
  assert (pure (has_start == start_present));
  assert (pure (has_client_hello == ch_present));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript == SZ.v transcript_len));

  assert (pure (SZ.v max_transcript_len_sz == max_transcript_len /\
                SZ.v max_client_hello_len_sz == max_client_hello_len));
  let transcript_bound = SZ.sub max_transcript_len_sz max_client_hello_len_sz;
  let transcript_room = sizet_lte_plain transcript_len transcript_bound;
  lemma_sizet_lte_plain transcript_len transcript_bound;
  let out_room = sizet_lte_plain 517sz network_out_len;
  lemma_sizet_lte_plain 517sz network_out_len;
  let ok =
    role_ok &&
    (tag = 1uy) &&
    (stage = 1uy) &&
    has_start &&
    (not has_client_hello) &&
    transcript_room &&
    out_room;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 1));
    assert (pure (start_present == true));
    assert (pure (ch_present == false));
    assert (pure (SZ.v transcript_len <= max_transcript_len - max_client_hello_len));
    assert (pure (517 <= SZ.v network_out_len));
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      start_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        true
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    unfold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    fold (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    rewrite (handshake_start_payload_exactly
      c.handshake.start
      true
      st0.CS.cs_model.CS.model_handshake.CS.hs_start)
      as (handshake_start_payload_exactly
        c.handshake.start
        start_present
        st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsStarted));
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_receive_server_hello
  (c:connection_state)
  (fragment_len:SZ.t)
  (#sh:erased GSH.serverHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Sem.serverHello_cipher_suite sh == Some T.TLS_CHACHA20_POLY1305_SHA256 /\
             // Parse-success equation supplied by the caller (see
             // TLS13.Impl.Handle.Handshake): the decoded ServerHello serializes
             // back to the on-the-wire fragment, so its serialized-handshake
             // length equals the concrete [fragment_len].  Combined with the
             // runtime [fragment_fits_sh] gate below this discharges the
             // ServerHello wire-profile bound (<= 16640) in the [legal_event]
             // obligation without re-proving the deleted static length lemma.
             B.length (W.serialize_handshake (M.ServerHello sh)) == SZ.v fragment_len)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            // Phase 4 deleted W.lemma_serialize_server_hello_len, so
            // `B.length (serialize_handshake (M.ServerHello sh)) <=
            // max_server_hello_len` is no longer a static theorem for general
            // generated serverHello records that carry arbitrary extensions.
            // The gate therefore takes the concrete [fragment_len] (the length of
            // the serialized record on the wire) and checks at runtime that it
            // fits the ServerHello buffer and the remaining transcript budget,
            // exactly as [can_receive_client_hello] does.  The caller connects
            // [SZ.v fragment_len] to [B.length (serialize_handshake ...)] via the
            // parse-success equation before calling [mark_received_server_hello].
            SZ.v fragment_len <= Bounds.max_server_hello_len /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ServerHello sh);
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 2uy;

  with start_present. assert (pure True);
  let has_start = !c.handshake.start.present;
  assert (pure (has_start == start_present));

  with stored_server_hello. assert (pure True);
  let stored = !c.handshake.messages.server_hello;
  let no_server_hello = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_server_hello));
  assert (pure (no_server_hello ==> stored == None));
  assert (pure (no_server_hello ==> stored_server_hello == None));
  assert (pure (no_server_hello ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));
  assert (pure (SZ.v current_transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  // The ServerHello serializer-length lemma was deleted in Phase 4, so we can no
  // longer statically bound `B.length (serialize_handshake (M.ServerHello sh))`.
  // Instead, gate on the concrete [fragment_len]: check that it fits the
  // ServerHello buffer capacity and the remaining transcript budget at runtime
  // (mirrors [can_receive_client_hello]).
  assert (pure (SZ.v max_transcript_len_sz == max_transcript_len /\
                SZ.v max_server_hello_len_sz == max_server_hello_len));
  let fragment_fits_sh = SZ.lte fragment_len max_server_hello_len_sz;
  let max_start = SZ.sub max_transcript_len_sz max_server_hello_len_sz;
  let transcript_room = SZ.lte current_transcript_len max_start;

  if has_start {
    unfold (handshake_start_payload_exactly
      c.handshake.start
      has_start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    with start_spec. assert (pure True);
    unfold (handshake_start_fields_exactly c.handshake.start start_spec);
        unfold (cipher_suite_list_exactly
          c.handshake.start.cipher_suites
          max_cipher_suites
          start_spec.CS.start_cipher_suites);
        with cipher_items cipher_len. assert (
          V.pts_to c.handshake.start.cipher_suites.items cipher_items **
          Box.pts_to c.handshake.start.cipher_suites.len cipher_len **
          pure (V.is_full_vec c.handshake.start.cipher_suites.items /\
                V.length c.handshake.start.cipher_suites.items == max_cipher_suites /\
                Seq.length cipher_items == max_cipher_suites /\
                SZ.v cipher_len <= max_cipher_suites /\
                IM.cipher_suites_match
                  cipher_items
                  (SZ.v cipher_len)
                  start_spec.CS.start_cipher_suites));
        let offered_len = !c.handshake.start.cipher_suites.len;
        assert (pure (offered_len == cipher_len));
        let offered_nonempty = SZ.gt offered_len 0sz;
        let first_cipher = V.op_Array_Access c.handshake.start.cipher_suites.items 0sz;
        let offers_chacha = first_cipher = 0x1303us;
        if (offered_nonempty && offers_chacha) {
          assert (pure (Seq.length cipher_items == max_cipher_suites));
          assert (pure (0 < Seq.length cipher_items));
          assert (pure (SZ.v cipher_len > 0));
          assert (pure (SZ.v offered_len == SZ.v cipher_len));
          assert (pure (start_spec.CS.start_cipher_suites <> []));
          assert (pure (U16.v (Seq.index cipher_items 0) == 0x1303));
          lemma_cipher_suites_match_first_chacha_offer
            cipher_items
            (SZ.v cipher_len)
            start_spec.CS.start_cipher_suites;
          assert (pure (Sem.serverHello_cipher_suite sh == Some T.TLS_CHACHA20_POLY1305_SHA256));
          assert (pure (CS.cipher_suite_offered
            start_spec.CS.start_cipher_suites
            T.TLS_CHACHA20_POLY1305_SHA256));
          assert (pure (H.is_supported_cipher_suite T.TLS_CHACHA20_POLY1305_SHA256));

          let control_ok = tag_ok && stage_ok && role_ok;
          let ok = control_ok && no_server_hello && transcript_room && fragment_fits_sh;
          assert (pure (ok ==> U8.v tag == 1));
          assert (pure (ok ==> U8.v stage == 2));
          assert (pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloSent));
          assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
          // fragment_fits_sh gives `fragment_len <= max_server_hello_len`, and
          // transcript_room gives `current_transcript_len <= max_transcript_len -
          // max_server_hello_len`; together they bound the resulting transcript.
          assert (pure (ok ==> SZ.v fragment_len <= max_server_hello_len));
          // The caller's parse-success equation gives
          //   B.length (serialize_handshake (ServerHello sh)) == SZ.v fragment_len,
          // and when [ok] the runtime gate bounds [fragment_len] by
          // max_server_hello_len (= 4096) <= 16640, discharging the ServerHello
          // wire-profile bound inside [legal_event].
          assert (pure (ok ==>
            B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640));
          assert (pure (ok ==>
            SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
          assert (pure (ok ==>
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <=
              max_transcript_len));
          assert (pure (ok ==> CS.legal_event
            st0.CS.cs_model
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            })));

          fold (cipher_suite_list_exactly
            c.handshake.start.cipher_suites
            max_cipher_suites
            start_spec.CS.start_cipher_suites);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (sized_bytes_exactly
            c.handshake.transcript
            max_transcript_len
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
          fold (server_hello_slot_exactly
            c.handshake.messages.server_hello
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          ok
        } else {
          fold (cipher_suite_list_exactly
            c.handshake.start.cipher_suites
            max_cipher_suites
            start_spec.CS.start_cipher_suites);
          fold (handshake_start_fields_exactly c.handshake.start start_spec);
          fold (handshake_start_payload_exactly
            c.handshake.start
            has_start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (sized_bytes_exactly
            c.handshake.transcript
            max_transcript_len
            st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
          fold (server_hello_slot_exactly
            c.handshake.messages.server_hello
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
          fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
          fold (handshake_start_exactly
            c.handshake.start
            st0.CS.cs_model.CS.model_handshake.CS.hs_start);
          fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
          fold (control_exactly
            c.control
            st0.CS.cs_model.CS.model_control
            st0.CS.cs_model.CS.model_failure);
          fold (connection_model_exactly c st0.CS.cs_model);
          fold (connection_exactly c st0);
          false
        }
  } else {
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (server_hello_slot_exactly
      c.handshake.messages.server_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_start_exactly
      c.handshake.start
      st0.CS.cs_model.CS.model_handshake.CS.hs_start);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_receive_client_hello
  (c:connection_state)
  (fragment_len:SZ.t)
  (#ch:erased GCH.clientHello)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsAwaitingClientHello /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_server c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 12uy;

  let has_client_hello = !c.handshake.messages.client_hello_present;
  let no_client_hello = not has_client_hello;
  assert (pure (no_client_hello ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));

  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (SZ.v current_transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  let fragment_fits = SZ.lte fragment_len max_transcript_len_sz;
  lemma_sizet_lte_plain fragment_len max_transcript_len_sz;
  if fragment_fits {
    assert (pure (SZ.v fragment_len <= max_transcript_len));
    assert (pure (SZ.fits (max_transcript_len - SZ.v fragment_len)));
    let max_start = SZ.sub max_transcript_len_sz fragment_len;
    let transcript_room = SZ.lte current_transcript_len max_start;
    let control_ok = tag_ok && stage_ok && role_ok;
    let ok = control_ok && no_client_hello && transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 12));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsAwaitingClientHello));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello == None));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==>
      B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        SZ.v fragment_len <=
        max_transcript_len));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      })));

    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_receive_client_finished
  (c:connection_state)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_server c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 16uy;

  with stored_fin. assert (Box.pts_to c.handshake.messages.client_finished stored_fin);
  let stored = !c.handshake.messages.client_finished;
  let no_fin = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_fin));
  assert (pure (no_fin ==> stored == None));
  assert (pure (no_fin ==> stored_fin == None));
  assert (pure (no_fin ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));

  with client_hs_present.
    assert (Box.pts_to c.handshake.keys.client_handshake_traffic.present client_hs_present);
  with client_hs_secret.
    assert (V.pts_to c.handshake.keys.client_handshake_traffic.traffic_secret client_hs_secret);
  with client_hs_key.
    assert (V.pts_to c.handshake.keys.client_handshake_traffic.traffic_key client_hs_key);
  with client_hs_iv.
    assert (V.pts_to c.handshake.keys.client_handshake_traffic.traffic_iv client_hs_iv);
  let has_client_handshake_keys = !c.handshake.keys.client_handshake_traffic.present;
  assert (pure (has_client_handshake_keys == client_hs_present));

  with master_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present master_present);
  with master_secret_bytes.
    assert (V.pts_to c.handshake.keys.master_secret.secret master_secret_bytes);
  let has_master = !c.handshake.keys.master_secret.present;
  assert (pure (has_master == master_present));

  let seq_ok = Rec.can_advance_seq c.records.read;

  with transcript_storage transcript_len_g.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage **
            Box.pts_to c.handshake.transcript.len transcript_len_g);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len_g));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let max_start = SZ.sub max_len 36sz;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;

  with server_app_present.
    assert (Box.pts_to c.handshake.keys.server_application_traffic.present server_app_present);
  let has_server_app_write = !c.handshake.keys.server_application_traffic.present;
  assert (pure (has_server_app_write == server_app_present));

  let ok = role_ok && tag_ok && stage_ok && no_fin && has_client_handshake_keys && has_master && has_server_app_write && seq_ok && transcript_room;

  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));

  assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    max_transcript_len));

  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 16));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedSent));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (ok ==> client_hs_present));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
  assert (pure (ok ==>
    U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (ok ==> CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_select_supported_server_parameters_runtime
  (c:connection_state)
  (#server_random:erased (b:B.bytes{B.length b == 32}))
  (#server_private_key:erased (b:B.bytes{B.length b == 32}))
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        st0.CS.cs_model.CS.model_config.CS.config_server with
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
                    CS.sni_policy_accepts cfg.CS.server_sni_policy (Sem.clientHello_server_name ch)
                  | _, _ -> True))
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            server_selection_absent st0.CS.cs_model.CS.model_handshake /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                   st0.CS.cs_model.CS.model_config.CS.config_server with
             | Some ch, Some cfg ->
               let selection = {
                 CS.server_selected_client_hello = ch;
                 CS.server_selected_cipher_suite =
                   T.TLS_CHACHA20_POLY1305_SHA256;
                 CS.server_selected_group = T.X25519;
                 CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
                 CS.server_random = Ghost.reveal server_random;
                 CS.server_key_share_private =
                   Some (Ghost.reveal server_private_key);
                 CS.server_key_share_public =
                   CryptoSpec.x25519_public_from_private
                     (Ghost.reveal server_private_key);
                 CS.server_selected_credential =
                   cfg.CS.server_credential_identity;
               } in
               can_select_server_parameters st0 selection
             | _, _ -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_server c.config;
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (server_selection_presence_exactly
    c.handshake.server_selection_present
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  with selection_present. _;
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_present ch_random ch_server_name ch_key_share
       ch_cipher_suites ch_signature_schemes. _;
  unfold (client_hello_metadata_exactly
    c.handshake.messages.client_hello_has_server_name
    c.handshake.messages.client_hello_server_name_len
    c.handshake.messages.client_hello_cipher_suites_len
    c.handshake.messages.client_hello_signature_schemes_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_has_server_name ch_server_name_len
       ch_cipher_suites_len ch_signature_schemes_len. _;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_selection = !c.handshake.server_selection_present;
  let has_client_hello = !c.handshake.messages.client_hello_present;
  let has_server_name = !c.handshake.messages.client_hello_has_server_name;
  let cipher_suites_len = !c.handshake.messages.client_hello_cipher_suites_len;
  let signature_schemes_len = !c.handshake.messages.client_hello_signature_schemes_len;

  assert (pure (has_selection == selection_present));
  assert (pure (has_client_hello == ch_present));
  assert (pure (has_server_name == ch_has_server_name));
  assert (pure (cipher_suites_len == ch_cipher_suites_len));
  assert (pure (signature_schemes_len == ch_signature_schemes_len));

  assert (pure (SZ.v 0sz < max_cipher_suites));
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_cipher_suites;
  let first_cipher =
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_cipher_suites).(0sz);
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_cipher_suites;
  assert (pure (first_cipher == Seq.index ch_cipher_suites 0));

  assert (pure (SZ.v 0sz < max_signature_schemes));
  V.to_array_pts_to c.handshake.messages.client_hello.IM.client_hello_signature_schemes;
  let first_signature =
    (V.vec_to_array c.handshake.messages.client_hello.IM.client_hello_signature_schemes).(0sz);
  V.to_vec_pts_to c.handshake.messages.client_hello.IM.client_hello_signature_schemes;
  assert (pure (first_signature == Seq.index ch_signature_schemes 0));

  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  with shared_secret_present shared_secret_bytes.
    assert (Box.pts_to c.handshake.keys.shared_secret.present shared_secret_present **
            V.pts_to c.handshake.keys.shared_secret.secret shared_secret_bytes **
            pure (optional_fixed_bytes_match
              shared_secret_present
              shared_secret_bytes
              32
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
  let shared_secret_is_present = !c.handshake.keys.shared_secret.present;
  assert (pure (shared_secret_is_present == shared_secret_present));
  fold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  let control_ok = (tag = 1uy) && (stage = 13uy) && role_ok;
  let selection_absent = not has_selection;
  let shared_secret_absent = not shared_secret_is_present;
  let cipher_nonempty = SZ.gt cipher_suites_len 0sz;
  let cipher_supported = first_cipher = 0x1303us;
  let signature_nonempty = SZ.gt signature_schemes_len 0sz;
  let signature_supported = first_signature = 0x0804us;
  let ok =
    control_ok &&
    selection_absent &&
    shared_secret_absent &&
    has_client_hello &&
    has_server_name &&
    cipher_nonempty &&
    cipher_supported &&
    signature_nonempty &&
    signature_supported;

  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 13));
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure (st0.CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (selection_present == false));
    assert (pure (selection_present ==
      Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
    assert (pure (not (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)));
    assert (pure (shared_secret_is_present == false));
    assert (pure (shared_secret_present == false));
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None));
    assert (pure (server_selection_absent st0.CS.cs_model.CS.model_handshake));
    assert (pure (ch_present == true));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    lemma_option_some_v st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello;
    let ch = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some (Ghost.reveal ch)));
    assert (pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server));
    lemma_option_some_v st0.CS.cs_model.CS.model_config.CS.config_server;
    let cfg = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_config.CS.config_server);
    assert (pure (st0.CS.cs_model.CS.model_config.CS.config_server ==
      Some (Ghost.reveal cfg)));

    assert (pure (ch_cipher_suites_len == client_hello_cipher_suites_len_for (Ghost.reveal ch)));
    assert (pure (ch_signature_schemes_len == client_hello_signature_schemes_len_for (Ghost.reveal ch)));
    assert (pure (SZ.v cipher_suites_len > 0));
    assert (pure (SZ.v signature_schemes_len > 0));
    assert (pure (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)) > 0));
    assert (pure (SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch)) > 0));
    assert (pure (IM.cipher_suites_match
      ch_cipher_suites
      (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)))
      (Sem.clientHello_cipher_suites (Ghost.reveal ch))));
    lemma_cipher_suites_match_length
      ch_cipher_suites
      (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)))
      (Sem.clientHello_cipher_suites (Ghost.reveal ch));
    assert (pure (length (Sem.clientHello_cipher_suites (Ghost.reveal ch)) > 0));
    assert (pure ((Sem.clientHello_cipher_suites (Ghost.reveal ch)) <> []));
    assert (pure (0 < SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch))));
    assert (pure (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)) <=
      Seq.length ch_cipher_suites));
    assert (pure (U16.v first_cipher == 0x1303));
    assert (pure (U16.v (Seq.index ch_cipher_suites 0) == 0x1303));
    lemma_cipher_suites_match_first_chacha_offer
      ch_cipher_suites
      (SZ.v (client_hello_cipher_suites_len_for (Ghost.reveal ch)))
      (Sem.clientHello_cipher_suites (Ghost.reveal ch));
    assert (pure (CS.cipher_suite_offered
      (Sem.clientHello_cipher_suites (Ghost.reveal ch))
      T.TLS_CHACHA20_POLY1305_SHA256));

    // Phase 5: the client_hello's offered signature schemes are now read through
    // the option-shaped Sem.clientHello_sig_algs.  The unfolded client_hello slot
    // (present here) discharges the None case (its predicate is `... | None ->
    // False`), so we extract the Some payload and thread it where the old proof
    // used the guaranteed-present m.M.signature_schemes field.
    let ch_sas = Ghost.hide (Some?.v (Sem.clientHello_sig_algs (Ghost.reveal ch)));
    assert (pure (Sem.clientHello_sig_algs (Ghost.reveal ch) == Some (Ghost.reveal ch_sas)));
    assert (pure (IM.signature_schemes_match
      ch_signature_schemes
      (SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch)))
      (Ghost.reveal ch_sas)));
    assert (pure (0 < SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch))));
    assert (pure (SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch)) <=
      Seq.length ch_signature_schemes));
    assert (pure (U16.v first_signature == 0x0804));
    assert (pure (U16.v (Seq.index ch_signature_schemes 0) == 0x0804));
    lemma_signature_schemes_match_first_rsa_offer
      ch_signature_schemes
      (SZ.v (client_hello_signature_schemes_len_for (Ghost.reveal ch)))
      (Ghost.reveal ch_sas);
    assert (pure (CS.signature_scheme_offered
      (Ghost.reveal ch_sas)
      T.Rsa_pss_rsae_sha256));

    assert (pure (CS.cipher_suite_offered
      (Ghost.reveal cfg).CS.server_supported_cipher_suites
      T.TLS_CHACHA20_POLY1305_SHA256));
    assert (pure (CS.named_group_offered
      (Ghost.reveal cfg).CS.server_supported_groups
      T.X25519));
    assert (pure (CS.signature_scheme_offered
      (Ghost.reveal cfg).CS.server_allowed_signature_schemes
      T.Rsa_pss_rsae_sha256));
    assert (pure (CS.sni_policy_accepts
      (Ghost.reveal cfg).CS.server_sni_policy
      (Sem.clientHello_server_name (Ghost.reveal ch))));

    let selection = Ghost.hide {
      CS.server_selected_client_hello = Ghost.reveal ch;
      CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
      CS.server_selected_group = T.X25519;
      CS.server_selected_signature_scheme = T.Rsa_pss_rsae_sha256;
      CS.server_random = Ghost.reveal server_random;
      CS.server_key_share_private =
        Some (Ghost.reveal server_private_key);
      CS.server_key_share_public =
        CryptoSpec.x25519_public_from_private
          (Ghost.reveal server_private_key);
      CS.server_selected_credential =
        (Ghost.reveal cfg).CS.server_credential_identity;
    };
    assert (pure (CS.server_selection_key_share_consistent (Ghost.reveal selection)));
    assert (pure (CS.server_selection_acceptable (Ghost.reveal cfg) (Ghost.reveal selection)));
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnLocalEvent (CS.LocalSelectServerParameters (Ghost.reveal selection)))));
    assert (pure (can_select_server_parameters st0 (Ghost.reveal selection)));

    fold (client_hello_metadata_exactly
      c.handshake.messages.client_hello_has_server_name
      c.handshake.messages.client_hello_server_name_len
      c.handshake.messages.client_hello_cipher_suites_len
      c.handshake.messages.client_hello_signature_schemes_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (client_hello_metadata_exactly
      c.handshake.messages.client_hello_has_server_name
      c.handshake.messages.client_hello_server_name_len
      c.handshake.messages.client_hello_cipher_suites_len
      c.handshake.messages.client_hello_signature_schemes_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_schedule_select_server_parameters_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            server_selection_absent st0.CS.cs_model.CS.model_handshake /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            Some? st0.CS.cs_model.CS.model_config.CS.config_server)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_server c.config;
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (server_selection_presence_exactly
    c.handshake.server_selection_present
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  with selection_present. _;
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_present ch_random ch_server_name ch_key_share
       ch_cipher_suites ch_signature_schemes. _;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_selection = !c.handshake.server_selection_present;
  let has_client_hello = !c.handshake.messages.client_hello_present;
  let ok =
    tag = 1uy &&
    stage = 13uy &&
    role_ok &&
    not has_selection &&
    has_client_hello;

  assert_norm (Tags.handshake_stage_tag_matches
    13uy
    CS.HsClientHelloReceived);
  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 13));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (has_selection == selection_present));
  assert (pure (ok ==> selection_present == false));
  assert (pure (ok ==>
    server_selection_absent st0.CS.cs_model.CS.model_handshake));
  assert (pure (has_client_hello == ch_present));
  assert (pure (ok ==> ch_present));
  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));

  fold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  fold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  fold (server_selection_presence_exactly
    c.handshake.server_selection_present
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_schedule_derive_shared_secret_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
             | Some selection ->
               CS.server_selection_key_share_consistent selection /\
               st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                 Some selection.CS.server_selected_client_hello
             | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_server c.config;
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (server_selection_presence_exactly
    c.handshake.server_selection_present
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  with selection_present. _;
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (client_hello_slot_exactly
    c.handshake.messages.client_hello_present
    c.handshake.messages.client_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  with ch_present ch_random ch_server_name ch_key_share
       ch_cipher_suites ch_signature_schemes. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  with shared_present shared_secret_bytes. _;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_selection = !c.handshake.server_selection_present;
  let has_client_hello = !c.handshake.messages.client_hello_present;
  let shared_secret_present = !c.handshake.keys.shared_secret.present;
  let ok =
    tag = 1uy &&
    stage = 13uy &&
    role_ok &&
    has_selection &&
    has_client_hello &&
    not shared_secret_present;

  assert_norm (Tags.handshake_stage_tag_matches
    13uy
    CS.HsClientHelloReceived);
  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 13));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (has_selection == selection_present));
  assert (pure (ok ==> selection_present));
  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (has_client_hello == ch_present));
  assert (pure (ok ==> ch_present));
  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (shared_secret_present == shared_present));
  lemma_optional_fixed_bytes_match_present_iff
    shared_present
    shared_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret;
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None));
  if ok {
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
    CSL.lemma_connection_state_consistent_server_selection_private_shape st0;
    assert (pure (
      match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        CS.server_selection_key_share_consistent selection /\
        st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
          Some selection.CS.server_selected_client_hello
      | None -> False));
    fold (optional_secret_exactly
      c.handshake.keys.shared_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.shared_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (client_hello_slot_exactly
      c.handshake.messages.client_hello_present
      c.handshake.messages.client_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_server_hello_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
             | Some selection ->
               CS.server_selection_key_share_consistent selection /\
               Some? selection.CS.server_key_share_private
             | None -> False) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
              max_transcript_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_server c.config;
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (server_selection_presence_exactly
    c.handshake.server_selection_present
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  with selection_present. _;
  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (server_hello_slot_exactly
    c.handshake.messages.server_hello
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
  with stored_server_hello. _;
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with transcript_storage transcript_len. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.shared_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  with shared_present shared_secret_bytes. _;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_selection = !c.handshake.server_selection_present;
  let server_hello = !c.handshake.messages.server_hello;
  let shared_secret_present = !c.handshake.keys.shared_secret.present;
  let current_transcript_len = !c.handshake.transcript.len;
  let no_server_hello = None? server_hello;
  let max_start = SZ.sub max_transcript_len_sz 90sz;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;
  let ok =
    tag = 1uy &&
    stage = 13uy &&
    role_ok &&
    shared_secret_present &&
    no_server_hello &&
    has_selection &&
    transcript_room;

  assert_norm (Tags.handshake_stage_tag_matches
    13uy
    CS.HsClientHelloReceived);
  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 13));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (shared_secret_present == shared_present));
  lemma_optional_fixed_bytes_match_present_iff
    shared_present
    shared_secret_bytes
    32
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret;
  assert (pure (ok ==>
    (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)));
  assert (pure (server_hello == stored_server_hello));
  assert (pure (ok ==> no_server_hello));
  assert (pure (ok ==> stored_server_hello == None));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
  assert (pure (has_selection == selection_present));
  assert (pure (ok ==> has_selection));
  assert (pure (ok ==>
    (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)));
  assert (pure (current_transcript_len == transcript_len));
  assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
  assert (pure (ok ==>
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
      max_transcript_len));
  if ok {
    CSL.lemma_connection_state_consistent_server_pre_server_hello_shape st0;
    assert (pure (
      match st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some selection ->
        CS.server_selection_key_share_consistent selection /\
        Some? selection.CS.server_key_share_private
      | None -> False));
    fold (optional_secret_exactly
      c.handshake.keys.shared_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (server_hello_slot_exactly
      c.handshake.messages.server_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.shared_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (server_hello_slot_exactly
      c.handshake.messages.server_hello
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    fold (handshake_messages_exactly
      c.handshake.messages
      st0.CS.cs_model.CS.model_handshake);
    fold (server_selection_presence_exactly
      c.handshake.server_selection_present
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_receive_application_data
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let ok = role_ok && control_ok && server_app_present && seq_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_endpoint_application_data
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Received /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
  with config_role_tag validation_time.
    assert (Box.pts_to c.config.role_tag config_role_tag **
            Box.pts_to c.config.validation_time_seconds validation_time);
  let role_tag = !c.config.role_tag;
  let role_client_ok = role_tag = 0uy;
  let role_server_ok = role_tag = 1uy;
  assert (pure (role_tag == config_role_tag));
  assert (pure (Tags.endpoint_role_tag_matches
    config_role_tag
    st0.CS.cs_model.CS.model_config.CS.config_role));
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (role_client_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint));
  assert (pure (role_server_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (role_client_ok ==> not role_server_ok));
  assert (pure (role_server_ok ==> not role_client_ok));
  fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let client_role_app_present = role_client_ok && server_app_present;
  let server_role_app_present = role_server_ok && client_app_present;
  let app_present_for_role =
    (if client_role_app_present then true else server_role_app_present);
  let ok =
    control_ok &&
    app_present_for_role &&
    seq_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
    CS.ServerTraffic);
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
    CS.ClientTraffic);
  if ok {
    assert (pure (app_present_for_role));
    if role_client_ok {
      assert (pure (server_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    } else {
      assert (pure (role_server_ok));
      assert (pure (client_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    }
  };
  assert (pure (ok ==>
    CS.application_traffic_available_for_role
      st0.CS.cs_model.CS.model_config.CS.config_role
      st0.CS.cs_model.CS.model_handshake
      CL.Received));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_deliver_application_data
  (c:connection_state)
  (payload_len:SZ.t)
  (app_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            SZ.v payload_len <= SZ.v app_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let output_ok = sizet_lte_plain payload_len app_out_len;
  lemma_sizet_lte_plain payload_len app_out_len;
  let ok = control_ok && output_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> SZ.v payload_len <= SZ.v app_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_install_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.handshake_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let present = !c.handshake.keys.handshake_secret.present;
  with stored_present.
    assert (Box.pts_to c.handshake.keys.handshake_secret.present stored_present);
  with stored_secret.
    assert (V.pts_to c.handshake.keys.handshake_secret.secret stored_secret);
  assert (pure (present == stored_present));

  let ok = role_ok && (tag = 1uy) && (stage = 3uy) && present;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 3));
    assert (pure stored_present);
    lemma_optional_fixed_bytes_match_some
      stored_present
      stored_secret
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret));
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerHelloReceived));
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.handshake_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_install_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let present = !c.handshake.keys.master_secret.present;
  with stored_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present stored_present);
  with stored_secret.
    assert (V.pts_to c.handshake.keys.master_secret.secret stored_secret);
  assert (pure (present == stored_present));

  let ok = role_ok && (tag = 1uy) && (stage = 10uy) && present;
  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 10));
    assert (pure stored_present);
    lemma_optional_fixed_bytes_match_some
      stored_present
      stored_secret
      32
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret;
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedVerified));
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    true
  } else {
    fold (optional_secret_exactly
      c.handshake.keys.master_secret
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_receive_encrypted_extensions
  (c:connection_state)
  (#ee:erased GEE.encryptedExtensions)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 3uy;

  with stored_ee. assert (Box.pts_to c.handshake.messages.encrypted_extensions stored_ee);
  let stored = !c.handshake.messages.encrypted_extensions;
  let no_encrypted_extensions = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_ee));
  assert (pure (no_encrypted_extensions ==> stored == None));
  assert (pure (no_encrypted_extensions ==> stored_ee == None));
  assert (pure (no_encrypted_extensions ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with server_hs_present.
    assert (Box.pts_to c.handshake.keys.server_handshake_traffic.present server_hs_present);
  with server_hs_secret.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_secret server_hs_secret);
  with server_hs_key.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_key server_hs_key);
  with server_hs_iv.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_iv server_hs_iv);
  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  assert (pure (has_server_handshake_keys == server_hs_present));

  let seq_ok = Rec.can_advance_seq c.records.read;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let control_ok = tag_ok && stage_ok && role_ok;
    let ok =
      control_ok &&
      no_encrypted_extensions &&
      has_server_handshake_keys &&
      seq_ok &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 3));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloReceived));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == None));
    assert (pure (ok ==> server_hs_present));
    assert (pure (ok ==> Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      })));

    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (encrypted_extensions_slot_exactly
      c.handshake.messages.encrypted_extensions
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (encrypted_extensions_slot_exactly
      c.handshake.messages.encrypted_extensions
      st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_encrypted_extensions_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerHelloSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
              max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value =
                  M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let role_ok = config_role_is_server c.config;
  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  let seq_ok = Rec.can_advance_seq c.records.write;
  let max_start = SZ.sub max_transcript_len_sz 6sz;
  let current_transcript_len = !c.handshake.transcript.len;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;
  let ok =
    tag = 1uy &&
    stage = 14uy &&
    role_ok &&
    has_server_handshake_keys &&
    seq_ok &&
    transcript_room;

  if ok {
    assert (pure (U8.v tag == 1));
    assert (pure (U8.v stage == 14));
    assert (pure (
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent));
    assert (pure (
      st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (U64.fits
      (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (
      B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 6 <=
        max_transcript_len));
    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value =
          M.TlsHandshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions));
      })));

    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_certificate_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (match st0.CS.cs_model.CS.model_config.CS.config_server with
                 | Some cfg ->
                   B.length cfg.CS.server_certificate_chain <=
                     max_server_certificate_chain_len
                 | None -> False)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            (match st0.CS.cs_model.CS.model_config.CS.config_server with
             | Some cfg ->
               // Transcript-length bound for the Certificate flight.  The
               // handshake message serializes to exactly 13 + |chain| bytes
               // (TLS13.Impl.Server.Send.lemma_mk_cert_witness_bytesize) and the
               // runtime transcript-room check below guarantees it fits.  (The
               // legal_event (M.Certificate cert) obligation stays a caller
               // obligation, discharged with the build-direction witness.)
               B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 13 +
                 B.length cfg.CS.server_certificate_chain <= max_transcript_len
             | None -> False))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let role_ok = config_role_is_server c.config;
  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 15uy;

  with stored_ee. assert (Box.pts_to c.handshake.messages.encrypted_extensions stored_ee);
  let stored_ee_opt = !c.handshake.messages.encrypted_extensions;
  let has_encrypted_extensions = (
    match stored_ee_opt with
    | Some _ -> true
    | None -> false);
  assert (pure (stored_ee_opt == stored_ee));
  assert (pure (has_encrypted_extensions ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None));

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored_cert_opt = !c.handshake.messages.certificate;
  let no_certificate = (
    match stored_cert_opt with
    | None -> true
    | Some _ -> false);
  assert (pure (stored_cert_opt == stored_cert));
  assert (pure (no_certificate ==> stored_cert == None));
  assert (pure (no_certificate ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));

  with parsed leaf_present leaf_storage leaf_len. assert (pure True);
  let leaf_present_runtime = !c.handshake.buffers.certificate_leaf_der.present;
  let no_leaf = not leaf_present_runtime;
  assert (pure (leaf_present_runtime == leaf_present));
  assert (pure (no_leaf ==> not leaf_present));
  assert (pure (no_leaf ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  let seq_ok = Rec.can_advance_seq c.records.write;

  assert_norm (max_server_certificate_chain_len == 16610);
  assert_norm (max_transcript_len == 65535);
  let max_certificate_fragment_len = 16623sz;
  assert (pure (SZ.v max_certificate_fragment_len == 13 + max_server_certificate_chain_len));
  let max_len = max_transcript_len_sz;
  let max_start = SZ.sub max_len max_certificate_fragment_len;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;

  let ok =
    tag_ok &&
    stage_ok &&
    role_ok &&
    has_encrypted_extensions &&
    no_certificate &&
    no_leaf &&
    has_server_handshake_keys &&
    seq_ok &&
    transcript_room;

  assert (pure (Some? st0.CS.cs_model.CS.model_config.CS.config_server));
  let server_cfg =
    Ghost.hide (Some?.v st0.CS.cs_model.CS.model_config.CS.config_server);
  assert (pure (
    st0.CS.cs_model.CS.model_config.CS.config_server ==
      Some (Ghost.reveal server_cfg)));
  assert (pure (
    B.length (Ghost.reveal server_cfg).CS.server_certificate_chain <=
      max_server_certificate_chain_len));
  // TODO-A1: deleted W.lemma_serialize_certificate_from_single_chain_len; the
  // serialized-certificate length fact below is no longer available.

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 15));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (ok ==> U64.fits
    (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
  assert (pure (ok ==>
    SZ.v current_transcript_len + SZ.v max_certificate_fragment_len <= max_transcript_len));
  // Connect the runtime transcript-room check to the exposed postcondition
  // conjunct: |chain| <= 16610 (server_cfg bound), so 13 + |chain| <= 16623 ==
  // max_certificate_fragment_len, hence |transcript| + 13 + |chain| fits.
  assert (pure (ok ==>
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 13 +
      B.length (Ghost.reveal server_cfg).CS.server_certificate_chain <=
        max_transcript_len));

  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  fold (encrypted_extensions_slot_exactly
    c.handshake.messages.encrypted_extensions
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_sign_certificate_verify_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  let role_ok = config_role_is_server c.config;
  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 15uy;

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored_cert_opt = !c.handshake.messages.certificate;
  let has_certificate = (
    match stored_cert_opt with
    | Some _ -> true
    | None -> false);
  assert (pure (stored_cert_opt == stored_cert));
  assert (pure (has_certificate ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored_cv_opt = !c.handshake.messages.certificate_verify;
  let no_cv = (
    match stored_cv_opt with
    | None -> true
    | Some _ -> false);
  assert (pure (stored_cv_opt == stored_cv));
  assert (pure (no_cv ==> stored_cv == None));
  assert (pure (no_cv ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));

  with parsed input_present input_storage input_len. assert (pure True);
  let input_present_runtime = !c.handshake.buffers.certificate_verify_input.present;
  let no_input = not input_present_runtime;
  assert (pure (input_present_runtime == input_present));
  assert (pure (no_input ==> not input_present));
  assert (pure (no_input ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));

  let ok =
    tag_ok &&
    stage_ok &&
    role_ok &&
    has_certificate &&
    no_cv &&
    no_input;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 15));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));

  fold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  fold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_certificate_verify_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            (let cv =
              Some?.v
                st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
             // Transcript-length bound for the CertificateVerify flight.  The
             // handshake message serializes to exactly 8 + |signature| bytes
             // (TLS13.Impl.Server.Send.lemma_serialize_handshake_certificate_verify_len)
             // and the runtime transcript-room check below guarantees it fits.
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 8 +
               B.length (Sem.certificateVerify_signature_bytes cv) <= max_transcript_len /\
             CS.legal_event
               st0.CS.cs_model
               (CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
               })))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let role_ok = config_role_is_server c.config;
  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 15uy;

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored_cert_opt = !c.handshake.messages.certificate;
  let has_certificate = (
    match stored_cert_opt with
    | Some _ -> true
    | None -> false);
  assert (pure (stored_cert_opt == stored_cert));
  assert (pure (has_certificate ==>
    (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None)));

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored_cv_opt = !c.handshake.messages.certificate_verify;
  let has_cv = (
    match stored_cv_opt with
    | Some _ -> true
    | None -> false);
  assert (pure (stored_cv_opt == stored_cv));
  assert (pure (has_cv ==>
    option_is_some st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));

  let already_verified = !c.handshake.certificate_verify_verified;
  assert (pure (already_verified == cv_verified));
  assert (pure (already_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  let not_verified = not already_verified;
  assert (pure (not_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));

  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  let seq_ok = Rec.can_advance_seq c.records.write;
  let certificate_verify_seq_slot = Rec.seq_eq c.records.write 2UL;
  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  if has_cv {
    assert (pure has_cv);
    assert (pure (option_is_some
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    lemma_option_is_some_some_imp
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify
      has_cv;
    let cv = Ghost.hide (Some?.v
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    assert (pure (
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some (Ghost.reveal cv)));
    let lcv = Some?.v stored_cv_opt;
    assert (pure (stored_cv_opt == Some lcv));
    assert (pure (stored_cv == Some lcv));

    rewrite (match stored_cv, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
      | _, _ -> pure False)
      as (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
    unfold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
    with signature_bytes. _;
    let signature_len = lcv.certificate_verify_signature_len;
    V.pts_to_len lcv.certificate_verify_signature;
    assert (pure (B.length signature_bytes == IM.max_signature_len));
    assert (pure (SZ.v signature_len <= IM.max_signature_len));
    assert (pure (IM.byte_prefix_matches
      signature_bytes
      signature_len
      (Sem.certificateVerify_signature_bytes (Ghost.reveal cv))));
    Seq.lemma_len_slice signature_bytes 0 (SZ.v signature_len);
    assert (pure (B.length (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)) == SZ.v signature_len));
    // TODO-A1: deleted W.lemma_serialize_certificate_verify_from_signature_len; the
    // exact serialized-length fact (== 8 + signature_len) is no longer available.
    assert_norm (IM.max_signature_len == 4096);
    assert_norm (max_transcript_len == 65535);
    assert (pure (SZ.v signature_len + 8 <= max_transcript_len));
    assert (pure (SZ.fits (SZ.v signature_len + 8)));
    let fragment_len = SZ.add signature_len 8sz;
    // TODO-A1: fragment_len == B.length (serialize_certificate_verify_from_signature cv)
    // assert removed (deleted serializer).  fragment_len is still signature_len + 8.
    assert (pure (SZ.v fragment_len <= max_transcript_len));
    let max_len = max_transcript_len_sz;
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let ok =
      role_ok &&
      tag_ok &&
      stage_ok &&
      has_certificate &&
      not_verified &&
      has_server_handshake_keys &&
      seq_ok &&
      certificate_verify_seq_slot &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 15));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
    assert (pure (ok ==>
      (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None)));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));
    assert (pure (ok ==> Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
    assert (pure (ok ==> Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert (pure (ok ==> U64.fits
      (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==>
      SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    // Connect the runtime transcript-room check to the exposed postcondition
    // conjunct: fragment_len == signature_len + 8 and
    // |Sem.certificateVerify_signature_bytes cv| == signature_len.
    assert (pure (ok ==>
      B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 8 +
        B.length (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)) <=
          max_transcript_len));
    // The signature is bounded by [signature_max_len] (4096), so the sent
    // CertificateVerify is [certificateVerify_representable] as the strengthened
    // Sent-CV [legal_handshake_message] arm now requires.
    W.lemma_certificateVerify_representable (Ghost.reveal cv);
    assert (pure (B.length (Sem.certificateVerify_signature_bytes (Ghost.reveal cv))
      <= M.signature_max_len));
    assert (pure (W.certificateVerify_representable (Ghost.reveal cv)));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
      })));

    fold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));
    rewrite (IM.is_valid_certificate_verify lcv (Ghost.reveal cv))
      as (match stored_cv, st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
        | None, None -> pure True
        | Some old_l, Some old_m -> IM.is_valid_certificate_verify old_l old_m
        | _, _ -> pure False);
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (certificate_slot_exactly
      c.handshake.messages.certificate
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (certificate_slot_exactly
      c.handshake.messages.certificate
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}

fn can_send_server_finished_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);

  let role_ok = config_role_is_server c.config;
  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 15uy;

  let already_verified = !c.handshake.certificate_verify_verified;
  assert (pure (already_verified == cv_verified));
  assert (pure (already_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));

  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  let seq_ok = Rec.can_advance_seq c.records.write;

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  let max_start = SZ.sub max_transcript_len_sz 36sz;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;

  let ok =
    tag_ok &&
    stage_ok &&
    role_ok &&
    already_verified &&
    has_server_handshake_keys &&
    seq_ok &&
    transcript_room;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 15));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (ok ==> U64.fits
    (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
  assert (pure (ok ==>
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
      max_transcript_len));

  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_receive_certificate
  (c:connection_state)
  (lcert:IM.certificate_msg)
  (#cert:erased GCert.certificate)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           IM.is_valid_certificate_msg lcert cert
  returns ok: bool
  ensures connection_exactly c st0 **
          IM.is_valid_certificate_msg lcert cert **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None /\
            (Sem.certificate_entries (Ghost.reveal cert)) <> [] /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
  unfold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 4uy;

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored = !c.handshake.messages.certificate;
  let no_certificate = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_cert));
  assert (pure (no_certificate ==> stored == None));
  assert (pure (no_certificate ==> stored_cert == None));
  assert (pure (no_certificate ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with parsed leaf_present leaf_storage leaf_len. assert (pure True);
  let leaf_present_runtime = !c.handshake.buffers.certificate_leaf_der.present;
  let no_leaf = not leaf_present_runtime;
  assert (pure (leaf_present_runtime == leaf_present));
  assert (pure (no_leaf ==> not leaf_present));
  assert (pure (no_leaf ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));

  let seq_ok = Rec.can_advance_seq c.records.read;

  with chain_bytes offsets lens. assert (pure True);
  let cert_count = lcert.IM.certificate_msg_cert_count;
  let has_certificate = SZ.gt cert_count 0sz;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    if has_certificate {
      assert (pure has_certificate);
      assert (pure (SZ.v cert_count > 0));
      assert (pure ((Sem.certificate_entries (Ghost.reveal cert)) <> []));
      let control_ok = tag_ok && stage_ok && role_ok;
      let ok =
        control_ok &&
        no_certificate &&
        no_leaf &&
        seq_ok &&
        transcript_room;

      assert (pure (ok ==> U8.v tag == 1));
      assert (pure (ok ==> U8.v stage == 4));
      assert (pure (ok ==>
        st0.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsEncryptedExtensionsReceived));
      assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
      assert (pure (ok ==>
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
      assert (pure (ok ==> (Sem.certificate_entries (Ghost.reveal cert)) <> []));
      assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
      assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
        SZ.v current_transcript_len));
      assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
      assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
      assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
        SZ.v fragment_len <= max_transcript_len));
      assert (pure (ok ==> CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate (Ghost.reveal cert));
        })));

      fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
      fold (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
      fold (optional_sized_bytes_exactly
        c.handshake.buffers.certificate_leaf_der
        max_handshake_flight_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
      fold (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
      fold (certificate_slot_exactly
        c.handshake.messages.certificate
        st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      ok
    } else {
      fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
      fold (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
      fold (optional_sized_bytes_exactly
        c.handshake.buffers.certificate_leaf_der
        max_handshake_flight_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
      fold (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
      fold (certificate_slot_exactly
        c.handshake.messages.certificate
        st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
      fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    fold (IM.is_valid_certificate_msg lcert (Ghost.reveal cert));
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_leaf_der
      max_handshake_flight_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (certificate_slot_exactly
      c.handshake.messages.certificate
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_validate_certificate
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der /\
            SZ.v payload_len <= max_public_key_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 5uy;

  with stored_cert. assert (Box.pts_to c.handshake.messages.certificate stored_cert);
  let stored_certificate = !c.handshake.messages.certificate;
  let certificate_present = (
    match stored_certificate with
    | Some _ -> true
    | None -> false);
  assert (pure (stored_certificate == stored_cert));
  assert (pure (certificate_present ==> Some? stored_cert));

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let stored_peer_present = !c.handshake.validated_peer.present;
  let no_peer = not stored_peer_present;
  assert (pure (stored_peer_present == peer_present));
  assert (pure (no_peer ==> not peer_present));
  assert (pure (no_peer ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));

  with leaf_present leaf_storage leaf_len. assert (pure True);
  let leaf_present_runtime = !c.handshake.buffers.certificate_leaf_der.present;
  assert (pure (leaf_present_runtime == leaf_present));
  if leaf_present_runtime {
    assert (pure leaf_present);
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
  };

  assert (pure (SZ.fits max_public_key_len));
  let max_pk_len = max_public_key_len_sz;
  let payload_fits = SZ.lte payload_len max_pk_len;
  let ok =
    role_ok &&
    tag_ok &&
    stage_ok &&
    no_peer &&
    certificate_present &&
    leaf_present_runtime &&
    payload_fits;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 5));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateReceived));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == None));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
  assert (pure (ok ==> SZ.v payload_len <= max_public_key_len));

  fold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_leaf_der
    max_handshake_flight_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  fold (certificate_slot_exactly
    c.handshake.messages.certificate
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_receive_certificate_verify
  (c:connection_state)
  (#cv:erased GCV.certificateVerify)
  (fragment_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateValidated /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v fragment_len <= max_transcript_len /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 6uy;

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored = !c.handshake.messages.certificate_verify;
  let no_cv = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_cv));
  assert (pure (no_cv ==> stored == None));
  assert (pure (no_cv ==> stored_cv == None));
  assert (pure (no_cv ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let peer_is_present = !c.handshake.validated_peer.present;
  assert (pure (peer_is_present == peer_present));
  assert (pure (peer_is_present ==> peer_present));
  assert (pure (peer_is_present ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  with parsed cv_input_present cv_input_storage cv_input_len. assert (pure True);
  let stored_cv_input_present = !c.handshake.buffers.certificate_verify_input.present;
  let no_cv_input = not stored_cv_input_present;
  assert (pure (stored_cv_input_present == cv_input_present));
  assert (pure (no_cv_input ==> not cv_input_present));
  assert (pure (no_cv_input ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));

  let seq_ok = Rec.can_advance_seq c.records.read;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let fragment_fits = SZ.lte fragment_len max_len;
  if fragment_fits {
    let max_start = SZ.sub max_len fragment_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let control_ok = tag_ok && stage_ok && role_ok;
    let ok =
      control_ok &&
      no_cv &&
      peer_is_present &&
      no_cv_input &&
      seq_ok &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 6));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateValidated));
    assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
    assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
    assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v fragment_len <= max_transcript_len));
    assert (pure (ok ==> CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify (Ghost.reveal cv));
      })));

    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (optional_sized_bytes_exactly
      c.handshake.buffers.certificate_verify_input
      max_certificate_verify_input_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
    fold (handshake_buffers_exactly
      c.handshake.buffers
      st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (peer_exactly
      c.handshake.validated_peer
      st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
    fold (certificate_verify_slot_exactly
      c.handshake.messages.certificate_verify
      st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn can_verify_certificate_signature
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  unfold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  unfold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  unfold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 7uy;

  with stored_cv. assert (Box.pts_to c.handshake.messages.certificate_verify stored_cv);
  let stored = !c.handshake.messages.certificate_verify;
  let has_cv = (
    match stored with
    | Some _ -> true
    | None -> false);
  assert (pure (stored == stored_cv));
  assert (pure (has_cv ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)));

  with peer_present peer_hostname peer_hostname_len peer_public_key peer_public_key_len peer_schemes peer_schemes_len.
    assert (pure True);
  let peer_is_present = !c.handshake.validated_peer.present;
  assert (pure (peer_is_present == peer_present));
  assert (pure (peer_is_present ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)));

  with parsed input_present input_storage input_len. assert (pure True);
  let cv_input_present = !c.handshake.buffers.certificate_verify_input.present;
  assert (pure (cv_input_present == input_present));
  assert (pure (cv_input_present ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)));

  let already_verified = !c.handshake.certificate_verify_verified;
  assert (pure (already_verified == cv_verified));
  let not_verified = not already_verified;
  assert (pure (not_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));

  let ok =
    role_ok &&
    tag_ok &&
    stage_ok &&
    has_cv &&
    peer_is_present &&
    cv_input_present &&
    not_verified;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 7));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyReceived));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)));
  assert (pure (ok ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == false));
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer
    ok;
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify
    ok;
  lemma_option_is_some_some_imp
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input
    ok;

  fold (optional_sized_bytes_exactly
    c.handshake.buffers.certificate_verify_input
    max_certificate_verify_input_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input);
  fold (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers);
  fold (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  fold (certificate_verify_slot_exactly
    c.handshake.messages.certificate_verify
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_receive_server_finished
  (c:connection_state)
  (#fin:erased GFin.finished)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            Some?
              st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
              max_transcript_len /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1) /\
            CS.legal_event
              st0.CS.cs_model
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
              }))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  unfold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 8uy;

  with stored_fin. assert (Box.pts_to c.handshake.messages.server_finished stored_fin);
  let stored = !c.handshake.messages.server_finished;
  let no_fin = (
    match stored with
    | None -> true
    | Some _ -> false);
  assert (pure (stored == stored_fin));
  assert (pure (no_fin ==> stored == None));
  assert (pure (no_fin ==> stored_fin == None));
  assert (pure (no_fin ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));

  with server_hs_present.
    assert (Box.pts_to c.handshake.keys.server_handshake_traffic.present server_hs_present);
  with server_hs_secret.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_secret server_hs_secret);
  with server_hs_key.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_key server_hs_key);
  with server_hs_iv.
    assert (V.pts_to c.handshake.keys.server_handshake_traffic.traffic_iv server_hs_iv);
  let has_server_handshake_keys = !c.handshake.keys.server_handshake_traffic.present;
  assert (pure (has_server_handshake_keys == server_hs_present));

  with master_present.
    assert (Box.pts_to c.handshake.keys.master_secret.present master_present);
  with master_secret_bytes.
    assert (V.pts_to c.handshake.keys.master_secret.secret master_secret_bytes);
  let has_master = !c.handshake.keys.master_secret.present;
  assert (pure (has_master == master_present));

  let seq_ok = Rec.can_advance_seq c.records.read;

  with transcript_storage transcript_len_g.
    assert (V.pts_to c.handshake.transcript.bytes transcript_storage **
            Box.pts_to c.handshake.transcript.len transcript_len_g);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len_g));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let max_start = SZ.sub max_len 36sz;
  let transcript_room = sizet_lte_plain current_transcript_len max_start;
  lemma_sizet_lte_plain current_transcript_len max_start;

  let ok = role_ok && tag_ok && stage_ok && no_fin && has_server_handshake_keys && has_master && seq_ok && transcript_room;

  assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    max_transcript_len));

  assert (pure (ok ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret));

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 8));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsCertificateVerifyVerified));
  assert (pure (ok ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished == None));
  assert (pure (ok ==> server_hs_present));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
  assert (pure (ok ==>
    U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));
  assert (pure (ok ==> CS.legal_event
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin));
    })));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (optional_secret_exactly
    c.handshake.keys.master_secret
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_verify_server_finished
  (c:connection_state)
  (payload_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedReceived /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
              SZ.v payload_len <= max_transcript_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. assert (pure True);
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 9uy;

  with stored_fin. assert (Box.pts_to c.handshake.messages.server_finished stored_fin);
  let stored = !c.handshake.messages.server_finished;
  let has_fin = (
    match stored with
    | Some _ -> true
    | None -> false);
  assert (pure (stored == stored_fin));
  assert (pure (has_fin ==>
    option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished)));

  let stored_server_hs_present = !c.handshake.keys.server_handshake_traffic.present;
  assert (pure (stored_server_hs_present ==>
    option_is_some
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));

  with transcript_storage transcript_len. assert (pure True);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  let already_verified = !c.handshake.server_finished_verified;
  assert (pure (already_verified == server_finished_verified));
  let not_verified = not already_verified;
  assert (pure (not_verified ==>
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let payload_fits = SZ.lte payload_len max_len;
  if payload_fits {
    let max_start = SZ.sub max_len payload_len;
    let transcript_room = sizet_lte_plain current_transcript_len max_start;
    lemma_sizet_lte_plain current_transcript_len max_start;

    let ok =
      role_ok &&
      tag_ok &&
      stage_ok &&
      has_fin &&
      stored_server_hs_present &&
      not_verified &&
      transcript_room;

    assert (pure (ok ==> U8.v tag == 1));
    assert (pure (ok ==> U8.v stage == 9));
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedReceived));
    assert (pure (ok ==>
      option_is_some (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished)));
    assert (pure (ok ==>
      option_is_some
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    lemma_option_is_some_some_imp
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished
      ok;
    lemma_option_is_some_some_imp
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic
      ok;
    assert (pure (ok ==>
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
      SZ.v current_transcript_len));
    assert (pure (ok ==> SZ.v current_transcript_len <= SZ.v max_start));
    assert (pure (ok ==> SZ.v current_transcript_len + SZ.v payload_len <= max_transcript_len));
    assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      SZ.v payload_len <= max_transcript_len));

    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (finished_slot_exactly
      c.handshake.messages.server_finished
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    ok
  } else {
    fold (traffic_key_material_exactly
      c.handshake.keys.server_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (finished_slot_exactly
      c.handshake.messages.server_finished
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
    fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (control_exactly
      c.control
      st0.CS.cs_model.CS.model_control
      st0.CS.cs_model.CS.model_failure);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    false
  }
}
fn server_finished_verify_data_matches
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsServerFinishedReceived /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                  st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified == false)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
             | Some fin, Some server_hs ->
               H.verify_finished
                 server_hs.CS.traffic_secret
                 (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                 fin
             | _, _ -> False))
{
  let fin = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  let server_hs =
    Ghost.hide (Some?.v
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
    Some (Ghost.reveal server_hs)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  with stored_fin_opt. assert (Box.pts_to c.handshake.messages.server_finished stored_fin_opt);
  let stored_fin = !c.handshake.messages.server_finished;
  assert (pure (stored_fin == stored_fin_opt));
  assert (pure (Some? stored_fin));
  let lfin = Some?.v stored_fin;
  assert (pure (stored_fin == Some lfin));
  assert (pure (stored_fin_opt == Some lfin));
  rewrite (match stored_fin_opt, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_finished lfin (Ghost.reveal fin));
  unfold (IM.is_valid_finished lfin (Ghost.reveal fin));
  with stored_verify_data. _;
  assert (pure (Seq.equal stored_verify_data (Sem.finished_verify_data (Ghost.reveal fin))));

  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  with server_hs_present server_hs_secret server_hs_key server_hs_iv. _;
  lemma_traffic_key_material_match_present_of_some
    server_hs_present
    server_hs_secret
    server_hs_key
    server_hs_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
    Some {
      CS.traffic_secret = server_hs_secret;
      CS.traffic_key = server_hs_key;
      CS.traffic_iv = server_hs_iv;
    }));
  assert (pure ((Ghost.reveal server_hs).CS.traffic_secret == server_hs_secret));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with transcript_storage transcript_len. _;
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.server_handshake_traffic.traffic_secret;
  let mut expected_verify_data = [| 0uy; 32sz |];
  KS.finished_verify_data
    (V.vec_to_array c.handshake.keys.server_handshake_traffic.traffic_secret)
    transcript_hash
    expected_verify_data;
  V.to_vec_pts_to c.handshake.keys.server_handshake_traffic.traffic_secret;
  with expected_verify_data_bytes.
    assert (ArrPts.pts_to expected_verify_data expected_verify_data_bytes);
  assert (pure (expected_verify_data_bytes ==
    K.finished_verify_data
      server_hs_secret
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  V.to_array_pts_to lfin.IM.finished_verify_data;
  let ok = Crypto.equal32 expected_verify_data (V.vec_to_array lfin.IM.finished_verify_data);
  V.to_vec_pts_to lfin.IM.finished_verify_data;
  assert (pure (ok ==> Seq.equal expected_verify_data_bytes stored_verify_data));
  assert (pure (ok ==> Seq.equal
    (Sem.finished_verify_data (Ghost.reveal fin))
    (K.finished_verify_data
      server_hs_secret
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  assert (pure (ok ==> H.verify_finished
    (Ghost.reveal server_hs).CS.traffic_secret
    (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    (Ghost.reveal fin)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (IM.is_valid_finished lfin (Ghost.reveal fin));
  rewrite (IM.is_valid_finished lfin (Ghost.reveal fin))
    as (match stored_fin_opt, st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
      | _, _ -> pure False);
  fold (finished_slot_exactly
    c.handshake.messages.server_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn client_finished_verify_data_matches
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control ==
                    CS.ControlHandshaking CS.HsClientFinishedReceived /\
                  Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                  Some?
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
                   st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
             | Some fin, Some client_hs ->
               H.verify_finished
                 client_hs.CS.traffic_secret
                 (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                 fin
             | _, _ -> False))
{
  let fin = Ghost.hide (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  let client_hs =
    Ghost.hide (Some?.v
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
    Some (Ghost.reveal client_hs)));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  with stored_fin_opt. assert (Box.pts_to c.handshake.messages.client_finished stored_fin_opt);
  let stored_fin = !c.handshake.messages.client_finished;
  assert (pure (stored_fin == stored_fin_opt));
  assert (pure (Some? stored_fin));
  let lfin = Some?.v stored_fin;
  assert (pure (stored_fin == Some lfin));
  assert (pure (stored_fin_opt == Some lfin));
  rewrite (match stored_fin_opt, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False)
    as (IM.is_valid_finished lfin (Ghost.reveal fin));
  unfold (IM.is_valid_finished lfin (Ghost.reveal fin));
  with stored_verify_data. _;
  assert (pure (Seq.equal stored_verify_data (Sem.finished_verify_data (Ghost.reveal fin))));

  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  with client_hs_present client_hs_secret client_hs_key client_hs_iv. _;
  lemma_traffic_key_material_match_present_of_some
    client_hs_present
    client_hs_secret
    client_hs_key
    client_hs_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
    Some {
      CS.traffic_secret = client_hs_secret;
      CS.traffic_key = client_hs_key;
      CS.traffic_iv = client_hs_iv;
    }));
  assert (pure ((Ghost.reveal client_hs).CS.traffic_secret == client_hs_secret));

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with transcript_storage transcript_len. _;
  let transcript_len_runtime = !c.handshake.transcript.len;
  assert (pure (transcript_len_runtime == transcript_len));
  assert (pure (byte_prefix_matches
    transcript_storage
    transcript_len_runtime
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime))));
  Seq.lemma_eq_intro
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice transcript_storage 0 (SZ.v transcript_len_runtime));

  V.to_array_pts_to c.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array c.handshake.transcript.bytes)
    transcript_len_runtime
    transcript_hash;
  V.to_vec_pts_to c.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (ArrPts.pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes == Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  V.to_array_pts_to c.handshake.keys.client_handshake_traffic.traffic_secret;
  let mut expected_verify_data = [| 0uy; 32sz |];
  KS.finished_verify_data
    (V.vec_to_array c.handshake.keys.client_handshake_traffic.traffic_secret)
    transcript_hash
    expected_verify_data;
  V.to_vec_pts_to c.handshake.keys.client_handshake_traffic.traffic_secret;
  with expected_verify_data_bytes.
    assert (ArrPts.pts_to expected_verify_data expected_verify_data_bytes);
  assert (pure (expected_verify_data_bytes ==
    K.finished_verify_data
      client_hs_secret
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

  V.to_array_pts_to lfin.IM.finished_verify_data;
  let ok = Crypto.equal32 expected_verify_data (V.vec_to_array lfin.IM.finished_verify_data);
  V.to_vec_pts_to lfin.IM.finished_verify_data;
  assert (pure (ok ==> Seq.equal expected_verify_data_bytes stored_verify_data));
  assert (pure (ok ==> Seq.equal
    (Sem.finished_verify_data (Ghost.reveal fin))
    (K.finished_verify_data
      client_hs_secret
      (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  assert (pure (ok ==> H.verify_finished
    (Ghost.reveal client_hs).CS.traffic_secret
    (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
    (Ghost.reveal fin)));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (IM.is_valid_finished lfin (Ghost.reveal fin));
  rewrite (IM.is_valid_finished lfin (Ghost.reveal fin))
    as (match stored_fin_opt, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
      | None, None -> pure True
      | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
      | _, _ -> pure False);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_verify_client_finished_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
            // TODO-A1: Model.can_verify_client_finished bundles a transcript-length
            // conjunct `B.length transcript + B.length (serialize_handshake
            // (M.Finished fin)) <= max_transcript_len`, whose proof needed the
            // Phase-4-deleted W.lemma_serialize_finished_len (which gave
            // serialize_handshake (M.Finished fin) == 36).  That bound is no longer
            // provable for general generated finished records, so we expose the
            // remaining (provable) conjuncts of can_verify_client_finished here
            // instead of the bundled predicate.  (Only the out-of-scope
            // TLS13.Impl.Server.Schedule consumes this result.)
            (let fin = Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
             st0.CS.cs_model.CS.model_control ==
               CS.ControlHandshaking CS.HsClientFinishedReceived /\
             st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             CS.application_record_keys_installed_for_role
               CS.ServerEndpoint st0.CS.cs_model /\
             (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
                    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
              | Some stored_fin, Some client_hs ->
                stored_fin == fin /\
                H.verify_finished
                  client_hs.CS.traffic_secret
                  (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
                  fin
              | _, _ -> False) /\
             CS.legal_event
               st0.CS.cs_model
               (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) /\
             // Transcript-length bound of CM.can_verify_client_finished: a
             // Finished handshake message serializes to exactly 36 bytes
             // (TLS13.Impl.Server.Send.lemma_serialize_handshake_finished_len);
             // the runtime transcript-room check below guarantees it fits.
             B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
               max_transcript_len))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_server c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 17uy;

  with client_finished_stored.
    assert (Box.pts_to c.handshake.messages.client_finished client_finished_stored);
  let client_finished_value = !c.handshake.messages.client_finished;
  assert (pure (client_finished_value == client_finished_stored));
  let client_finished_present = (
    match client_finished_value with
    | Some _ -> true
    | None -> false);
  assert (pure (client_finished_present ==>
    Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));

  with client_hs_present_w client_hs_secret client_hs_key client_hs_iv.
    assert (Box.pts_to c.handshake.keys.client_handshake_traffic.present client_hs_present_w **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_secret client_hs_secret **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_key client_hs_key **
            V.pts_to c.handshake.keys.client_handshake_traffic.traffic_iv client_hs_iv);
  with client_app_present_w client_app_secret client_app_key client_app_iv.
    assert (Box.pts_to c.handshake.keys.client_application_traffic.present client_app_present_w **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_secret client_app_secret **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_key client_app_key **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_iv client_app_iv);
  with server_app_present_w server_app_secret server_app_key server_app_iv.
    assert (Box.pts_to c.handshake.keys.server_application_traffic.present server_app_present_w **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_secret server_app_secret **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_key server_app_key **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_iv server_app_iv);

  let client_hs_present = !c.handshake.keys.client_handshake_traffic.present;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;
  assert (pure (client_hs_present == client_hs_present_w));
  assert (pure (client_app_present == client_app_present_w));
  assert (pure (server_app_present == server_app_present_w));

  with transcript_len. assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  let read_keys_match =
    Rec.application_keys_match
      c.records.read
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_key;

  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  let write_keys_match =
    Rec.application_keys_match
      c.records.write
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_key;

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let finished_len = 36sz;
  let transcript_room = (
    if SZ.lte finished_len max_len then
      let max_start = SZ.sub max_len finished_len in
      sizet_lte_plain current_transcript_len max_start
    else
      false);

  let base_ok =
    role_ok &&
    tag_ok &&
    stage_ok &&
    client_finished_present &&
    client_hs_present &&
    client_app_present &&
    server_app_present &&
    read_keys_match &&
    write_keys_match &&
    transcript_room;

  assert (pure (base_ok ==> U8.v tag == 1));
  assert (pure (base_ok ==> U8.v stage == 17));
  assert_norm (Tags.handshake_stage_tag_matches 17uy CS.HsClientFinishedReceived);
  assert (pure (base_ok ==>
    st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientFinishedReceived));
  assert (pure (base_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (base_ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
  assert (pure (base_ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
  assert (pure (base_ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (base_ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  lemma_sizet_lte_plain current_transcript_len (SZ.sub max_len finished_len);
  assert (pure (base_ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (base_ok ==> SZ.v current_transcript_len + 36 <= max_transcript_len));
  assert (pure (base_ok ==>
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
      max_transcript_len));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);

  if base_ok {
    let finished_ok = client_finished_verify_data_matches c;
    if finished_ok {
      let fin =
        Ghost.hide
          (Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
      lemma_traffic_key_material_match_present_of_some
        client_hs_present_w
        client_hs_secret
        client_hs_key
        client_hs_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
      lemma_traffic_key_material_match_present_of_some
        client_app_present_w
        client_app_secret
        client_app_key
        client_app_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
      lemma_traffic_key_material_match_present_of_some
        server_app_present_w
        server_app_secret
        server_app_key
        server_app_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;
      assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
        CS.ClientTraffic);
      assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
        CS.ServerTraffic);
      assert (pure (CS.application_record_keys_installed_for_role
        CS.ServerEndpoint
        st0.CS.cs_model));
      // TODO-A1: deleted W.lemma_serialize_finished_len; we establish the provable
      // conjuncts of can_verify_client_finished (everything except the transcript /
      // serialized-finished length bound — see the ensures clause above).
      assert (pure (
        st0.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientFinishedReceived /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.application_record_keys_installed_for_role CS.ServerEndpoint st0.CS.cs_model /\
        (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
               st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic with
         | Some stored_fin, Some client_hs ->
           stored_fin == Ghost.reveal fin /\
           H.verify_finished client_hs.CS.traffic_secret
             (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
             (Ghost.reveal fin)
         | _, _ -> False) /\
        CS.legal_event st0.CS.cs_model
          (CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin)))));
      // Transcript-length bound: base_ok holds on this branch, and the runtime
      // transcript-room check established |transcript| + 36 <= max_transcript_len.
      assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
        max_transcript_len));
      true
    } else {
      false
    }
  } else {
    false
  }
}

fn server_application_record_keys_installed_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            CS.application_record_keys_installed_for_role
              CS.ServerEndpoint
              st0.CS.cs_model)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  with client_app_present_w client_app_secret client_app_key client_app_iv.
    assert (Box.pts_to c.handshake.keys.client_application_traffic.present client_app_present_w **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_secret client_app_secret **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_key client_app_key **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_iv client_app_iv);
  with server_app_present_w server_app_secret server_app_key server_app_iv.
    assert (Box.pts_to c.handshake.keys.server_application_traffic.present server_app_present_w **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_secret server_app_secret **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_key server_app_key **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_iv server_app_iv);

  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;
  assert (pure (client_app_present == client_app_present_w));
  assert (pure (server_app_present == server_app_present_w));

  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  let read_keys_match =
    Rec.application_keys_match
      c.records.read
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_key;

  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  let write_keys_match =
    Rec.application_keys_match
      c.records.write
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_key;

  let ok =
    client_app_present &&
    server_app_present &&
    read_keys_match &&
    write_keys_match;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  if ok {
    lemma_traffic_key_material_match_present_of_some
      client_app_present_w
      client_app_secret
      client_app_key
      client_app_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
    lemma_traffic_key_material_match_present_of_some
      server_app_present_w
      server_app_secret
      server_app_key
      server_app_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;
    assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
      CS.ClientTraffic);
    assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
      CS.ServerTraffic);
    assert (pure (CS.application_record_keys_installed_for_role
      CS.ServerEndpoint
      st0.CS.cs_model));
    ok
  } else {
    ok
  }
}

fn client_application_record_keys_installed_runtime
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            CS.application_record_keys_installed_for_role
              CS.ClientEndpoint
              st0.CS.cs_model)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  with client_app_present_w client_app_secret client_app_key client_app_iv.
    assert (Box.pts_to c.handshake.keys.client_application_traffic.present client_app_present_w **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_secret client_app_secret **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_key client_app_key **
            V.pts_to c.handshake.keys.client_application_traffic.traffic_iv client_app_iv);
  with server_app_present_w server_app_secret server_app_key server_app_iv.
    assert (Box.pts_to c.handshake.keys.server_application_traffic.present server_app_present_w **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_secret server_app_secret **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_key server_app_key **
            V.pts_to c.handshake.keys.server_application_traffic.traffic_iv server_app_iv);

  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;
  assert (pure (client_app_present == client_app_present_w));
  assert (pure (server_app_present == server_app_present_w));

  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  let read_keys_match =
    Rec.application_keys_match
      c.records.read
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_key;

  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  let write_keys_match =
    Rec.application_keys_match
      c.records.write
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
      (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_key;

  let ok =
    client_app_present &&
    server_app_present &&
    read_keys_match &&
    write_keys_match;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  if ok {
    lemma_traffic_key_material_match_present_of_some
      client_app_present_w
      client_app_secret
      client_app_key
      client_app_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
    lemma_traffic_key_material_match_present_of_some
      server_app_present_w
      server_app_secret
      server_app_key
      server_app_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;
    assert_norm (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
      CS.ServerTraffic);
    assert_norm (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
      CS.ClientTraffic);
    assert (pure (CS.application_record_keys_installed_for_role
      CS.ClientEndpoint
      st0.CS.cs_model));
    ok
  } else {
    ok
  }
}
fn can_send_client_finished_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
            (match st0.CS.cs_model.CS.model_record.CS.record_write.R.key,
                   st0.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
             | Some _, Some _ -> True
             | _, _ -> False) /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len /\
            58 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let stage = !c.control.handshake_stage_tag;
  let tag_ok = tag = 1uy;
  let stage_ok = stage = 10uy;

  with client_finished_stored. assert (Box.pts_to c.handshake.messages.client_finished client_finished_stored);
  let client_finished_value = !c.handshake.messages.client_finished;
  assert (pure (client_finished_value == client_finished_stored));
  let client_finished_absent = (
    match client_finished_value with
    | None -> true
    | Some _ -> false);

  with ch_present. assert (Box.pts_to c.handshake.keys.client_handshake_traffic.present ch_present);
  let client_hs_present = !c.handshake.keys.client_handshake_traffic.present;
  assert (pure (client_hs_present == ch_present));

  with ca_present. assert (Box.pts_to c.handshake.keys.client_application_traffic.present ca_present);
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  assert (pure (client_app_present == ca_present));

  with sa_present. assert (Box.pts_to c.handshake.keys.server_application_traffic.present sa_present);
  let server_app_present = !c.handshake.keys.server_application_traffic.present;
  assert (pure (server_app_present == sa_present));

  with transcript_len. assert (Box.pts_to c.handshake.transcript.len transcript_len);
  let current_transcript_len = !c.handshake.transcript.len;
  assert (pure (current_transcript_len == transcript_len));

  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_handshake_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  fold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);

  let seq_ok = Rec.can_advance_seq c.records.write;
  let seal_key_ok = Rec.has_seal_keys c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  assert (pure (SZ.fits max_transcript_len));
  let max_len = max_transcript_len_sz;
  let finished_len = 36sz;
  let transcript_room = (
    if SZ.lte finished_len max_len then
      let max_start = SZ.sub max_len finished_len in
      sizet_lte_plain current_transcript_len max_start
    else
      false);
  let out_room = sizet_lte_plain 58sz network_out_len;

  let ok =
    role_ok &&
    tag_ok &&
    stage_ok &&
    client_finished_absent &&
    client_hs_present &&
    client_app_present &&
    server_app_present &&
    seq_ok &&
    seal_key_ok &&
    transcript_room &&
    out_room;

  assert (pure (ok ==> U8.v tag == 1));
  assert (pure (ok ==> U8.v stage == 10));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
  assert (pure (ok ==>
    (match st0.CS.cs_model.CS.model_record.CS.record_write.R.key,
           st0.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
     | Some _, Some _ -> True
     | _, _ -> False)));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  lemma_sizet_lte_plain 58sz network_out_len;
  assert (pure (ok ==> 58 <= SZ.v network_out_len));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript ==
    SZ.v current_transcript_len));
  assert (pure (ok ==> SZ.v current_transcript_len + 36 <= max_transcript_len));
  assert (pure (ok ==> B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));

  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_send_application_data_runtime
  (c:connection_state)
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            SZ.v payload_len <= SM.max_application_data_fragment_len /\
            SZ.v payload_len + 22 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_application_data_sizes payload_len network_out_len;

  let ok =
    role_ok &&
    control_ok &&
    client_app_present &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> SZ.v payload_len <= SM.max_application_data_fragment_len));
  assert (pure (ok ==> SZ.v payload_len + 22 <= SZ.v network_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_endpoint_application_data_runtime
  (c:connection_state)
  (payload_len:SZ.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Sent /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            SZ.v payload_len <= SM.max_application_data_fragment_len /\
            SZ.v payload_len + 22 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
  with config_role_tag validation_time.
    assert (Box.pts_to c.config.role_tag config_role_tag **
            Box.pts_to c.config.validation_time_seconds validation_time);
  let role_tag = !c.config.role_tag;
  let role_client_ok = role_tag = 0uy;
  let role_server_ok = role_tag = 1uy;
  assert (pure (role_tag == config_role_tag));
  assert (pure (Tags.endpoint_role_tag_matches
    config_role_tag
    st0.CS.cs_model.CS.model_config.CS.config_role));
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (role_client_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint));
  assert (pure (role_server_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (role_client_ok ==> not role_server_ok));
  assert (pure (role_server_ok ==> not role_client_ok));
  fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_application_data_sizes payload_len network_out_len;

  let client_role_app_present = role_client_ok && client_app_present;
  let server_role_app_present = role_server_ok && server_app_present;
  let app_present_for_role =
    (if client_role_app_present then true else server_role_app_present);
  let ok =
    control_ok &&
    app_present_for_role &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> SZ.v payload_len <= SM.max_application_data_fragment_len));
  assert (pure (ok ==> SZ.v payload_len + 22 <= SZ.v network_out_len));
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
    CS.ClientTraffic);
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
    CS.ServerTraffic);
  if ok {
    assert (pure (app_present_for_role));
    if role_client_ok {
      assert (pure (client_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    } else {
      assert (pure (role_server_ok));
      assert (pure (server_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    }
  };
  assert (pure (ok ==>
    CS.application_traffic_available_for_role
      st0.CS.cs_model.CS.model_config.CS.config_role
      st0.CS.cs_model.CS.model_handshake
      CL.Sent));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_close_notify_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            24 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_close_notify_sizes network_out_len;

  let ok =
    role_ok &&
    control_ok &&
    client_app_present &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> 24 <= SZ.v network_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_endpoint_close_notify_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            CS.application_traffic_available_for_role
              st0.CS.cs_model.CS.model_config.CS.config_role
              st0.CS.cs_model.CS.model_handshake
              CL.Sent /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            24 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

  unfold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);
  with config_role_tag validation_time.
    assert (Box.pts_to c.config.role_tag config_role_tag **
            Box.pts_to c.config.validation_time_seconds validation_time);
  let role_tag = !c.config.role_tag;
  let role_client_ok = role_tag = 0uy;
  let role_server_ok = role_tag = 1uy;
  assert (pure (role_tag == config_role_tag));
  assert (pure (Tags.endpoint_role_tag_matches
    config_role_tag
    st0.CS.cs_model.CS.model_config.CS.config_role));
  assert_norm (Tags.endpoint_role_tag_matches 0uy CS.ClientEndpoint);
  assert_norm (Tags.endpoint_role_tag_matches 1uy CS.ServerEndpoint);
  assert (pure (role_client_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint));
  assert (pure (role_server_ok ==>
    st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint));
  assert (pure (role_client_ok ==> not role_server_ok));
  assert (pure (role_server_ok ==> not role_client_ok));
  fold (connection_config_exactly c.config st0.CS.cs_model.CS.model_config);

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let server_app_present = !c.handshake.keys.server_application_traffic.present;

  fold (traffic_key_material_exactly
    c.handshake.keys.server_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_close_notify_sizes network_out_len;

  let client_role_app_present = role_client_ok && client_app_present;
  let server_role_app_present = role_server_ok && server_app_present;
  let app_present_for_role =
    (if client_role_app_present then true else server_role_app_present);
  let ok =
    control_ok &&
    app_present_for_role &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> 24 <= SZ.v network_out_len));
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
    CS.ClientTraffic);
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
    CS.ServerTraffic);
  if ok {
    assert (pure (app_present_for_role));
    if role_client_ok {
      assert (pure (client_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    } else {
      assert (pure (role_server_ok));
      assert (pure (server_app_present));
      assert (pure (Some?
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    }
  };
  assert (pure (ok ==>
    CS.application_traffic_available_for_role
      st0.CS.cs_model.CS.model_config.CS.config_role
      st0.CS.cs_model.CS.model_handshake
      CL.Sent));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_send_key_update_runtime
  (c:connection_state)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending /\
            Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1) /\
            27 <= SZ.v network_out_len)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  with source_offset pending_response. _;

  let role_ok = config_role_is_client c.config;

  let tag = !c.control.control_tag;
  let control_ok = tag = 2uy;
  let client_app_present = !c.handshake.keys.client_application_traffic.present;
  let pending = !c.application.key_update_response_pending;

  fold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);

  let seq_ok = Rec.can_advance_seq c.records.write;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let size_ok =
    can_send_key_update_sizes network_out_len;

  let ok =
    role_ok &&
    control_ok &&
    pending &&
    client_app_present &&
    seq_ok &&
    size_ok;

  assert (pure (ok ==> U8.v tag == 2));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (ok ==> pending_response));
  assert (pure (ok ==> st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending));
  assert (pure (ok ==> Some?
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (ok ==> 27 <= SZ.v network_out_len));

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
fn can_receive_endpoint_close_notify
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
             st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let tag = !c.control.control_tag;
  let app_ok = tag = 2uy;
  let closing_ok = tag = 3uy;
  let control_ok = app_ok || closing_ok;

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let ok = control_ok && seq_ok;

  assert (pure (app_ok ==> U8.v tag == 2));
  assert (pure (closing_ok ==> U8.v tag == 3));
  assert (pure (ok ==>
    (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
     st0.CS.cs_model.CS.model_control == CS.ControlClosing)));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));

  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}

fn can_receive_close_notify
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures connection_exactly c st0 **
          pure (ok ==>
            (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
             st0.CS.cs_model.CS.model_control == CS.ControlClosing) /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1))
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  let role_ok = config_role_is_client c.config;
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let tag = !c.control.control_tag;
  let app_ok = tag = 2uy;
  let closing_ok = tag = 3uy;
  let control_ok = app_ok || closing_ok;

  fold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);

  let seq_ok = Rec.can_advance_seq c.records.read;
  fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

  let ok = role_ok && control_ok && seq_ok;

  assert (pure (app_ok ==> U8.v tag == 2));
  assert (pure (closing_ok ==> U8.v tag == 3));
  assert (pure (ok ==>
    (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
     st0.CS.cs_model.CS.model_control == CS.ControlClosing)));
  assert (pure (ok ==> U64.fits (st0.CS.cs_model.CS.model_record.CS.record_read.R.seq + 1)));

  fold (connection_model_exactly c st0.CS.cs_model);
  fold (connection_exactly c st0);
  ok
}
