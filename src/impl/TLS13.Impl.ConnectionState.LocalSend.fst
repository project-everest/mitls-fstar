module TLS13.Impl.ConnectionState.LocalSend

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Queries = TLS13.Impl.ConnectionState.Queries
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.StateMachine
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

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Queries
open TLS13.Impl.ConnectionState.Repr

fn write_close_notify_alert
  (alert:array U8.t)
  requires ArrPts.pts_to alert (Seq.create 2 0uy)
  ensures exists* alert_bytes.
            ArrPts.pts_to alert alert_bytes **
            pure (B.length alert_bytes == 2 /\
                  Seq.equal alert_bytes close_notify_alert_fragment)
{
  alert.(0sz) <- 2uy;
  alert.(1sz) <- 0uy;
  with alert_bytes.
    assert (ArrPts.pts_to alert alert_bytes);
  assert_norm (close_notify_alert_fragment == B.of_list [2uy; 0uy]);
  assert_norm (B.length close_notify_alert_fragment == 2);
  assert_norm (Seq.index close_notify_alert_fragment 0 == 2uy);
  assert_norm (Seq.index close_notify_alert_fragment 1 == 0uy);
  assert (pure (B.length alert_bytes == 2));
  assert (pure (Seq.index alert_bytes 0 == 2uy));
  assert (pure (Seq.index alert_bytes 1 == 0uy));
  Seq.lemma_eq_intro alert_bytes close_notify_alert_fragment;
  assert (pure (Seq.equal alert_bytes close_notify_alert_fragment))
}

fn write_key_update_response
  (handshake:array U8.t)
  requires ArrPts.pts_to handshake (Seq.create 5 0uy)
  ensures exists* handshake_bytes.
            ArrPts.pts_to handshake handshake_bytes **
            pure (B.length handshake_bytes == 5 /\
                  Seq.equal handshake_bytes key_update_response_fragment)
{
  handshake.(0sz) <- 24uy;
  handshake.(1sz) <- 0uy;
  handshake.(2sz) <- 0uy;
  handshake.(3sz) <- 1uy;
  handshake.(4sz) <- 0uy;
  with handshake_bytes.
    assert (ArrPts.pts_to handshake handshake_bytes);
  assert_norm (key_update_response_fragment == B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]);
  assert_norm (B.length key_update_response_fragment == 5);
  assert_norm (Seq.index key_update_response_fragment 0 == 24uy);
  assert_norm (Seq.index key_update_response_fragment 1 == 0uy);
  assert_norm (Seq.index key_update_response_fragment 2 == 0uy);
  assert_norm (Seq.index key_update_response_fragment 3 == 1uy);
  assert_norm (Seq.index key_update_response_fragment 4 == 0uy);
  assert (pure (B.length handshake_bytes == 5));
  assert (pure (Seq.index handshake_bytes 0 == 24uy));
  assert (pure (Seq.index handshake_bytes 1 == 0uy));
  assert (pure (Seq.index handshake_bytes 2 == 0uy));
  assert (pure (Seq.index handshake_bytes 3 == 1uy));
  assert (pure (Seq.index handshake_bytes 4 == 0uy));
  Seq.lemma_eq_intro handshake_bytes key_update_response_fragment;
  assert (pure (Seq.equal handshake_bytes key_update_response_fragment))
}

fn mark_sent_client_finished
  (c:connection_state)
  (handshake_bytes:array U8.t)
  (handshake_len:SZ.t)
  (lfin:IM.finished)
  (network_out:array U8.t)
  (written:SZ.t)
  (#fin:erased M.finished)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to handshake_bytes 'handshake_storage **
           IM.is_valid_finished lfin fin **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (can_send_client_finished st0 (Ghost.reveal fin) (Ghost.reveal raw_sent) /\
                 B.length 'handshake_storage == SZ.v handshake_len /\
                 SZ.v handshake_len == 36 /\
                 Seq.equal
                   (Ghost.reveal 'handshake_storage)
                   (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                 SZ.v written == 58 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)) **
          ArrPts.pts_to handshake_bytes 'handshake_storage **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_client_finished st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerFinishedVerified));
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
  assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));

  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
  unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;

  c.control.control_tag := 2uy;
  assert (pure (Tags.control_state_matches
    2uy
    10uy
    false
    0uy
    0uy
    CS.ControlApplicationData));
  fold (control_exactly
    c.control
    CS.ControlApplicationData
    st0.CS.cs_model.CS.model_failure);

  unfold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
  unfold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  with ca_present ca_secret ca_key ca_iv. _;
  lemma_traffic_key_material_match_present_of_some
    ca_present
    ca_secret
    ca_key
    ca_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
    Some {
      CS.traffic_secret = ca_secret;
      CS.traffic_key = ca_key;
      CS.traffic_iv = ca_iv;
    }));

  Rec.advance_seq c.records.write;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  Rec.install_application_keys_runtime
    c.records.write
    (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
    (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_iv);
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  fold (traffic_key_material_exactly
    c.handshake.keys.client_application_traffic
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
  fold (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read ==
    st0.CS.cs_model.CS.model_record.CS.record_read));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write ==
    R.install_keys
      (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
      R.Application
      ca_key
      ca_iv));
  rewrite (Rec.is_record_state
    c.records.read
    st0.CS.cs_model.CS.model_record.CS.record_read)
    as (Rec.is_record_state
      c.records.read
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read);
  rewrite (Rec.is_record_state
    c.records.write
    (R.install_keys
      (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
      R.Application
      ca_key
      ca_iv))
    as (Rec.is_record_state
      c.records.write
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write);
  fold (record_layer_exactly
    c.records
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);

  unfold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !c.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (SZ.v transcript_len + SZ.v handshake_len <= max_transcript_len));
  copy_array_to_transcript
    handshake_bytes
    c.handshake.transcript.bytes
    handshake_len
    transcript_len;
  with copied_transcript_storage.
    assert (V.pts_to c.handshake.transcript.bytes copied_transcript_storage);
  assert (pure (SZ.fits (SZ.v transcript_len + SZ.v handshake_len)));
  let new_transcript_len = SZ.add transcript_len handshake_len;
  c.handshake.transcript.len := new_transcript_len;
  assert (pure (Seq.equal
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (Ghost.reveal 'handshake_storage))
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin))))));
  fold (sized_bytes_exactly
    c.handshake.transcript
    max_transcript_len
    (B.append
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
      (W.serialize_handshake (M.Finished (Ghost.reveal fin)))));

  unfold (handshake_messages_exactly
    c.handshake.messages
    st0.CS.cs_model.CS.model_handshake);
  unfold (finished_slot_exactly
    c.handshake.messages.client_finished
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  with old_client_finished. _;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished == None));
  assert (pure (old_client_finished == None));
  drop_ (match old_client_finished, st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished with
    | None, None -> pure True
    | Some old_l, Some old_m -> IM.is_valid_finished old_l old_m
    | _, _ -> pure False);
  c.handshake.messages.client_finished := Some lfin;
  fold (finished_slot_exactly
    c.handshake.messages.client_finished
    (Some (Ghost.reveal fin)));
  fold (handshake_messages_exactly
    c.handshake.messages
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys ==
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys));

  rewrite (handshake_start_exactly
    c.handshake.start
    st0.CS.cs_model.CS.model_handshake.CS.hs_start)
    as (handshake_start_exactly
      c.handshake.start
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
  unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
  fold (server_key_share_exactly
    c.handshake.server_key_share
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  rewrite (peer_exactly
    c.handshake.validated_peer
    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
    as (peer_exactly
      c.handshake.validated_peer
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
  rewrite (handshake_buffers_exactly
    c.handshake.buffers
    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
    as (handshake_buffers_exactly
      c.handshake.buffers
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
  rewrite (key_schedule_exactly
    c.handshake.keys
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys)
    as (key_schedule_exactly
      c.handshake.keys
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);
  assert (pure (cv_verified ==
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
  assert (pure (server_finished_verified ==
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
  fold (handshake_exactly
    c.handshake
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);
  fold (connection_model_exactly
    c
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_client_finished_state_evolves st0 (Ghost.reveal fin) (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)))
}

fn try_send_client_finished
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* fin raw_sent network_out_bytes.
              connection_exactly c (sent_client_finished_state st0 fin raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    58 <= B.length network_out_bytes /\
                    can_send_client_finished st0 fin raw_sent /\
                    (exists outer_fragment.
                       W.parse_record (Seq.slice network_out_bytes 0 58) ==
                         Some (T.ApplicationData, outer_fragment, 58)) /\
                    Seq.equal raw_sent (Seq.slice network_out_bytes 0 58))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_client_finished_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsServerFinishedVerified));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <= max_transcript_len));
    assert (pure (58 <= SZ.v network_out_len));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    with cv_verified server_finished_verified. _;
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

    unfold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    unfold (traffic_key_material_exactly
      c.handshake.keys.client_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    with ch_present ch_secret ch_key ch_iv. _;
    lemma_traffic_key_material_match_present_of_some
      ch_present
      ch_secret
      ch_key
      ch_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
      Some {
        CS.traffic_secret = ch_secret;
        CS.traffic_key = ch_key;
        CS.traffic_iv = ch_iv;
      }));

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
    let mut verify_data = [| 0uy; 32sz |];
    KS.finished_verify_data
      (V.vec_to_array c.handshake.keys.client_handshake_traffic.traffic_secret)
      transcript_hash
      verify_data;
    V.to_vec_pts_to c.handshake.keys.client_handshake_traffic.traffic_secret;
    with verify_data_bytes. assert (ArrPts.pts_to verify_data verify_data_bytes);
    assert (pure (verify_data_bytes ==
      K.finished_verify_data
        ch_secret
        (Tr.hash st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)));

    fold (traffic_key_material_exactly
      c.handshake.keys.client_handshake_traffic
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    fold (key_schedule_exactly
      c.handshake.keys
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
    fold (sized_bytes_exactly
      c.handshake.transcript
      max_transcript_len
      st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
    fold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);

    let fin = Ghost.hide ({ M.verify_data = verify_data_bytes });
    let fin_vec = V.alloc 0uy 32sz;
    copy_fixed32_array_to_vec verify_data fin_vec;
    let lfin = { IM.finished_verify_data = fin_vec };
    assert (pure (lfin.IM.finished_verify_data == fin_vec));
    with fin_vec_bytes. assert (V.pts_to fin_vec fin_vec_bytes);
    assert (pure (fin_vec_bytes == verify_data_bytes));
    rewrite (V.pts_to fin_vec fin_vec_bytes)
      as (V.pts_to lfin.IM.finished_verify_data fin_vec_bytes);
    assert (pure (B.length verify_data_bytes == 32));
    assert (pure (Seq.equal fin_vec_bytes (Ghost.reveal fin).M.verify_data));
    fold (IM.is_valid_finished lfin (Ghost.reveal fin));

    let mut serialized_finished = [| 0uy; 36sz |];
    unfold connection_exactly c st0;
    unfold connection_model_exactly c st0.CS.cs_model;
    unfold record_layer_exactly c.records st0.CS.cs_model.CS.model_record;
    let written_raw =
      Ser.serialize_client_finished_outputs
        c.records.write
        lfin
        serialized_finished
        network_out
        network_out_len;
    with sent_fin serialized_finished_bytes network_out_bytes. _;
    fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (connection_model_exactly c st0.CS.cs_model);
    fold (connection_exactly c st0);
    let fin_sent = Ghost.hide sent_fin;
    assert (pure (B.length serialized_finished_bytes == 36));
    assert (pure (Seq.equal
      serialized_finished_bytes
      (W.serialize_handshake (M.Finished (Ghost.reveal fin_sent)))));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v written_raw == 58));
    assert (pure (58 <= B.length network_out_bytes));
    let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written_raw));
    assert (pure (Seq.equal
      (Ghost.reveal raw_sent)
      (Seq.slice network_out_bytes 0 58)));
    assert (pure (CS.raw_records_exactly (Ghost.reveal raw_sent) T.ApplicationData 1));

    assert (pure (CS.legal_event
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin_sent));
      })));
    assert (pure (CS.event_raw_delta_legal
      st0.CS.cs_model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished (Ghost.reveal fin_sent));
      })
      (Ghost.reveal raw_sent)
      B.empty));
    W.lemma_serialize_finished_len (Ghost.reveal fin_sent);
    assert (pure (B.length st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.Finished (Ghost.reveal fin_sent))) <= max_transcript_len));
    assert (pure (can_send_client_finished st0 (Ghost.reveal fin_sent) (Ghost.reveal raw_sent)));
    assert (pure (SZ.v written_raw <= B.length network_out_bytes));

    mark_sent_client_finished
      c
      serialized_finished
      36sz
      lfin
      network_out
      written_raw
      #fin_sent
      #raw_sent;
    true
  } else {
    false
  }
}

fn mark_sent_application_data_after_record_advanced
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 B.length 'payload_bytes == SZ.v payload_len /\
                 can_send_application_data
                   st0
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == SZ.v payload_len + 22 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_application_data_state
              st0
              (Ghost.reveal 'payload_bytes)
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to payload 'payload_bytes **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_application_data
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure (CS.pending_application_consistent
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
    st0.CS.cs_model.CS.model_control));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake ==
    st0.CS.cs_model.CS.model_handshake));
  assert (pure ((sent_application_data_state
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
    { st0.CS.cs_model.CS.model_record with
        CS.record_write = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }));

  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure)
    as (control_exactly
      c.control
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);
  rewrite (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake)
    as (handshake_exactly
      c.handshake
      (sent_application_data_state
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  fold (connection_model_exactly
    c
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_application_data_state_evolves
    st0
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_application_data_state
      st0
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal raw_sent)))
}

fn mark_sent_close_notify_after_record_advanced
  (c:connection_state)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 can_send_close_notify
                   st0
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == 24 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_close_notify_state
              st0
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to network_out 'network_out_bytes
{
  assert (pure (can_send_close_notify
    st0
    (Ghost.reveal raw_sent)));
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));

  unfold (control_exactly
    c.control
    st0.CS.cs_model.CS.model_control
    st0.CS.cs_model.CS.model_failure);
  assert (pure (st0.CS.cs_model.CS.model_failure == None));
  c.control.control_tag := 3uy;
  c.control.handshake_stage_tag := 0uy;
  c.control.failure_present := false;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 0uy;

  assert (pure (Tags.control_state_matches
    3uy
    0uy
    false
    0uy
    0uy
    CS.ControlClosing));
  fold (control_exactly
    c.control
    CS.ControlClosing
    st0.CS.cs_model.CS.model_failure);

  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
    CS.ControlClosing));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
    st0.CS.cs_model.CS.model_failure));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake ==
    st0.CS.cs_model.CS.model_handshake));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application ==
    st0.CS.cs_model.CS.model_application));
  assert (pure ((sent_close_notify_state
    st0
    (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record ==
    { st0.CS.cs_model.CS.model_record with
        CS.record_write = R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }));

  rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
    as (connection_config_exactly
      c.config
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
  rewrite (control_exactly
    c.control
    CS.ControlClosing
    st0.CS.cs_model.CS.model_failure)
    as (control_exactly
      c.control
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);
  rewrite (record_layer_exactly
    c.records
    ({ st0.CS.cs_model.CS.model_record with
        CS.record_write =
          R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }))
    as (record_layer_exactly
      c.records
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);
  rewrite (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake)
    as (handshake_exactly
      c.handshake
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
  rewrite (application_exactly c.application st0.CS.cs_model.CS.model_application)
    as (application_exactly
      c.application
      (sent_close_notify_state
        st0
        (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

  fold (connection_model_exactly
    c
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent)).CS.cs_model);

  lemma_sent_close_notify_state_evolves
    st0
    (Ghost.reveal raw_sent);
  MR.update
    c.ghost_state
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent));
  fold (connection_exactly
    c
    (sent_close_notify_state
      st0
      (Ghost.reveal raw_sent)))
}

fn try_send_application_data
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_application_data_state
                  st0
                  (Ghost.reveal 'payload_bytes)
                  raw_sent) **
              ArrPts.pts_to payload 'payload_bytes **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    SZ.v payload_len + 22 <= B.length network_out_bytes /\
                    can_send_application_data
                      st0
                      (Ghost.reveal 'payload_bytes)
                      raw_sent /\
                    (exists outer_fragment.
                       W.parse_record
                         (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22)) ==
                         Some
                           (T.ApplicationData,
                            outer_fragment,
                            SZ.v payload_len + 22)) /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22)))
          else
            connection_exactly c st0 **
            ArrPts.pts_to payload 'payload_bytes **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_endpoint_application_data_runtime c payload_len network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (CS.application_traffic_available_for_role
      st0.CS.cs_model.CS.model_config.CS.config_role
      st0.CS.cs_model.CS.model_handshake
      CL.Sent));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) == SZ.v payload_len));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) <= SM.max_application_data_fragment_len));
    lemma_application_data_record_count_small (Ghost.reveal 'payload_bytes);
    assert (pure (SM.application_data_record_count (Ghost.reveal 'payload_bytes) == 1));
    assert (pure (SZ.v payload_len + 22 <= SZ.v network_out_len));

    assert (pure (SZ.fits (SZ.v payload_len + 1)));
    let inner_plaintext_len = SZ.add payload_len 1sz;
    assert (pure (SZ.v inner_plaintext_len == SZ.v payload_len + 1));
    assert (pure (SZ.fits (SZ.v inner_plaintext_len + 16)));
    let ciphertext_len = SZ.add inner_plaintext_len 16sz;
    assert (pure (SZ.v ciphertext_len == SZ.v payload_len + 17));
    assert (pure (SZ.v ciphertext_len <= 16640));
    assert (pure (SZ.v ciphertext_len + 5 <= SZ.v network_out_len));

    let inner_plaintext = V.alloc 0uy inner_plaintext_len;
    with old_inner_plaintext_bytes.
      assert (V.pts_to inner_plaintext old_inner_plaintext_bytes);
    V.pts_to_len inner_plaintext;
    assert (pure (B.length old_inner_plaintext_bytes == SZ.v inner_plaintext_len));
    V.to_array_pts_to inner_plaintext;
    Ser.encode_inner_plaintext_no_padding_slice
      payload
      payload_len
      0sz
      payload_len
      23uy
      (V.vec_to_array inner_plaintext)
      inner_plaintext_len;
    with inner_plaintext_bytes.
      assert (ArrPts.pts_to (V.vec_to_array inner_plaintext) inner_plaintext_bytes);
    assert (pure (B.length inner_plaintext_bytes == SZ.v inner_plaintext_len));

    let ciphertext = V.alloc 0uy ciphertext_len;
    with old_ciphertext_bytes.
      assert (V.pts_to ciphertext old_ciphertext_bytes);
    V.pts_to_len ciphertext;
    assert (pure (B.length old_ciphertext_bytes == SZ.v ciphertext_len));
    let mut aad = [| 0uy; 5sz |];
    Ser.serialize_application_data_header ciphertext_len aad 5sz;
    with aad_bytes.
      assert (ArrPts.pts_to aad aad_bytes);
    assert (pure (B.length aad_bytes == 5));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

    V.to_array_pts_to ciphertext;
    let sealed =
      Rec.seal_application
        c.records.write
        aad
        5sz
        (V.vec_to_array inner_plaintext)
        inner_plaintext_len
        (V.vec_to_array ciphertext);
    with sealed_write ciphertext_bytes. _;
    if sealed {
      assert (pure (R.seal
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        { R.content_type = T.ApplicationData;
          R.fragment = inner_plaintext_bytes } ==
        Some (ciphertext_bytes, sealed_write)));
      lemma_seal_application_success_next_seq
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes
        sealed_write;
      assert (pure (sealed_write ==
        R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      fold (record_layer_exactly
        c.records
        { st0.CS.cs_model.CS.model_record with
            CS.record_write =
              R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write });

      assert (pure (B.length ciphertext_bytes == SZ.v ciphertext_len));
      let written =
        Ser.serialize_raw_application_data_record
          (V.vec_to_array ciphertext)
          ciphertext_len
          network_out
          network_out_len;
      with network_out_bytes.
        assert (ArrPts.pts_to network_out network_out_bytes);
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
      assert (pure (SZ.v written == SZ.v payload_len + 22));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written))));
      assert (pure (CS.raw_records_exactly
        (Ghost.reveal raw_sent)
        T.ApplicationData
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsApplicationData (Ghost.reveal 'payload_bytes)) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })
        (Ghost.reveal raw_sent)
        B.empty));
      assert (pure (IM.content_type_matches 23uy T.ApplicationData));
      Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len);
      assert (pure (Seq.equal
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))
        (Ghost.reveal 'payload_bytes)));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.ApplicationData;
          M.fragment =
            Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len);
        })));
      Seq.lemma_eq_elim
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))
        (Ghost.reveal 'payload_bytes);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.ApplicationData;
          M.fragment = Ghost.reveal 'payload_bytes;
        })));
      W.lemma_serialize_tls_message_application_data (Ghost.reveal 'payload_bytes);
      assert (pure (
        CS.sent_tls_inner_plaintext_fragment
          (M.TlsApplicationData (Ghost.reveal 'payload_bytes)) ==
        W.serialize_plaintext {
          M.content_type = T.ApplicationData;
          M.fragment = Ghost.reveal 'payload_bytes;
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (CS.sent_tls_inner_plaintext_fragment
          (M.TlsApplicationData (Ghost.reveal 'payload_bytes)))));
      assert (pure (Seq.equal
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsApplicationData (Ghost.reveal 'payload_bytes))
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (CS.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })
        (Ghost.reveal raw_sent)));
      assert (pure (can_send_application_data
        st0
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal raw_sent)));

      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;

      mark_sent_application_data_after_record_advanced
        c
        payload
        payload_len
        network_out
        written
        #raw_sent;

      assert (pure (SZ.v written == SZ.v payload_len + 22));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22))));
      true
    } else {
      assert (pure (sealed_write ==
        st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          st0.CS.cs_model.CS.model_record.CS.record_write);
      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    false
  }
}

fn try_send_close_notify
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_close_notify_state
                  st0
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    24 <= B.length network_out_bytes /\
                    can_send_close_notify
                      st0
                      raw_sent /\
                    (exists outer_fragment.
                       W.parse_record (Seq.slice network_out_bytes 0 24) ==
                         Some (T.ApplicationData, outer_fragment, 24)) /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 24))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_endpoint_close_notify_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (CS.application_traffic_available_for_role
      st0.CS.cs_model.CS.model_config.CS.config_role
      st0.CS.cs_model.CS.model_handshake
      CL.Sent));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (24 <= SZ.v network_out_len));

    let mut alert_plaintext = [| 0uy; 2sz |];
    write_close_notify_alert alert_plaintext;
    with alert_plaintext_bytes.
      assert (ArrPts.pts_to alert_plaintext alert_plaintext_bytes);
    assert (pure (Seq.equal alert_plaintext_bytes close_notify_alert_fragment));
    assert (pure (B.length alert_plaintext_bytes == 2));

    let inner_plaintext_len = 3sz;
    assert (pure (SZ.v inner_plaintext_len == 3));
    let inner_plaintext = V.alloc 0uy inner_plaintext_len;
    with old_inner_plaintext_bytes.
      assert (V.pts_to inner_plaintext old_inner_plaintext_bytes);
    V.pts_to_len inner_plaintext;
    assert (pure (B.length old_inner_plaintext_bytes == SZ.v inner_plaintext_len));
    V.to_array_pts_to inner_plaintext;
    Ser.encode_inner_plaintext_no_padding_slice
      alert_plaintext
      2sz
      0sz
      2sz
      21uy
      (V.vec_to_array inner_plaintext)
      inner_plaintext_len;
    with inner_plaintext_bytes.
      assert (ArrPts.pts_to (V.vec_to_array inner_plaintext) inner_plaintext_bytes);
    assert (pure (B.length inner_plaintext_bytes == 3));

    let ciphertext_len = 19sz;
    assert (pure (SZ.v ciphertext_len == 19));
    assert (pure (SZ.v ciphertext_len == SZ.v inner_plaintext_len + 16));
    assert (pure (SZ.v ciphertext_len <= 16640));
    assert (pure (SZ.v ciphertext_len + 5 <= SZ.v network_out_len));

    let ciphertext = V.alloc 0uy ciphertext_len;
    with old_ciphertext_bytes.
      assert (V.pts_to ciphertext old_ciphertext_bytes);
    V.pts_to_len ciphertext;
    assert (pure (B.length old_ciphertext_bytes == SZ.v ciphertext_len));
    assert (pure (B.length old_ciphertext_bytes == B.length inner_plaintext_bytes + 16));
    let mut aad = [| 0uy; 5sz |];
    Ser.serialize_application_data_header ciphertext_len aad 5sz;
    with aad_bytes.
      assert (ArrPts.pts_to aad aad_bytes);
    assert (pure (B.length aad_bytes == 5));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

    V.to_array_pts_to ciphertext;
    let sealed =
      Rec.seal_application
        c.records.write
        aad
        5sz
        (V.vec_to_array inner_plaintext)
        inner_plaintext_len
        (V.vec_to_array ciphertext);
    with sealed_write ciphertext_bytes. _;
    if sealed {
      assert (pure (R.seal
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        { R.content_type = T.ApplicationData;
          R.fragment = inner_plaintext_bytes } ==
        Some (ciphertext_bytes, sealed_write)));
      lemma_seal_application_success_next_seq
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes
        sealed_write;
      assert (pure (sealed_write ==
        R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      fold (record_layer_exactly
        c.records
        { st0.CS.cs_model.CS.model_record with
            CS.record_write =
              R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write });

      assert (pure (B.length ciphertext_bytes == SZ.v ciphertext_len));
      let written =
        Ser.serialize_raw_application_data_record
          (V.vec_to_array ciphertext)
          ciphertext_len
          network_out
          network_out_len;
      with network_out_bytes.
        assert (ArrPts.pts_to network_out network_out_bytes);
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
      assert (pure (SZ.v written == 24));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written))));
      assert (pure (CS.raw_records_exactly
        (Ghost.reveal raw_sent)
        T.ApplicationData
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsAlert T.CloseNotify) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })
        (Ghost.reveal raw_sent)
        B.empty));
      assert (pure (IM.content_type_matches 21uy T.Alert));
      Seq.lemma_len_slice alert_plaintext_bytes 0 2;
      assert (pure (Seq.equal
        (Seq.slice alert_plaintext_bytes 0 2)
        alert_plaintext_bytes));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Alert;
          M.fragment = Seq.slice alert_plaintext_bytes 0 2;
        })));
      Seq.lemma_eq_elim (Seq.slice alert_plaintext_bytes 0 2) alert_plaintext_bytes;
      assert (pure (Seq.equal alert_plaintext_bytes Model.close_notify_alert_fragment));
      Seq.lemma_eq_elim alert_plaintext_bytes Model.close_notify_alert_fragment;
      assert (pure (Seq.equal alert_plaintext_bytes (B.of_list [2uy; 0uy])));
      Seq.lemma_eq_elim alert_plaintext_bytes (B.of_list [2uy; 0uy]);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Alert;
          M.fragment = B.of_list [2uy; 0uy];
        })));
      W.lemma_serialize_tls_message_close_notify ();
      assert (pure (
        CS.sent_tls_inner_plaintext_fragment (M.TlsAlert T.CloseNotify) ==
        W.serialize_plaintext {
          M.content_type = T.Alert;
          M.fragment = B.of_list [2uy; 0uy];
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (CS.sent_tls_inner_plaintext_fragment (M.TlsAlert T.CloseNotify))));
      assert (pure (Seq.equal
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsAlert T.CloseNotify)
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (CS.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })
        (Ghost.reveal raw_sent)));
      assert (pure (can_send_close_notify
        st0
        (Ghost.reveal raw_sent)));

      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;

      mark_sent_close_notify_after_record_advanced
        c
        network_out
        written
        #raw_sent;

      assert (pure (SZ.v written == 24));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 24)));
      true
    } else {
      assert (pure (sealed_write ==
        st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          st0.CS.cs_model.CS.model_record.CS.record_write);
      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    false
  }
}

fn try_send_key_update
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_key_update_response_state
                  st0
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    27 <= B.length network_out_bytes /\
                    can_send_key_update
                      st0
                      raw_sent /\
                    (exists outer_fragment.
                       W.parse_record (Seq.slice network_out_bytes 0 27) ==
                         Some (T.ApplicationData, outer_fragment, 27)) /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 27))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_key_update_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (27 <= SZ.v network_out_len));

    let mut key_update_plaintext = [| 0uy; 5sz |];
    write_key_update_response key_update_plaintext;
    with key_update_plaintext_bytes.
      assert (ArrPts.pts_to key_update_plaintext key_update_plaintext_bytes);
    assert (pure (Seq.equal key_update_plaintext_bytes key_update_response_fragment));
    assert (pure (B.length key_update_plaintext_bytes == 5));

    let inner_plaintext_len = 6sz;
    assert (pure (SZ.v inner_plaintext_len == 6));
    let inner_plaintext = V.alloc 0uy inner_plaintext_len;
    with old_inner_plaintext_bytes.
      assert (V.pts_to inner_plaintext old_inner_plaintext_bytes);
    V.pts_to_len inner_plaintext;
    assert (pure (B.length old_inner_plaintext_bytes == SZ.v inner_plaintext_len));
    V.to_array_pts_to inner_plaintext;
    Ser.encode_inner_plaintext_no_padding_slice
      key_update_plaintext
      5sz
      0sz
      5sz
      22uy
      (V.vec_to_array inner_plaintext)
      inner_plaintext_len;
    with inner_plaintext_bytes.
      assert (ArrPts.pts_to (V.vec_to_array inner_plaintext) inner_plaintext_bytes);
    assert (pure (B.length inner_plaintext_bytes == 6));

    let ciphertext_len = 22sz;
    assert (pure (SZ.v ciphertext_len == 22));
    assert (pure (SZ.v ciphertext_len == SZ.v inner_plaintext_len + 16));
    assert (pure (SZ.v ciphertext_len <= 16640));
    assert (pure (SZ.v ciphertext_len + 5 <= SZ.v network_out_len));

    let ciphertext = V.alloc 0uy ciphertext_len;
    with old_ciphertext_bytes.
      assert (V.pts_to ciphertext old_ciphertext_bytes);
    V.pts_to_len ciphertext;
    assert (pure (B.length old_ciphertext_bytes == SZ.v ciphertext_len));
    assert (pure (B.length old_ciphertext_bytes == B.length inner_plaintext_bytes + 16));
    let mut aad = [| 0uy; 5sz |];
    Ser.serialize_application_data_header ciphertext_len aad 5sz;
    with aad_bytes.
      assert (ArrPts.pts_to aad aad_bytes);
    assert (pure (B.length aad_bytes == 5));

    unfold (connection_exactly c st0);
    unfold (connection_model_exactly c st0.CS.cs_model);
    unfold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);

    V.to_array_pts_to ciphertext;
    let sealed =
      Rec.seal_application
        c.records.write
        aad
        5sz
        (V.vec_to_array inner_plaintext)
        inner_plaintext_len
        (V.vec_to_array ciphertext);
    with sealed_write ciphertext_bytes. _;
    if sealed {
      assert (pure (R.seal
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        { R.content_type = T.ApplicationData;
          R.fragment = inner_plaintext_bytes } ==
        Some (ciphertext_bytes, sealed_write)));
      lemma_seal_application_success_next_seq
        st0.CS.cs_model.CS.model_record.CS.record_write
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes
        sealed_write;
      assert (pure (sealed_write ==
        R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write));

      assert (pure (B.length ciphertext_bytes == SZ.v ciphertext_len));
      let written =
        Ser.serialize_raw_application_data_record
          (V.vec_to_array ciphertext)
          ciphertext_len
          network_out
          network_out_len;
      with network_out_bytes.
        assert (ArrPts.pts_to network_out network_out_bytes);
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
      assert (pure (SZ.v written == 27));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let raw_sent = Ghost.hide (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written))));
      assert (pure (CS.raw_records_exactly
        (Ghost.reveal raw_sent)
        T.ApplicationData
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsKeyUpdate M.UpdateNotRequested) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
        })
        (Ghost.reveal raw_sent)
        B.empty));
      assert (pure (IM.content_type_matches 22uy T.Handshake));
      Seq.lemma_len_slice key_update_plaintext_bytes 0 5;
      assert (pure (Seq.equal
        (Seq.slice key_update_plaintext_bytes 0 5)
        key_update_plaintext_bytes));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = Seq.slice key_update_plaintext_bytes 0 5;
        })));
      Seq.lemma_eq_elim
        (Seq.slice key_update_plaintext_bytes 0 5)
        key_update_plaintext_bytes;
      assert (pure (Seq.equal
        key_update_plaintext_bytes
        Model.key_update_response_fragment));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        Model.key_update_response_fragment;
      assert (pure (Seq.equal
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; 0uy])));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; 0uy];
        })));
      W.lemma_serialize_tls_message_key_update_not_requested ();
      assert (pure (
        CS.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate M.UpdateNotRequested) ==
        W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; 0uy];
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (CS.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate M.UpdateNotRequested))));
      assert (pure (Seq.equal
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (CS.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (CS.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (CS.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsKeyUpdate M.UpdateNotRequested)
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (CS.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
        })
        (Ghost.reveal raw_sent)));
      assert (pure (can_send_key_update
        st0
        (Ghost.reveal raw_sent)));

      unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      with cv_verified server_finished_verified. _;
      unfold (key_schedule_exactly
        c.handshake.keys
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      unfold (traffic_key_material_exactly
        c.handshake.keys.client_application_traffic
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      with old_present old_secret old_key old_iv. _;
      lemma_traffic_key_material_match_present_of_some
        old_present
        old_secret
        old_key
        old_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
      assert (pure (old_present));
      assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
        Some {
          CS.traffic_secret = old_secret;
          CS.traffic_key = old_key;
          CS.traffic_iv = old_iv;
        }));
      let old_material = Ghost.hide (Some?.v
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (pure ((Ghost.reveal old_material).CS.traffic_secret == old_secret));

      V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_secret;
      let mut traffic_secret_out = [| 0uy; 32sz |];
      KS.application_traffic_secret_update
        (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_secret)
        traffic_secret_out;
      V.to_vec_pts_to c.handshake.keys.client_application_traffic.traffic_secret;
      with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
      assert (pure (traffic_secret_bytes ==
        K.application_traffic_secret_update old_secret));

      fold (traffic_key_material_exactly
        c.handshake.keys.client_application_traffic
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);

      let mut traffic_key_out = [| 0uy; 32sz |];
      KS.derive_traffic_key traffic_secret_out traffic_key_out;
      let mut traffic_iv_out = [| 0uy; 12sz |];
      KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
      with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
      with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

      let traffic_secret = Ghost.hide traffic_secret_bytes;
      let material = Ghost.hide (CS.traffic_key_material_for_secret (Ghost.reveal traffic_secret));
      assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
      assert (pure ((Ghost.reveal material).CS.traffic_key == traffic_key_bytes));
      assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
      assert (pure (Ghost.reveal material == CS.updated_traffic_key_material (Ghost.reveal old_material)));

      store_traffic_key_material
        c.handshake.keys.client_application_traffic
        traffic_secret_out
        traffic_key_out
        traffic_iv_out
        #material;

      fold (key_schedule_exactly
        c.handshake.keys
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);

      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));

      rewrite (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start)
        as (handshake_start_exactly
          c.handshake.start
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
      unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      fold (handshake_messages_exactly
        c.handshake.messages
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (server_key_share_exactly
        c.handshake.server_key_share
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      rewrite (peer_exactly
        c.handshake.validated_peer
        st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
        as (peer_exactly
          c.handshake.validated_peer
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
      rewrite (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
        as (sized_bytes_exactly
          c.handshake.transcript
          max_transcript_len
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
      rewrite (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
        as (handshake_buffers_exactly
          c.handshake.buffers
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
      assert (pure (cv_verified ==
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure (server_finished_verified ==
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      fold (handshake_exactly
        c.handshake
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

      Rec.install_application_keys_runtime c.records.write traffic_key_out traffic_iv_out;
      assert (pure (R.install_keys
        (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
        R.Application
        (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv ==
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state
        c.records.write
        (R.install_keys
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
          R.Application
          (Ghost.reveal material).CS.traffic_key
          (Ghost.reveal material).CS.traffic_iv))
        as (Rec.is_record_state
          c.records.write
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write);
      rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
        as (Rec.is_record_state
          c.records.read
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read);
      fold (record_layer_exactly
        c.records
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);

      unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
      with source_offset pending_response. _;
      c.application.key_update_response_pending := false;
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_key_update_response_pending == false));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
      assert (pure (CS.pending_application_consistent
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application));
      fold (application_exactly
        c.application
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
                    st0.CS.cs_model.CS.model_config));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
                    st0.CS.cs_model.CS.model_control));
      assert (pure ((sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
                    st0.CS.cs_model.CS.model_failure));
      rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
        as (connection_config_exactly
          c.config
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
      rewrite (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure)
        as (control_exactly
          c.control
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
          (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);

      fold (connection_model_exactly
        c
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)).CS.cs_model);

      lemma_sent_key_update_response_state_evolves
        st0
        (Ghost.reveal raw_sent);
      MR.update
        c.ghost_state
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent));
      fold (connection_exactly
        c
        (sent_key_update_response_state st0 (Ghost.reveal raw_sent)));

      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;

      assert (pure (SZ.v written == 27));
      assert (pure (Seq.equal
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 27)));
      true
    } else {
      assert (pure (sealed_write ==
        st0.CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state c.records.write sealed_write)
        as (Rec.is_record_state
          c.records.write
          st0.CS.cs_model.CS.model_record.CS.record_write);
      V.to_vec_pts_to inner_plaintext;
      V.free inner_plaintext;
      V.to_vec_pts_to ciphertext;
      V.free ciphertext;
      fold (record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
      fold (connection_model_exactly c st0.CS.cs_model);
      fold (connection_exactly c st0);
      false
    }
  } else {
    false
  }
}
