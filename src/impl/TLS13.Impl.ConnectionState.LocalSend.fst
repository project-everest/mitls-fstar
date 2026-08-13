module TLS13.Impl.ConnectionState.LocalSend

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
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
module PR = Pulse.Lib.Reference
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
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module GA = TLS13.Wire.Generated.Alert
module GAL = TLS13.Wire.Generated.AlertLevel
module GAD = TLS13.Wire.Generated.AlertDescription
module LP = LowParse.Spec
module LPC = LowParse.Pulse.Combinators
module LPS = LowParse.Pulse.Base

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
                  Seq.equal alert_bytes (close_notify_alert_fragment ()))
{
  let low : GA.alert_lowtype = (GAL.Fatal, GAD.Close_notify);
  let mid : Ghost.erased GA.alert_mid =
    Ghost.hide (GAL.Fatal, GAD.Close_notify);
  fold (LPS.eq_as_slprop GAL.alertLevel GAL.Fatal GAL.Fatal);
  fold (LPS.eq_as_slprop GAD.alertDescription GAD.Close_notify GAD.Close_notify);
  rewrite (LPS.eq_as_slprop GAL.alertLevel GAL.Fatal GAL.Fatal)
       as (GAL.alertLevel_vmatch GAL.Fatal GAL.Fatal);
  rewrite (LPS.eq_as_slprop GAD.alertDescription GAD.Close_notify GAD.Close_notify)
       as (GAD.alertDescription_vmatch GAD.Close_notify GAD.Close_notify);
  rewrite (GAL.alertLevel_vmatch GAL.Fatal GAL.Fatal)
       as (GAL.alertLevel_vmatch (fst low) (fst (Ghost.reveal mid)));
  rewrite (GAD.alertDescription_vmatch GAD.Close_notify GAD.Close_notify)
       as (GAD.alertDescription_vmatch (snd low) (snd (Ghost.reveal mid)));
  fold (LPC.vmatch_pair
    GAL.alertLevel_vmatch GAD.alertDescription_vmatch low (Ghost.reveal mid));
  rewrite
    (LPC.vmatch_pair
      GAL.alertLevel_vmatch GAD.alertDescription_vmatch low (Ghost.reveal mid))
    as (GA.alert_vmatch low (Ghost.reveal mid));
  let record : Ghost.erased GA.alert = Ghost.hide {
    GA.level = GAL.Fatal;
    GA.description = GAD.Close_notify;
  };
  assert (pure (GA.alert_conv (Ghost.reveal mid) ==
    Some (Ghost.reveal record)));
  LP.serialize_length GAL.alertLevel_serializer GAL.Fatal;
  LP.serialize_length GAD.alertDescription_serializer GAD.Close_notify;
  GA.alert_bytesize_eqn (Ghost.reveal record);
  assert (pure (B.length
    (LP.serialize GA.alert_serializer (Ghost.reveal record)) == 2));
  ArrPts.pts_to_len alert;
  let s = Slice.from_array alert 2sz;
  Slice.pts_to_len s;
  let s_len = Slice.len s;
  assert (pure (SZ.v s_len == 2));
  let mut perr = false;
  let written = GA.write_alert low #mid s perr;
  with slice_bytes. assert (Slice.pts_to s slice_bytes);
  Slice.pts_to_len s;
  assert (pure (B.length slice_bytes == 2));
  let err = PR.read perr;
  assert (pure (err == false));
  Slice.to_array s;
  with alert_bytes.
    assert (ArrPts.pts_to alert alert_bytes);
  Model.lemma_close_notify_alert_fragment_generated ();
  assert (pure (B.length alert_bytes == 2));
  assert (pure (SZ.v written == 2));
  assert (pure (Seq.equal
    alert_bytes
    (LP.serialize GA.alert_serializer {
      GA.level = GAL.Fatal;
      GA.description = GAD.Close_notify;
    })));
  assert (pure (
    LP.serialize GA.alert_serializer {
      GA.level = GAL.Fatal;
      GA.description = GAD.Close_notify;
    } == close_notify_alert_fragment ()));
  Seq.lemma_eq_refl
    (LP.serialize GA.alert_serializer {
      GA.level = GAL.Fatal;
      GA.description = GAD.Close_notify;
    })
    (close_notify_alert_fragment ());
  Seq.lemma_eq_elim
    alert_bytes
    (LP.serialize GA.alert_serializer {
      GA.level = GAL.Fatal;
      GA.description = GAD.Close_notify;
    });
  assert (pure (Seq.equal alert_bytes (close_notify_alert_fragment ())));
  unfold (GA.alert_vmatch low (Ghost.reveal mid));
  unfold (LPC.vmatch_pair
    GAL.alertLevel_vmatch GAD.alertDescription_vmatch low (Ghost.reveal mid));
  rewrite (GAL.alertLevel_vmatch (fst low) (fst (Ghost.reveal mid)))
       as (GAL.alertLevel_vmatch GAL.Fatal GAL.Fatal);
  rewrite (GAD.alertDescription_vmatch (snd low) (snd (Ghost.reveal mid)))
       as (GAD.alertDescription_vmatch GAD.Close_notify GAD.Close_notify);
  rewrite (GAL.alertLevel_vmatch GAL.Fatal GAL.Fatal)
       as (LPS.eq_as_slprop GAL.alertLevel GAL.Fatal GAL.Fatal);
  rewrite (GAD.alertDescription_vmatch GAD.Close_notify GAD.Close_notify)
       as (LPS.eq_as_slprop
         GAD.alertDescription GAD.Close_notify GAD.Close_notify);
  unfold (LPS.eq_as_slprop GAL.alertLevel GAL.Fatal GAL.Fatal);
  unfold (LPS.eq_as_slprop
    GAD.alertDescription GAD.Close_notify GAD.Close_notify)
}

fn write_key_update
  (handshake:array U8.t)
  (req:M.key_update_request)
  requires ArrPts.pts_to handshake (Seq.create 5 0uy)
  ensures exists* handshake_bytes.
            ArrPts.pts_to handshake handshake_bytes **
            pure (B.length handshake_bytes == 5 /\
                  Seq.equal handshake_bytes (key_update_fragment req))
{
  handshake.(0sz) <- 24uy;
  handshake.(1sz) <- 0uy;
  handshake.(2sz) <- 0uy;
  handshake.(3sz) <- 1uy;
  let request_byte = W.key_update_request_byte req;
  handshake.(4sz) <- request_byte;
  with handshake_bytes.
    assert (ArrPts.pts_to handshake handshake_bytes);
  lemma_key_update_fragment_bytes req;
  assert (pure (B.length handshake_bytes == 5));
  assert (pure (Seq.index handshake_bytes 0 == 24uy));
  assert (pure (Seq.index handshake_bytes 1 == 0uy));
  assert (pure (Seq.index handshake_bytes 2 == 0uy));
  assert (pure (Seq.index handshake_bytes 3 == 1uy));
  assert (pure (Seq.index handshake_bytes 4 == W.key_update_request_byte req));
  Seq.lemma_eq_intro handshake_bytes (key_update_fragment req);
  assert (pure (Seq.equal handshake_bytes (key_update_fragment req)))
}

fn write_key_update_response
  (handshake:array U8.t)
  requires ArrPts.pts_to handshake (Seq.create 5 0uy)
  ensures exists* handshake_bytes.
            ArrPts.pts_to handshake handshake_bytes **
            pure (B.length handshake_bytes == 5 /\
                  Seq.equal handshake_bytes key_update_response_fragment)
{
  write_key_update handshake M.UpdateNotRequested;
  with handshake_bytes.
    assert (ArrPts.pts_to handshake handshake_bytes);
  lemma_key_update_fragment_response ();
  Seq.lemma_eq_intro handshake_bytes key_update_response_fragment
}

fn mark_sent_client_finished
  (c:connection_state)
  (handshake_bytes:array U8.t)
  (handshake_len:SZ.t)
  (lfin:IM.finished)
  (network_out:array U8.t)
  (written:SZ.t)
  (#fin:erased GFin.finished)
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
  with ca_present ca_secret ca_alg ca_key ca_iv. _;
  lemma_traffic_key_material_match_present_of_some
    ca_present
    ca_secret
    ca_alg
    ca_key
    ca_iv
    st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
  assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
    Some {
      CS.traffic_secret = ca_secret;
      CS.traffic_alg = ca_alg;
      CS.traffic_key = CryptoSpec.logical_key ca_alg ca_key;
      CS.traffic_iv = ca_iv;
    }));

  let ca_alg_runtime = !c.handshake.keys.client_application_traffic.alg;
  assert (pure (ca_alg_runtime == ca_alg));
  Rec.advance_seq c.records.write;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_key;
  V.to_array_pts_to c.handshake.keys.client_application_traffic.traffic_iv;
  Rec.install_application_keys_runtime
    c.records.write
    (V.vec_to_array c.handshake.keys.client_application_traffic.traffic_key)
    ca_alg_runtime
    (Ghost.hide (CryptoSpec.logical_key ca_alg ca_key))
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
      ca_alg_runtime
      (CryptoSpec.logical_key ca_alg ca_key)
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
      ca_alg_runtime
      (CryptoSpec.logical_key ca_alg ca_key)
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
                         Some (T.Application_data, outer_fragment, 58)) /\
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
    assert (pure (
      match st0.CS.cs_model.CS.model_record.CS.record_write.R.key,
            st0.CS.cs_model.CS.model_record.CS.record_write.R.static_iv with
      | Some _, Some _ -> True
      | _, _ -> False));
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
    with ch_present ch_secret ch_alg ch_key ch_iv. _;
    lemma_traffic_key_material_match_present_of_some
      ch_present
      ch_secret
      ch_alg
      ch_key
      ch_iv
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic;
    assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
      Some {
        CS.traffic_secret = ch_secret;
        CS.traffic_alg = ch_alg;
        CS.traffic_key = CryptoSpec.logical_key ch_alg ch_key;
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

    assert (pure (B.length verify_data_bytes == 32));
    let fin = Ghost.hide (verify_data_bytes <: GFin.finished);
    let fin_vec = V.alloc 0uy 32sz;
    copy_fixed32_array_to_vec verify_data fin_vec;
    let lfin = { IM.finished_verify_data = fin_vec };
    assert (pure (lfin.IM.finished_verify_data == fin_vec));
    with fin_vec_bytes. assert (V.pts_to fin_vec fin_vec_bytes);
    assert (pure (fin_vec_bytes == verify_data_bytes));
    rewrite (V.pts_to fin_vec fin_vec_bytes)
      as (V.pts_to lfin.IM.finished_verify_data fin_vec_bytes);
    assert (pure (B.length verify_data_bytes == 32));
    assert (pure (Seq.equal fin_vec_bytes (Sem.finished_verify_data (Ghost.reveal fin))));
    fold (IM.is_valid_finished lfin (Ghost.reveal fin));
    lemma_seal_some_of_keys
      st0.CS.cs_model.CS.model_record.CS.record_write
      (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)
      {
        R.content_type = T.Application_data;
        R.fragment =
          TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
            (M.TlsHandshake (M.Finished (Ghost.reveal fin)));
      };
    assert (pure (Some? (R.seal
      st0.CS.cs_model.CS.model_record.CS.record_write
      (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)
      {
        R.content_type = T.Application_data;
        R.fragment =
          TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
            (M.TlsHandshake (M.Finished (Ghost.reveal fin)));
      })));

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
    assert (pure (CS.raw_records_exactly (Ghost.reveal raw_sent) T.Application_data 1));

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
    // Phase 5: deleted W.lemma_serialize_finished_len.  The fixed 36-byte length of
    // serialize_handshake (M.Finished fin_sent) is recovered from the serializer
    // output facts above (B.length serialized_finished_bytes == 36 and
    // serialized_finished_bytes == serialize_handshake (M.Finished fin_sent)).
    assert (pure (B.length (W.serialize_handshake (M.Finished (Ghost.reveal fin_sent))) ==
      B.length serialized_finished_bytes));
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
           pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0 /\
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
  assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
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
           pure (TLS13.Spec.StateMachine.Reachability.connection_state_consistent st0 /\
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
                           (T.Application_data,
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
        { R.content_type = T.Application_data;
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
        T.Application_data
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
      assert (pure (IM.content_type_matches 23uy T.Application_data));
      Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len);
      assert (pure (Seq.equal
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))
        (Ghost.reveal 'payload_bytes)));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Application_data;
          M.fragment =
            Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len);
        })));
      Seq.lemma_eq_elim
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))
        (Ghost.reveal 'payload_bytes);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Application_data;
          M.fragment = Ghost.reveal 'payload_bytes;
        })));
      W.lemma_serialize_tls_message_application_data (Ghost.reveal 'payload_bytes);
      assert (pure (
        TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsApplicationData (Ghost.reveal 'payload_bytes)) ==
        W.serialize_plaintext {
          M.content_type = T.Application_data;
          M.fragment = Ghost.reveal 'payload_bytes;
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsApplicationData (Ghost.reveal 'payload_bytes)))));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsApplicationData (Ghost.reveal 'payload_bytes))
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
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
                         Some (T.Application_data, outer_fragment, 24)) /\
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
    assert (pure (Seq.equal
      alert_plaintext_bytes (close_notify_alert_fragment ())));
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
        { R.content_type = T.Application_data;
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
        T.Application_data
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.Close_notify;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsAlert T.Close_notify) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.Close_notify;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.Close_notify;
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
      assert (pure (Seq.equal
        alert_plaintext_bytes (Model.close_notify_alert_fragment ())));
      Seq.lemma_eq_elim
        alert_plaintext_bytes (Model.close_notify_alert_fragment ());
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Alert;
          M.fragment = Model.close_notify_alert_fragment ();
        })));
      Model.lemma_close_notify_alert_fragment_generated ();
      W.lemma_serialize_tls_message_close_notify ();
      assert (pure (
        TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment (M.TlsAlert T.Close_notify) ==
        W.serialize_plaintext {
          M.content_type = T.Alert;
          M.fragment = Model.close_notify_alert_fragment ();
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment (M.TlsAlert T.Close_notify))));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsAlert T.Close_notify)
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.Close_notify;
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
  (req:M.key_update_request)
  (need_pending:bool)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_key_update_state
                  st0
                  req
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    27 <= B.length network_out_bytes /\
                    can_send_key_update_gen
                      st0
                      req
                      raw_sent /\
                    (exists outer_fragment.
                       W.parse_record (Seq.slice network_out_bytes 0 27) ==
                         Some (T.Application_data, outer_fragment, 27)) /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 27))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = can_send_key_update_runtime_gen c network_out_len need_pending;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (need_pending ==>
      st0.CS.cs_model.CS.model_application.CS.app_key_update_response_pending));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (27 <= SZ.v network_out_len));

    let mut key_update_plaintext = [| 0uy; 5sz |];
    write_key_update key_update_plaintext req;
    with key_update_plaintext_bytes.
      assert (ArrPts.pts_to key_update_plaintext key_update_plaintext_bytes);
    assert (pure (Seq.equal key_update_plaintext_bytes (key_update_fragment req)));
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
        { R.content_type = T.Application_data;
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
        T.Application_data
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsKeyUpdate req) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
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
        (Model.key_update_fragment req)));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        (Model.key_update_fragment req);
      assert (pure (Seq.equal
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req])));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req]);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req];
        })));
      W.lemma_serialize_tls_message_key_update req;
      assert (pure (
        TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate req) ==
        W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req];
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate req))));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsKeyUpdate req)
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        })
        (Ghost.reveal raw_sent)));
      assert (pure (can_send_key_update_gen
        st0
        req
        (Ghost.reveal raw_sent)));

      unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      with cv_verified server_finished_verified. _;
      unfold (key_schedule_exactly
        c.handshake.keys
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      unfold (traffic_key_material_exactly
        c.handshake.keys.client_application_traffic
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      with old_present old_secret old_alg old_key old_iv. _;
      lemma_traffic_key_material_match_present_of_some
        old_present
        old_secret
        old_alg
        old_key
        old_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic;
      assert (pure (old_present));
      assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic ==
        Some {
          CS.traffic_secret = old_secret;
          CS.traffic_alg = old_alg;
          CS.traffic_key = CryptoSpec.logical_key old_alg old_key;
          CS.traffic_iv = old_iv;
        }));
      let old_material = Ghost.hide (Some?.v
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (pure ((Ghost.reveal old_material).CS.traffic_secret == old_secret));
      let rotate_alg = !c.handshake.keys.client_application_traffic.alg;
      assert (pure (rotate_alg == old_alg));
      assert (pure (CryptoSpec.aead_key_len rotate_alg == B.length (Ghost.reveal old_material).CS.traffic_key));

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
      KS.derive_traffic_key traffic_secret_out rotate_alg traffic_key_out;
      let mut traffic_iv_out = [| 0uy; 12sz |];
      KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
      with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
      with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

      let traffic_secret = Ghost.hide traffic_secret_bytes;
      let material = Ghost.hide (CS.traffic_key_material_for_secret (rotate_alg) (Ghost.reveal traffic_secret));
      assert (pure ((Ghost.reveal material).CS.traffic_alg == rotate_alg));
      assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
      assert (pure (Seq.equal traffic_key_bytes (TLS13.Crypto.Spec.pad_key_32 (Ghost.reveal material).CS.traffic_key)));
      assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
      assert (pure (Ghost.reveal material == CS.updated_traffic_key_material (Ghost.reveal old_material)));

      store_traffic_key_material
        c.handshake.keys.client_application_traffic
        traffic_secret_out
        rotate_alg
        traffic_key_out
        traffic_iv_out
        #material;

      fold (key_schedule_exactly
        c.handshake.keys
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);

      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));

      rewrite (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start)
        as (handshake_start_exactly
          c.handshake.start
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
      unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      rewrite (client_hello_metadata_exactly
        c.handshake.messages.client_hello_has_server_name
        c.handshake.messages.client_hello_server_name_len
        c.handshake.messages.client_hello_cipher_suites_len
        c.handshake.messages.client_hello_signature_schemes_len
        c.handshake.messages.client_hello_session_id_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello) as
        (client_hello_metadata_exactly
          c.handshake.messages.client_hello_has_server_name
          c.handshake.messages.client_hello_server_name_len
          c.handshake.messages.client_hello_cipher_suites_len
          c.handshake.messages.client_hello_signature_schemes_len
          c.handshake.messages.client_hello_session_id_len
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello);
      fold (handshake_messages_exactly
        c.handshake.messages
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      rewrite (server_selection_presence_exactly
        c.handshake.server_selection_present
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection) as
        (server_selection_presence_exactly
          c.handshake.server_selection_present
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_selection);
      unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (server_key_share_exactly
        c.handshake.server_key_share
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      rewrite (peer_exactly
        c.handshake.validated_peer
        st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
        as (peer_exactly
          c.handshake.validated_peer
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
      rewrite (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
        as (sized_bytes_exactly
          c.handshake.transcript
          max_transcript_len
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
      rewrite (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
        as (handshake_buffers_exactly
          c.handshake.buffers
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
      assert (pure (cv_verified ==
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure (server_finished_verified ==
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      fold (handshake_exactly
        c.handshake
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

      Rec.install_application_keys_runtime c.records.write traffic_key_out rotate_alg (Ghost.hide (Ghost.reveal material).CS.traffic_key) traffic_iv_out;
      assert (pure (R.install_keys
        (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
        R.Application
        rotate_alg (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv ==
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state
        c.records.write
        (R.install_keys
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
          R.Application
          rotate_alg (Ghost.reveal material).CS.traffic_key
          (Ghost.reveal material).CS.traffic_iv))
        as (Rec.is_record_state
          c.records.write
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write);
      rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
        as (Rec.is_record_state
          c.records.read
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read);
      fold (record_layer_exactly
        c.records
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);

      unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
      with source_offset pending_response. _;
      let cur_pending = !c.application.key_update_response_pending;
      let new_pending = key_update_clears_pending req cur_pending;
      c.application.key_update_response_pending := new_pending;
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_key_update_response_pending == new_pending));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
      assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application));
      fold (application_exactly
        c.application
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
                    st0.CS.cs_model.CS.model_config));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
                    st0.CS.cs_model.CS.model_control));
      assert (pure ((sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
                    st0.CS.cs_model.CS.model_failure));
      rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
        as (connection_config_exactly
          c.config
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
      rewrite (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure)
        as (control_exactly
          c.control
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
          (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);

      fold (connection_model_exactly
        c
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model);

      lemma_sent_key_update_state_evolves
        st0
        req
        (Ghost.reveal raw_sent);
      MR.update
        c.ghost_state
        (sent_key_update_state st0 req (Ghost.reveal raw_sent));
      fold (connection_exactly
        c
        (sent_key_update_state st0 req (Ghost.reveal raw_sent)));

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

fn server_try_send_key_update
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (req:M.key_update_request)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (server_sent_key_update_state
                  st0
                  req
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    27 <= B.length network_out_bytes /\
                    server_can_send_key_update
                      st0
                      req
                      raw_sent /\
                    (exists outer_fragment.
                       W.parse_record (Seq.slice network_out_bytes 0 27) ==
                         Some (T.Application_data, outer_fragment, 27)) /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 27))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)
{
  let ready = server_can_send_key_update_runtime c network_out_len;
  if ready {
    assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
    assert (pure (Some?
      st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic));
    assert (pure (U64.fits (st0.CS.cs_model.CS.model_record.CS.record_write.R.seq + 1)));
    assert (pure (27 <= SZ.v network_out_len));

    let mut key_update_plaintext = [| 0uy; 5sz |];
    write_key_update key_update_plaintext req;
    with key_update_plaintext_bytes.
      assert (ArrPts.pts_to key_update_plaintext key_update_plaintext_bytes);
    assert (pure (Seq.equal key_update_plaintext_bytes (key_update_fragment req)));
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
        { R.content_type = T.Application_data;
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
        T.Application_data
        1));
      assert (pure (CS.legal_event
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        })));
      assert (pure (CS.protected_record_count
        CL.Sent
        (M.TlsKeyUpdate req) == 1));
      assert (pure (CS.network_message_raw_delta_legal
        st0.CS.cs_model
        {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        }
        (Ghost.reveal raw_sent)));
      Seq.lemma_eq_intro B.empty B.empty;
      assert (pure (CS.event_raw_delta_legal
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
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
        (Model.key_update_fragment req)));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        (Model.key_update_fragment req);
      assert (pure (Seq.equal
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req])));
      Seq.lemma_eq_elim
        key_update_plaintext_bytes
        (B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req]);
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req];
        })));
      W.lemma_serialize_tls_message_key_update req;
      assert (pure (
        TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate req) ==
        W.serialize_plaintext {
          M.content_type = T.Handshake;
          M.fragment = B.of_list [24uy; 0uy; 0uy; 1uy; W.key_update_request_byte req];
        }));
      assert (pure (Seq.equal
        inner_plaintext_bytes
        (TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
          (M.TlsKeyUpdate req))));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      assert (pure (Seq.equal
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len))));
      Seq.lemma_eq_elim
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      Seq.lemma_eq_elim
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))
        (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v ciphertext_len));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_out_bytes 0 (SZ.v written)))));
      Seq.lemma_eq_elim
        (Ghost.reveal raw_sent)
        (Seq.slice network_out_bytes 0 (SZ.v written));
      assert (pure (Seq.equal
        aad_bytes
        (TLS13.Spec.StateMachine.Canonical.record_header_aad (Ghost.reveal raw_sent))));
      CSL.lemma_sent_event_seal_projection_intro
        st0.CS.cs_model
        (M.TlsKeyUpdate req)
        (Ghost.reveal raw_sent)
        aad_bytes
        inner_plaintext_bytes
        ciphertext_bytes;
      assert (pure (TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
        st0.CS.cs_model
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsKeyUpdate req;
        })
        (Ghost.reveal raw_sent)));
      assert (pure (server_can_send_key_update
        st0
        req
        (Ghost.reveal raw_sent)));

      unfold (handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake);
      with cv_verified server_finished_verified. _;
      unfold (key_schedule_exactly
        c.handshake.keys
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys);
      unfold (traffic_key_material_exactly
        c.handshake.keys.server_application_traffic
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
      with old_present old_secret old_alg old_key old_iv. _;
      lemma_traffic_key_material_match_present_of_some
        old_present
        old_secret
        old_alg
        old_key
        old_iv
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic;
      assert (pure (old_present));
      assert (pure (st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic ==
        Some {
          CS.traffic_secret = old_secret;
          CS.traffic_alg = old_alg;
          CS.traffic_key = CryptoSpec.logical_key old_alg old_key;
          CS.traffic_iv = old_iv;
        }));
      let old_material = Ghost.hide (Some?.v
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
      assert (pure ((Ghost.reveal old_material).CS.traffic_secret == old_secret));
      let rotate_alg = !c.handshake.keys.server_application_traffic.alg;
      assert (pure (rotate_alg == old_alg));
      assert (pure (CryptoSpec.aead_key_len rotate_alg == B.length (Ghost.reveal old_material).CS.traffic_key));

      V.to_array_pts_to c.handshake.keys.server_application_traffic.traffic_secret;
      let mut traffic_secret_out = [| 0uy; 32sz |];
      KS.application_traffic_secret_update
        (V.vec_to_array c.handshake.keys.server_application_traffic.traffic_secret)
        traffic_secret_out;
      V.to_vec_pts_to c.handshake.keys.server_application_traffic.traffic_secret;
      with traffic_secret_bytes. assert (ArrPts.pts_to traffic_secret_out traffic_secret_bytes);
      assert (pure (traffic_secret_bytes ==
        K.application_traffic_secret_update old_secret));

      fold (traffic_key_material_exactly
        c.handshake.keys.server_application_traffic
        st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);

      let mut traffic_key_out = [| 0uy; 32sz |];
      KS.derive_traffic_key traffic_secret_out rotate_alg traffic_key_out;
      let mut traffic_iv_out = [| 0uy; 12sz |];
      KS.derive_traffic_iv traffic_secret_out traffic_iv_out;
      with traffic_key_bytes. assert (ArrPts.pts_to traffic_key_out traffic_key_bytes);
      with traffic_iv_bytes. assert (ArrPts.pts_to traffic_iv_out traffic_iv_bytes);

      let traffic_secret = Ghost.hide traffic_secret_bytes;
      let material = Ghost.hide (CS.traffic_key_material_for_secret (rotate_alg) (Ghost.reveal traffic_secret));
      assert (pure ((Ghost.reveal material).CS.traffic_alg == rotate_alg));
      assert (pure ((Ghost.reveal material).CS.traffic_secret == traffic_secret_bytes));
      assert (pure (Seq.equal traffic_key_bytes (TLS13.Crypto.Spec.pad_key_32 (Ghost.reveal material).CS.traffic_key)));
      assert (pure ((Ghost.reveal material).CS.traffic_iv == traffic_iv_bytes));
      assert (pure (Ghost.reveal material == CS.updated_traffic_key_material (Ghost.reveal old_material)));

      store_traffic_key_material
        c.handshake.keys.server_application_traffic
        traffic_secret_out
        rotate_alg
        traffic_key_out
        traffic_iv_out
        #material;

      fold (key_schedule_exactly
        c.handshake.keys
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_keys);

      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_start));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_buffers));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
                    st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));

      rewrite (handshake_start_exactly
        c.handshake.start
        st0.CS.cs_model.CS.model_handshake.CS.hs_start)
        as (handshake_start_exactly
          c.handshake.start
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_start);
      unfold (handshake_messages_exactly c.handshake.messages st0.CS.cs_model.CS.model_handshake);
      rewrite (client_hello_metadata_exactly
        c.handshake.messages.client_hello_has_server_name
        c.handshake.messages.client_hello_server_name_len
        c.handshake.messages.client_hello_cipher_suites_len
        c.handshake.messages.client_hello_signature_schemes_len
        c.handshake.messages.client_hello_session_id_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello) as
        (client_hello_metadata_exactly
          c.handshake.messages.client_hello_has_server_name
          c.handshake.messages.client_hello_server_name_len
          c.handshake.messages.client_hello_cipher_suites_len
          c.handshake.messages.client_hello_signature_schemes_len
          c.handshake.messages.client_hello_session_id_len
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_client_hello);
      fold (handshake_messages_exactly
        c.handshake.messages
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      rewrite (server_selection_presence_exactly
        c.handshake.server_selection_present
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection) as
        (server_selection_presence_exactly
          c.handshake.server_selection_present
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_selection);
      unfold (server_key_share_exactly c.handshake.server_key_share st0.CS.cs_model.CS.model_handshake);
      fold (server_key_share_exactly
        c.handshake.server_key_share
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);
      rewrite (peer_exactly
        c.handshake.validated_peer
        st0.CS.cs_model.CS.model_handshake.CS.hs_validated_peer)
        as (peer_exactly
          c.handshake.validated_peer
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_validated_peer);
      rewrite (sized_bytes_exactly
        c.handshake.transcript
        max_transcript_len
        st0.CS.cs_model.CS.model_handshake.CS.hs_transcript)
        as (sized_bytes_exactly
          c.handshake.transcript
          max_transcript_len
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_transcript);
      rewrite (handshake_buffers_exactly
        c.handshake.buffers
        st0.CS.cs_model.CS.model_handshake.CS.hs_buffers)
        as (handshake_buffers_exactly
          c.handshake.buffers
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_buffers);
      assert (pure (cv_verified ==
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified));
      assert (pure (server_finished_verified ==
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified));
      fold (handshake_exactly
        c.handshake
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_handshake);

      Rec.install_application_keys_runtime c.records.write traffic_key_out rotate_alg (Ghost.hide (Ghost.reveal material).CS.traffic_key) traffic_iv_out;
      assert (pure (R.install_keys
        (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
        R.Application
        rotate_alg (Ghost.reveal material).CS.traffic_key
        (Ghost.reveal material).CS.traffic_iv ==
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write));
      rewrite (Rec.is_record_state
        c.records.write
        (R.install_keys
          (R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write)
          R.Application
          rotate_alg (Ghost.reveal material).CS.traffic_key
          (Ghost.reveal material).CS.traffic_iv))
        as (Rec.is_record_state
          c.records.write
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_write);
      rewrite (Rec.is_record_state c.records.read st0.CS.cs_model.CS.model_record.CS.record_read)
        as (Rec.is_record_state
          c.records.read
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record.CS.record_read);
      fold (record_layer_exactly
        c.records
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_record);

      unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
      with source_offset pending_response. _;
      let cur_pending = !c.application.key_update_response_pending;
      let new_pending = key_update_clears_pending req cur_pending;
      c.application.key_update_response_pending := new_pending;
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_key_update_response_pending == new_pending));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                    st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
      assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application));
      fold (application_exactly
        c.application
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_application);

      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config ==
                    st0.CS.cs_model.CS.model_config));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control ==
                    st0.CS.cs_model.CS.model_control));
      assert (pure ((server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure ==
                    st0.CS.cs_model.CS.model_failure));
      rewrite (connection_config_exactly c.config st0.CS.cs_model.CS.model_config)
        as (connection_config_exactly
          c.config
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_config);
      rewrite (control_exactly
        c.control
        st0.CS.cs_model.CS.model_control
        st0.CS.cs_model.CS.model_failure)
        as (control_exactly
          c.control
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_control
          (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model.CS.model_failure);

      fold (connection_model_exactly
        c
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)).CS.cs_model);

      lemma_server_sent_key_update_state_evolves
        st0
        req
        (Ghost.reveal raw_sent);
      MR.update
        c.ghost_state
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent));
      fold (connection_exactly
        c
        (server_sent_key_update_state st0 req (Ghost.reveal raw_sent)));

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
