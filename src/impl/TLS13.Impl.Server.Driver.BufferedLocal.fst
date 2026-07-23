module TLS13.Impl.Server.Driver.BufferedLocal

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module IM = TLS13.Impl.Messages
module LR = TLS13.Impl.Server.Driver.LocalReady
module M = TLS13.Messages
module O = TLS13.OpenSSL
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

fn check_certificate_chain_nonempty
  (d:DS.buffered_driver)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len
  returns ok:bool
  ensures
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pure (ok ==> 1 <= B.length (Ghost.reveal 'certificate_chain))
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
  assert_norm (IM.max_certificate_chain_bytes == 32768);
  let chain_bytes = V.alloc 0uy 32768sz;
  with old_chain_bytes. assert (V.pts_to chain_bytes old_chain_bytes);
  assert (pure (V.is_full_vec chain_bytes));
  assert (pure (B.length old_chain_bytes == 32768));
  V.to_array_pts_to chain_bytes;
  let copy_result =
    O.copy_server_certificate_chain
      d.buffered_driver_credentials
      (V.vec_to_array chain_bytes)
      32768sz;
  V.to_vec_pts_to chain_bytes;
  V.free chain_bytes;
  fold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  fold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  match copy_result {
    None -> { false }
    Some written -> { SZ.gt written 0sz }
  }
}

fn process_empty_local_event_once
  (d:DS.buffered_driver)
  (kind:ST.local_event_kind)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      BN.local_event_ready
        'st0
        kind
        (Ghost.reveal 'empty_payload_bytes)
        (Ghost.reveal 'certificate_chain)
        (Ghost.reveal 'credential_identity))
  returns status:local_status
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)
{
  let result =
    BN.process_local_event
      d
      kind
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  if (result.BN.local_write_resp.ST.status = ST.StepOk) {
    LocalProcessed
  } else {
    LocalStepFailed
  }
}

fn process_ready_empty_local_action_once
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len)
  returns status:local_status
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)
{
  assert (pure (Seq.equal
    (Ghost.reveal 'empty_payload_bytes)
    B.empty));
  Seq.lemma_eq_elim
    (Ghost.reveal 'empty_payload_bytes)
    B.empty;
  unfold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d 'st0 'certificate_chain 'credential_identity
      'buffered 'buffered_len model received committed sent);
  unfold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  assert (pure (ST.server_state_correct 'st0));
  let action = S.next_local_action d.buffered_driver_server;
  assert (pure (ST.next_local_action_sound 'st0 action));
  fold (DS.buffered_driver_indexed
    d 'st0 'certificate_chain 'credential_identity
    'buffered 'buffered_len model received committed sent);
  fold (DS.buffered_driver_exactly
    d 'st0 'certificate_chain 'credential_identity 'buffered 'buffered_len);
  if action.ST.next_local_ready {
    assert (pure (action.ST.next_local_ready == true));
    LR.lemma_internal_action_ready_with_credentials
      'st0
      action
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity);
    match action.ST.next_local_kind {
      ST.LocalInstallServerHandshakeTrafficKeys -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalInstallClientHandshakeTrafficKeys -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalInstallServerApplicationTrafficKeys -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalInstallClientApplicationTrafficKeys -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalSendEncryptedExtensions -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalSendServerFinished -> {
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalSendCertificate -> {
        assert (pure (ST.server_local_event_input_ready
          'st0 action.ST.next_local_kind B.empty));
        ST.server_local_event_input_ready_with_state_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity);
        assert (pure (B.length (Ghost.reveal 'certificate_chain) <=
          Bounds.max_server_certificate_chain_len));
        let nonempty = check_certificate_chain_nonempty d;
        if nonempty {
          assert (pure (1 <= B.length (Ghost.reveal 'certificate_chain)));
          SS.lemma_mk_cert_witness_bytesize
            (Ghost.reveal 'certificate_chain);
          assert (pure (BN.local_event_ready
            'st0
            action.ST.next_local_kind
            B.empty
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity)));
          process_empty_local_event_once
            d
            action.ST.next_local_kind
            empty_payload
            network_out
            network_out_len
            app_out
            app_out_len
        } else {
          LocalStepFailed
        }
      }
      ST.LocalSignCertificateVerify -> {
        LR.lemma_sign_certificate_verify_ready
          'st0
          action
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity);
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalSendCertificateVerify -> {
        assert (pure (ST.server_local_event_input_ready
          'st0 action.ST.next_local_kind B.empty));
        LR.lemma_send_certificate_verify_transcript_bound 'st0;
        assert (pure (Some?
          'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
        SS.lemma_serialize_handshake_certificate_verify_len
          (Some?.v
            'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      ST.LocalVerifyClientFinished -> {
        assert (pure (ST.server_local_event_input_ready
          'st0 action.ST.next_local_kind B.empty));
        LR.lemma_can_verify_client_finished 'st0;
        assert (pure (BN.local_event_ready
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        process_empty_local_event_once
          d
          action.ST.next_local_kind
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
      }
      _ -> { LocalUnsupported }
    }
  } else {
    LocalNotReady
  }
}

fn rec drain_ready_empty_local_actions
  (d:DS.buffered_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      'buffered_len **
    pts_to empty_payload 'empty_payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'empty_payload_bytes == 0 /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len)
  returns result:drain_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len **
      pts_to empty_payload 'empty_payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len)
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    {
      drain_last = LocalNotReady;
      drain_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let status =
      process_ready_empty_local_action_once
        d
        empty_payload
        network_out
        network_out_len
        app_out
        app_out_len;
    match status {
      LocalProcessed -> {
        with st1 network_out_bytes app_out_bytes.
          assert (
            DS.buffered_driver_exactly
              d st1 'certificate_chain 'credential_identity
              'buffered 'buffered_len **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        drain_ready_empty_local_actions
          d
          empty_payload
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
      }
      LocalStepFailed -> {
        {
          drain_last = LocalStepFailed;
          drain_exhausted = false;
        }
      }
      LocalNotReady -> {
        {
          drain_last = LocalNotReady;
          drain_exhausted = false;
        }
      }
      LocalUnsupported -> {
        {
          drain_last = LocalUnsupported;
          drain_exhausted = false;
        }
      }
    }
  }
}
