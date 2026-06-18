module TLS13.Impl.Server.Auth

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CF = TLS13.Impl.ConnectionState.Fail
module H = TLS13.Handshake.Spec
module CLA = TLS13.Impl.ConnectionState.LocalAuth
module CLH = TLS13.Impl.ConnectionState.LocalHandshake
module CR = TLS13.Impl.ConnectionState.Repr
module IM = TLS13.Impl.Messages
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Ser = TLS13.Impl.Serializer
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Tr = TLS13.Transcript
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

fn process_local_unexpected_message
  (s:server)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0)
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  CF.mark_unexpected_message s;
  fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_unexpected_message_error));
  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.IllegalTransition;
  };
  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
  CM.lemma_local_fail_state_evolves 'st0 CM.tls_unexpected_message_error;
  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error);
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
  assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
  assert (pure (ST.server_end_to_end_invariant
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
  assert (pure (ST.unexpected_message_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    'old_network_out
    'old_app_out));
  resp
}

fn process_sign_certificate_verify
  (s:server)
  (creds:O.server_credentials)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           O.is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 'st0.CS.cs_model.CS.model_control ==
                   CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                 'st0.CS.cs_model.CS.model_config.CS.config_role ==
                   CS.ServerEndpoint /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None /\
                 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
                  | Some selection ->
                    selection.CS.server_selected_signature_scheme ==
                      T.RsaPssRsaeSha256 /\
                    selection.CS.server_selected_credential ==
                      Ghost.reveal 'credential_identity /\
                    CS.signature_scheme_offered
                      'st0.CS.cs_model.CS.model_config.CS.config_signature_schemes
                      T.RsaPssRsaeSha256
                  | None -> False))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          O.is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSignCertificateVerify
                  B.empty
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  unfold (CR.connection_model_exactly s 'st0.CS.cs_model);
  unfold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  with cv_verified server_finished_verified. _;
  unfold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  with old_transcript_storage old_transcript_len. _;
  let transcript_len = !s.handshake.transcript.len;
  assert (pure (transcript_len == old_transcript_len));
  assert (pure (SZ.v transcript_len ==
    B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (CR.byte_prefix_matches
    old_transcript_storage
    transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));
  assert (pure (Seq.equal
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len))));
  Seq.lemma_eq_intro
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript
    (Seq.slice old_transcript_storage 0 (SZ.v transcript_len));

  V.to_array_pts_to s.handshake.transcript.bytes;
  let mut transcript_hash = [| 0uy; 32sz |];
  Crypto.sha256_prefix
    (V.vec_to_array s.handshake.transcript.bytes)
    transcript_len
    transcript_hash;
  V.to_vec_pts_to s.handshake.transcript.bytes;
  with transcript_hash_bytes. assert (pts_to transcript_hash transcript_hash_bytes);
  assert (pure (transcript_hash_bytes ==
    Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript));

  let mut certificate_verify_input = [| 0uy; 130sz |];
  Ser.build_server_certificate_verify_input
    transcript_hash
    certificate_verify_input
    130sz;
  with certificate_verify_input_bytes.
    assert (pts_to certificate_verify_input certificate_verify_input_bytes);
  assert (pure (B.length certificate_verify_input_bytes == 130));
  assert (pure (B.length transcript_hash_bytes == 32));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  W.lemma_serialize_server_certificate_verify_input_len32
    (Ghost.reveal transcript_hash_bytes);
  assert (pure (Seq.equal
    (W.serialize_server_certificate_verify_input (Ghost.reveal transcript_hash_bytes))
    (H.certificate_verify_input (Ghost.reveal transcript_hash_bytes))));
  assert (pure (Seq.equal
    (Ghost.reveal certificate_verify_input_bytes)
    (H.certificate_verify_input
      (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
  Seq.lemma_len_slice certificate_verify_input_bytes 0 130;
  Seq.lemma_eq_intro
    certificate_verify_input_bytes
    (Seq.slice certificate_verify_input_bytes 0 130);

  fold (CR.sized_bytes_exactly
    s.handshake.transcript
    Bounds.max_transcript_len
    'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript);
  fold (CR.handshake_exactly s.handshake 'st0.CS.cs_model.CS.model_handshake);
  fold (CR.connection_model_exactly s 'st0.CS.cs_model);
  fold (connection_exactly s 'st0);

  assert_norm (IM.max_signature_len == 4096);
  let signature_vec = V.alloc 0uy 4096sz;
  with old_signature_bytes. assert (V.pts_to signature_vec old_signature_bytes);
  assert (pure (V.is_full_vec signature_vec));
  assert (pure (V.length signature_vec == IM.max_signature_len));
  assert (pure (B.length old_signature_bytes == IM.max_signature_len));
  V.to_array_pts_to signature_vec;
  let sign_result =
    O.sign_certificate_verify
      creds
      certificate_verify_input
      130sz
      (V.vec_to_array signature_vec)
      4096sz;
  match sign_result {
    None -> {
      V.to_vec_pts_to signature_vec;
      V.free signature_vec;
      let mut empty_payload = [| 0uy; 0sz |];
      process_local_unexpected_message
        s
        ST.LocalSignCertificateVerify
        empty_payload
        0sz
        network_out
        network_out_len
        app_out
        app_out_len
    }
    Some signature_len -> {
      with signature_bytes.
        assert (pts_to (V.vec_to_array signature_vec) signature_bytes);
      assert (pure (B.length signature_bytes == 4096));
      assert (pure (SZ.v signature_len <= 4096));
      assert (pure (SZ.v signature_len <= B.length signature_bytes));
      Seq.lemma_len_slice signature_bytes 0 (SZ.v signature_len);
      let signature : erased B.bytes =
        Ghost.hide (Seq.slice signature_bytes 0 (SZ.v signature_len));
      assert (pure (Seq.equal
        (Ghost.reveal signature)
        (Seq.slice signature_bytes 0 (SZ.v signature_len))));
      assert (pure (B.length (Ghost.reveal signature) == SZ.v signature_len));
      assert (pure (TLS13.Crypto.Spec.verify_signature
        T.RsaPssRsaeSha256
        (Ghost.reveal 'credential_identity)
        (Seq.slice (Ghost.reveal certificate_verify_input_bytes) 0 130)
        (Ghost.reveal signature)));
      assert (pure (Seq.equal
        (Seq.slice (Ghost.reveal certificate_verify_input_bytes) 0 130)
        (H.certificate_verify_input
          (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))));
      assert (pure (TLS13.Crypto.Spec.verify_signature
        T.RsaPssRsaeSha256
        (Ghost.reveal 'credential_identity)
        (H.certificate_verify_input
          (Tr.hash 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript))
        (Ghost.reveal signature)));
      let cv : erased M.certificate_verify = Ghost.hide {
        M.scheme = T.RsaPssRsaeSha256;
        M.signature = Ghost.reveal signature;
        M.body = B.empty;
      };
      let lcv = {
        IM.certificate_verify_scheme = 0x0804us;
        IM.certificate_verify_signature = signature_vec;
        IM.certificate_verify_signature_len = signature_len;
      };
      V.to_vec_pts_to signature_vec;
      assert (pure (lcv.IM.certificate_verify_signature == signature_vec));
      assert (pure (lcv.IM.certificate_verify_signature_len == signature_len));
      assert (pure (lcv.IM.certificate_verify_scheme == 0x0804us));
      rewrite (V.pts_to signature_vec signature_bytes)
        as (V.pts_to lcv.IM.certificate_verify_signature signature_bytes);
      assert_norm (IM.signature_scheme_matches 0x0804us T.RsaPssRsaeSha256);
      assert (pure (IM.byte_prefix_matches
        signature_bytes
        signature_len
        (Ghost.reveal cv).M.signature));
      fold (IM.is_valid_certificate_verify lcv (Ghost.reveal cv));

      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))));
      assert (pure (CM.can_sign_certificate_verify 'st0 (Ghost.reveal cv)));
      unfold (connection_exactly s 'st0);
      CLH.mark_signed_certificate_verify
        s
        lcv
        #cv;
      fold (connection_exactly s (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)));

      let resp = {
        ST.network_out_len = 0sz;
        ST.app_out_len = 0sz;
        ST.status = ST.StepOk;
      };
      let delta = Ghost.hide {
        CS.delta_event =
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv));
        CS.delta_raw_sent = B.empty;
        CS.delta_raw_received = B.empty;
      };
      CM.lemma_signed_certificate_verify_state_evolves 'st0 (Ghost.reveal cv);
      assert (pure (CS.legal_connection_delta
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      CSL.lemma_legal_connection_delta_full_log_consistent_for_role
        CS.ServerEndpoint
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_raw_event_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_connection_state_protected_raw_segmented_replay
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        'st0
        (Ghost.reveal delta)
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv));
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      Seq.lemma_len_slice 'old_app_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
      assert (pure ((CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure ((CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config.CS.config_role ==
        CS.ServerEndpoint));
      assert (pure (Some?
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv)).CS.cs_model.CS.model_config.CS.config_server));
      assert (pure (ST.server_state_correct
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.server_raw_to_message_replay_consistent
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.server_end_to_end_invariant
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))));
      assert (pure (ST.legal_response_for_event
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.legal_local_response
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        (CS.ConnLocalEvent (CS.LocalSignCertificateVerify (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.legal_handled_local_response
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (ST.server_local_event_end_to_end_correct
        'st0
        (CM.signed_certificate_verify_state 'st0 (Ghost.reveal cv))
        resp
        ST.LocalSignCertificateVerify
        B.empty
        'old_network_out
        'old_app_out));
      resp
    }
  }
}

fn process_verify_client_finished
  (s:server)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
                 CM.can_verify_client_finished
                   'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
  returns resp:ST.server_response
  ensures exists* network_out_bytes app_out_bytes fin.
          connection_exactly
            s
            (CM.verified_client_finished_state 'st0 fin) **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
                  Some fin /\
                ST.server_local_event_end_to_end_correct
                        'st0
                        (CM.verified_client_finished_state 'st0 fin)
                        resp
                        ST.LocalVerifyClientFinished
                        B.empty
                        network_out_bytes
                        app_out_bytes)
{
  let fin = Ghost.hide
    (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
    Some (Ghost.reveal fin)));
  assert (pure (CM.can_verify_client_finished 'st0 (Ghost.reveal fin)));
  W.lemma_serialize_finished_len (Ghost.reveal fin);
  assert (pure (B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    Bounds.max_transcript_len));
  unfold (connection_exactly s 'st0);
  CLA.mark_verified_stored_client_finished
    s
    #fin;
  fold (connection_exactly
    s
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin)));

  let resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.StepOk;
  };

  let delta = Ghost.hide {
    CS.delta_event =
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin));
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  };
  CM.lemma_verified_client_finished_state_evolves 'st0 (Ghost.reveal fin);
  assert (pure (CS.legal_connection_delta
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));

  CSL.lemma_legal_connection_delta_full_log_consistent_for_role
    CS.ServerEndpoint
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_raw_event_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_connection_state_protected_raw_segmented_replay
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));
  CSL.lemma_legal_connection_delta_received_decode_replay_consistent
    'st0
    (Ghost.reveal delta)
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin));

  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  Seq.lemma_len_slice 'old_app_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);

  assert (pure ((CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure ((CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin)).CS.cs_model.CS.model_config.CS.config_server));
  assert (pure (ST.server_state_correct
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));
  assert (pure (ST.server_raw_to_message_replay_consistent
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));
  assert (pure (ST.server_end_to_end_invariant
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))));

  assert (pure (ST.legal_response_for_event
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    (CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_local_response
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    (CS.ConnLocalEvent (CS.LocalVerifyClientFinished (Ghost.reveal fin)))
    B.empty
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.legal_handled_local_response
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    'old_network_out
    'old_app_out));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    (CM.verified_client_finished_state 'st0 (Ghost.reveal fin))
    resp
    ST.LocalVerifyClientFinished
    B.empty
    'old_network_out
    'old_app_out));
  resp
}
