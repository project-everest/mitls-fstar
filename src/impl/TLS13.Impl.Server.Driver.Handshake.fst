module TLS13.Impl.Server.Driver.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module ID = FStar.IndefiniteDescription
module DN = TLS13.Impl.Server.Driver.Network
module IO = TLS13.IO
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

open TLS13.Impl.Server.Driver.State
open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local

let lemma_select_server_parameters_ready_payload_irrelevant
  (st:CS.connection_state)
  (payload0:B.bytes)
  (payload1:B.bytes)
  : Lemma
      (requires
        B.length payload0 == 64 /\
        B.length payload1 == 64 /\
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload0)
      (ensures
        ST.server_local_event_input_ready
          st
          ST.LocalSelectServerParameters
          payload1)
=
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (CR.server_selection_absent st.CS.cs_model.CS.model_handshake);
  assert (Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  assert (Some? st.CS.cs_model.CS.model_config.CS.config_server);
  let ch = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
  let cfg = Some?.v st.CS.cs_model.CS.model_config.CS.config_server in
  let selection0 = {
    CS.server_selected_client_hello = ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = CL.raw_slice payload0 0 32;
    CS.server_key_share_private = Some (CL.raw_slice payload0 32 64);
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private (CL.raw_slice payload0 32 64);
    CS.server_selected_credential = cfg.CS.server_credential_identity;
  } in
  let selection1 = {
    CS.server_selected_client_hello = ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = CL.raw_slice payload1 0 32;
    CS.server_key_share_private = Some (CL.raw_slice payload1 32 64);
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private (CL.raw_slice payload1 32 64);
    CS.server_selected_credential = cfg.CS.server_credential_identity;
  } in
  assert (CM.can_select_server_parameters st selection0);
  assert (CS.server_selection_acceptable cfg selection0);
  assert (CS.cipher_suite_offered
    cfg.CS.server_supported_cipher_suites
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.cipher_suite_offered
    ch.M.cipher_suites
    T.TLS_CHACHA20_POLY1305_SHA256);
  assert (CS.named_group_offered
    cfg.CS.server_supported_groups
    T.X25519);
  assert (CS.signature_scheme_offered
    cfg.CS.server_allowed_signature_schemes
    T.RsaPssRsaeSha256);
  assert (CS.signature_scheme_offered
    ch.M.signature_schemes
    T.RsaPssRsaeSha256);
  assert (CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name);
  assert (CS.server_selection_key_share_consistent selection1);
  assert (CS.server_selection_acceptable cfg selection1);
  assert (CS.legal_event
    st.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1)));
  assert (CM.can_select_server_parameters st selection1)

let lemma_select_derive_success_server_hello_ready
  (st0 st2:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : Lemma
      (requires
       B.length payload == 64 /\
       resp.ST.status == ST.StepOk /\
       server_driver_select_derive_from_payload_success_correct
         st0 st2 resp payload /\
       st2.CS.cs_model.CS.model_control ==
         CS.ControlHandshaking CS.HsClientHelloReceived /\
       st2.CS.cs_model.CS.model_config.CS.config_role ==
         CS.ServerEndpoint /\
       Some? st2.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None /\
       Some? st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
       B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
         Bounds.max_transcript_len)
      (ensures
       ST.server_local_event_input_ready
         st2
         ST.LocalSendServerHello
         payload)
=
  assert (CL.raw_slice payload 0 32 == Seq.slice payload 0 32);
  assert (CL.raw_slice payload 32 64 == Seq.slice payload 32 64);
  Seq.lemma_len_slice payload 0 32;
  Seq.lemma_len_slice payload 32 64;
  assert (B.length (CL.raw_slice payload 0 32) == 32);
  assert (B.length (CL.raw_slice payload 32 64) == 32);
  let server_random = CL.raw_slice payload 0 32 in
  let server_private_key = CL.raw_slice payload 32 64 in
  let sh = {
    M.random = server_random;
    M.key_share = CryptoSpec.x25519_public_from_private server_private_key;
    M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
  } in
  assert (exists st1 shared.
    server_driver_selection_from_payload_correct st0 st1 payload /\
    st2 == CM.derived_shared_secret_state st1 shared /\
    (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
     | Some ch ->
      CryptoSpec.x25519_shared
        server_private_key
        ch.M.key_share == Some shared
     | None -> False));
  let st1 =
    ID.indefinite_description_ghost
      CS.connection_state
      (fun st1 -> exists shared.
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          CryptoSpec.x25519_shared
            server_private_key
            ch.M.key_share == Some shared
        | None -> False)) in
  let shared =
    ID.indefinite_description_ghost
      CryptoSpec.x25519_shared_secret
      (fun shared ->
       server_driver_selection_from_payload_correct st0 st1 payload /\
       st2 == CM.derived_shared_secret_state st1 shared /\
       (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
        | Some ch ->
          CryptoSpec.x25519_shared
            server_private_key
            ch.M.key_share == Some shared
        | None -> False)) in
  assert (server_driver_selection_from_payload_correct st0 st1 payload);
  assert (st2 == CM.derived_shared_secret_state st1 shared);
  assert (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
               st0.CS.cs_model.CS.model_config.CS.config_server with
    | Some ch, Some cfg ->
      let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
       CS.server_selected_group = T.X25519;
       CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
       CS.server_random = server_random;
       CS.server_key_share_private = Some server_private_key;
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private server_private_key;
       CS.server_selected_credential = cfg.CS.server_credential_identity;
      } in
      st1 == CM.selected_server_parameters_state st0 selection
    | _ -> False);
  assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  assert (Some? st0.CS.cs_model.CS.model_config.CS.config_server);
  let selected_ch = Some?.v st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
  let server_cfg = Some?.v st0.CS.cs_model.CS.model_config.CS.config_server in
  let selection = {
    CS.server_selected_client_hello = selected_ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = server_random;
    CS.server_key_share_private = Some server_private_key;
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private server_private_key;
    CS.server_selected_credential = server_cfg.CS.server_credential_identity;
  } in
  assert (st1 == CM.selected_server_parameters_state st0 selection);
  assert (st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    Some selection);
  assert (Some?.v st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
    selection);
  assert (Seq.equal selection.CS.server_random server_random);
  assert (Some? selection.CS.server_key_share_private);
  assert (Seq.equal (Some?.v selection.CS.server_key_share_private) server_private_key);
  assert (CS.server_selection_key_share_consistent selection);
  assert (CS.server_hello_matches_selection selection sh);
  W.lemma_serialize_server_hello_len sh;
  assert (B.length (W.serialize_handshake (M.ServerHello sh)) == 90);
  assert (
    B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript +
      B.length (W.serialize_handshake (M.ServerHello sh)) <=
      Bounds.max_transcript_len);
  assert (CS.legal_event
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    }));
  assert (CS.event_raw_delta_legal
    st2.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    })
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh)))
    B.empty);
  assert (CM.can_send_server_hello
    st2
    sh
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello sh))));
  assert (ST.server_local_event_input_ready
    st2
    ST.LocalSendServerHello
    payload)

fn generate_server_material_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns ok:bool
  ensures server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_material_payload;
  let ok =
    Crypto.random_bytes
      (V.vec_to_array d.server_driver_material_payload)
      driver_material_capacity;
  with material_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_material_payload) material_bytes);
  assert (pure (B.length material_bytes == SZ.v driver_material_capacity));
  V.to_vec_pts_to d.server_driver_material_payload;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  ok
}

fn select_default_server_parameters_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready
             'st0
             ST.LocalSelectServerParameters
             (Seq.create 64 0uy))
  returns resp:ST.server_response
  ensures exists* st1.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_material_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  with material_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_material_payload) material_bytes);
  assert (pure (B.length material_bytes == SZ.v driver_material_capacity));
  assert (pure (B.length material_bytes == 64));
  lemma_select_server_parameters_ready_payload_irrelevant
    'st0
    (Seq.create 64 0uy)
    material_bytes;
  assert (pure (ST.server_local_event_input_ready
    'st0
    ST.LocalSelectServerParameters
    material_bytes));

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    (V.vec_to_array d.server_driver_material_payload)
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_random_bytes == 32));
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice material_bytes 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64)));
  assert (pure (CR.server_selection_absent
    'st0.CS.cs_model.CS.model_handshake));
  assert (pure (Some?
    'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (Some?
    'st0.CS.cs_model.CS.model_config.CS.config_server));
  let selected_ch =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  let server_cfg =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
  let selection = Ghost.hide {
    CS.server_selected_client_hello = Ghost.reveal selected_ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = server_random_bytes;
    CS.server_key_share_private = Some server_private_key_bytes;
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private server_private_key_bytes;
    CS.server_selected_credential =
      (Ghost.reveal server_cfg).CS.server_credential_identity;
  };
  assert (pure (CM.can_select_server_parameters
    'st0
    (Ghost.reveal selection)));

  let resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.server_driver_server
      server_random
      server_private_key
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (st1 ==
    CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)));
  assert (pure (st1.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st1.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some (Ghost.reveal selection).CS.server_selected_client_hello));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      Some (Ghost.reveal selection)));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (
    Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      Ghost.reveal selection));
  assert (pure (CS.server_selection_key_share_consistent
    (Ghost.reveal selection)));
  assert (pure (Some?
    (Ghost.reveal selection).CS.server_key_share_private));
  assert (pure (
    Some?.v (Ghost.reveal selection).CS.server_key_share_private ==
      server_private_key_bytes));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice material_bytes 32 64);
  assert (pure (
    Some?.v (Ghost.reveal selection).CS.server_key_share_private ==
      CL.raw_slice material_bytes 32 64));
  assert (pure (ST.server_end_to_end_invariant st1));

  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (server_driver_wire_logs_match
    st1
    'received
    'sent
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_material_payload;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
}

fn select_default_server_parameters_from_payload_once
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
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSelectServerParameters
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            'sent **
          pts_to payload 'payload_bytes **
          pure (server_driver_selection_from_payload_correct
            'st0
            st1
            (Ghost.reveal 'payload_bytes))
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_random_bytes == 32));
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  assert (pure (CR.server_selection_absent
    'st0.CS.cs_model.CS.model_handshake));
  assert (pure (Some?
    'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (Some?
    'st0.CS.cs_model.CS.model_config.CS.config_server));
  let selected_ch =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
  let server_cfg =
    Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_config.CS.config_server);
  let selection = Ghost.hide {
    CS.server_selected_client_hello = Ghost.reveal selected_ch;
    CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
    CS.server_selected_group = T.X25519;
    CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
    CS.server_random = server_random_bytes;
    CS.server_key_share_private = Some server_private_key_bytes;
    CS.server_key_share_public =
      CryptoSpec.x25519_public_from_private server_private_key_bytes;
    CS.server_selected_credential =
      (Ghost.reveal server_cfg).CS.server_credential_identity;
  };
  assert (pure (CM.can_select_server_parameters
    'st0
    (Ghost.reveal selection)));

  let resp =
    S.process_select_default_server_parameters_with_derived_public_from_private_array
      d.server_driver_server
      server_random
      server_private_key
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to server_random server_random_bytes **
      pts_to server_private_key server_private_key_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (st1 ==
    CM.selected_server_parameters_state 'st0 (Ghost.reveal selection)));
  assert (pure (st1.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived));
  assert (pure (st1.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      Some (Ghost.reveal selection).CS.server_selected_client_hello));
  assert (pure (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      Some (Ghost.reveal selection)));
  assert (pure (Some?
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
  assert (pure (
    Some?.v st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      Ghost.reveal selection));
  assert (pure (CS.server_selection_key_share_consistent
    (Ghost.reveal selection)));
  assert (pure (Some?
    (Ghost.reveal selection).CS.server_key_share_private));
  assert (pure (
    Some?.v (Ghost.reveal selection).CS.server_key_share_private ==
      server_private_key_bytes));
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  Seq.lemma_eq_elim
    server_random_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (server_driver_selection_from_payload_correct
    'st0
    st1
    (Ghost.reveal 'payload_bytes)));

  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (server_driver_wire_logs_match
    st1
    'received
    'sent
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
}

fn derive_shared_secret_from_payload_once
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
                 SZ.v payload_len == 32 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalDeriveSharedSecret
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            ST.LocalDeriveSharedSecret
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent' /\
           server_driver_derive_shared_secret_success_correct
            'st0
            st1
            resp
            (Ghost.reveal 'payload_bytes))
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  let resp =
    S.process_derive_shared_secret_from_private_array
      d.server_driver_server
      payload
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      pts_to payload 'payload_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (SZ.v resp.ST.network_out_len <= B.length network_out_bytes));

  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let written =
    IO.write
      concrete_ch
      (V.vec_to_array d.server_driver_network_out)
      resp.ST.network_out_len;
  assert (pure (written == resp.ST.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  rewrite
    (IO.is_channel
      concrete_ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)))
    as
    (IO.is_channel
      ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (ST.response_network_out resp network_out_bytes)));
  let old_consumed =
    Ghost.hide (ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        server_driver_wire_logs_match_witness
          'st0
          (Ghost.reveal 'received)
          (Ghost.reveal 'sent)
          consumed
          buffered
          buffered_len));
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  assert (pure (Seq.equal
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (ST.response_network_out resp network_out_bytes))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    st1.CS.cs_wire_log.CL.raw_sent));
  assert (pure (server_driver_wire_logs_match_witness
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  assert (pure (server_driver_wire_logs_match
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)));
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append
      (Ghost.reveal 'sent)
      (ST.response_network_out resp network_out_bytes))));
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  assert (pure (server_driver_local_write_correct
    'st0
    st1
    resp
    ST.LocalDeriveSharedSecret
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))));
  assert (pure (server_driver_derive_shared_secret_success_correct
    'st0
    st1
    resp
    (Ghost.reveal 'payload_bytes)));
  resp
}

fn select_supported_server_parameters_from_payload_if_ready_once
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
                 SZ.v payload_len == 64 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some ch, Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.RsaPssRsaeSha256 /\
                    CS.sni_policy_accepts cfg.CS.server_sni_policy ch.M.server_name
                  | _, _ -> True))
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             exists* st1.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
               pts_to payload 'payload_bytes **
               pure (server_driver_selection_from_payload_correct
                 'st0
                 st1
                 (Ghost.reveal 'payload_bytes))
           | ServerDriverLocalNotReady ->
               server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
               pts_to payload 'payload_bytes
           | ServerDriverLocalExternalOrUnsupported ->
               pure False)
{
  assert (pure (B.length (Ghost.reveal 'payload_bytes) == 64));
  assert (pure (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32 ==
    Seq.slice (Ghost.reveal 'payload_bytes) 0 32));
  Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 0 32;
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32) == 32));
  assert (pure (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64 ==
    Seq.slice (Ghost.reveal 'payload_bytes) 32 64));
  Seq.lemma_len_slice (Ghost.reveal 'payload_bytes) 32 64;
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64) == 32));
  let server_random : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
  let server_private_key : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (Ghost.reveal server_random ==
    CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32));
  assert (pure (Ghost.reveal server_private_key ==
    CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64));

  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  rewrite (S.connection_exactly d.server_driver_server 'st0)
    as (CR.connection_exactly d.server_driver_server 'st0);
  let ready =
    CQ.can_select_supported_server_parameters_runtime
      d.server_driver_server
      #server_random
      #server_private_key;
  rewrite (CR.connection_exactly d.server_driver_server 'st0)
    as (S.connection_exactly d.server_driver_server 'st0);
  if ready {
    assert (pure (ready));
    assert (pure ('st0.CS.cs_model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (CR.server_selection_absent
      'st0.CS.cs_model.CS.model_handshake));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
    assert (pure (Some?
      'st0.CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                        'st0.CS.cs_model.CS.model_config.CS.config_server with
      | Some selected_ch, Some cfg ->
        let selection = {
          CS.server_selected_client_hello = selected_ch;
          CS.server_selected_cipher_suite =
            T.TLS_CHACHA20_POLY1305_SHA256;
          CS.server_selected_group = T.X25519;
          CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
          CS.server_random = Ghost.reveal server_random;
          CS.server_key_share_private = Some (Ghost.reveal server_private_key);
          CS.server_key_share_public =
            CryptoSpec.x25519_public_from_private
              (Ghost.reveal server_private_key);
          CS.server_selected_credential = cfg.CS.server_credential_identity;
        } in
        CM.can_select_server_parameters 'st0 selection
      | _, _ -> False));
    Seq.lemma_eq_elim
      (Ghost.reveal server_random)
      (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
    Seq.lemma_eq_elim
      (Ghost.reveal server_private_key)
      (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      (Ghost.reveal 'payload_bytes)));
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    let resp =
      select_default_server_parameters_from_payload_once
        d
        payload
        payload_len;
    with st1.
      assert (server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        'received
        'sent);
    assert (pure (server_driver_selection_from_payload_correct
      'st0
      st1
      (Ghost.reveal 'payload_bytes)));
    ServerDriverLocalProcessed
  } else {
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    ServerDriverLocalNotReady
  }
}

fn select_and_derive_shared_secret_from_payload_once
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
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSelectServerParameters
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st2 sent'.
          server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_select_derive_from_payload_success_correct
            'st0
            st2
            resp
            (Ghost.reveal 'payload_bytes))
{
  let _ =
    select_default_server_parameters_from_payload_once
      d
      payload
      payload_len;
  with st1.
    assert (
      server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        'received
        'sent **
      pts_to payload 'payload_bytes **
      pure (server_driver_selection_from_payload_correct
        'st0
        st1
        (Ghost.reveal 'payload_bytes)));

  let mut server_random = [| 0uy; 32sz |];
  let mut server_private_key = [| 0uy; 32sz |];
  Mat.copy_server_random_and_private_from_payload
    payload
    server_random
    server_private_key;
  with server_random_bytes. assert (pts_to server_random server_random_bytes);
  with server_private_key_bytes.
    assert (pts_to server_private_key server_private_key_bytes);
  assert (pure (B.length server_private_key_bytes == 32));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  let resp =
    derive_shared_secret_from_payload_once
      d
      server_private_key
      32sz;
  with st2 sent'.
    assert (
      server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        'received
        sent' **
      pts_to server_private_key server_private_key_bytes **
      pure (server_driver_local_write_correct
        st1
        st2
        resp
        ST.LocalDeriveSharedSecret
        server_private_key_bytes
        (Ghost.reveal 'sent)
        sent' /\
      server_driver_derive_shared_secret_success_correct
        st1
        st2
        resp
        server_private_key_bytes));
  assert (pure (Seq.equal
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
  Seq.lemma_eq_elim
    server_private_key_bytes
    (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
  assert (pure (server_driver_select_derive_from_payload_success_correct
    'st0
    st2
    resp
    (Ghost.reveal 'payload_bytes)));
  resp
}

fn send_server_hello_from_payload_once
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
                 SZ.v payload_len == 64 /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendServerHello
                   (Ghost.reveal 'payload_bytes))
 returns resp:ST.server_response
 ensures exists* st1 sent'.
         server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           'received
           sent' **
         pts_to payload 'payload_bytes **
         pure (server_driver_local_write_correct
           'st0
           st1
           resp
           ST.LocalSendServerHello
           (Ghost.reveal 'payload_bytes)
           (Ghost.reveal 'sent)
           sent' /\
         server_driver_send_server_hello_from_payload_success_correct
           'st0
           st1
           resp
           (Ghost.reveal 'payload_bytes))
{
 unfold (server_driver_connected
   d
   'st0
   'certificate_chain
   'credential_identity
   'received
   'sent);
 with ch buffered buffered_len.
   assert (Box.pts_to d.server_driver_channel (Some ch) **
           IO.is_channel ch 'received 'sent **
           server_driver_buffers d buffered buffered_len);
 assert (pure (ST.server_end_to_end_invariant 'st0));
 assert (pure (server_driver_wire_logs_match
   'st0
   'received
   'sent
   buffered
   buffered_len));

 unfold (server_driver_buffers d buffered buffered_len);
 with empty_payload raw network_out material cv_input signature app_out.
   assert (
     Box.pts_to d.server_driver_buffered_len buffered_len **
     V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
     V.pts_to d.server_driver_raw #1.0R raw **
     V.pts_to d.server_driver_network_out #1.0R network_out **
     V.pts_to d.server_driver_material_payload #1.0R material **
     V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
     V.pts_to d.server_driver_signature #1.0R signature **
     V.pts_to d.server_driver_app_out #1.0R app_out);
 V.to_array_pts_to d.server_driver_app_out;

 let mut server_random = [| 0uy; 32sz |];
 let mut server_private_key = [| 0uy; 32sz |];
 let mut server_hello_out = [| 0uy; 95sz |];
 Mat.copy_server_random_and_private_from_payload
   payload
   server_random
   server_private_key;
 with server_random_bytes server_private_key_bytes server_hello_out_bytes.
   assert (pts_to payload 'payload_bytes **
           pts_to server_random server_random_bytes **
           pts_to server_private_key server_private_key_bytes **
           pts_to server_hello_out server_hello_out_bytes **
           pts_to (V.vec_to_array d.server_driver_app_out) app_out);
 assert (pure (B.length server_random_bytes == 32));
 assert (pure (B.length server_private_key_bytes == 32));
 assert (pure (B.length server_hello_out_bytes == 95));
 assert (pure (Seq.equal
   server_random_bytes
   (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32)));
 assert (pure (Seq.equal
   server_private_key_bytes
   (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64)));
 Seq.lemma_eq_elim
   server_random_bytes
   (CL.raw_slice (Ghost.reveal 'payload_bytes) 0 32);
 Seq.lemma_eq_elim
   server_private_key_bytes
   (CL.raw_slice (Ghost.reveal 'payload_bytes) 32 64);
 assert (pure (let sh = {
     M.random = server_random_bytes;
     M.key_share =
       CryptoSpec.x25519_public_from_private server_private_key_bytes;
     M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
   } in
   CM.can_send_server_hello
     'st0
     sh
     (CS.serialized_cleartext_tls_message
       (M.TlsHandshake (M.ServerHello sh)))));

 let resp =
   S.process_send_server_hello_with_derived_public_from_private_array
     d.server_driver_server
     server_random
     server_private_key
     server_hello_out
     95sz
     (V.vec_to_array d.server_driver_app_out)
     driver_app_out_capacity;
 with st1 network_out_bytes app_out_bytes.
   assert (
     S.connection_exactly d.server_driver_server st1 **
     pts_to server_random server_random_bytes **
     pts_to server_private_key server_private_key_bytes **
     pts_to server_hello_out network_out_bytes **
     pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
 assert (pure (B.length network_out_bytes == 95));
 assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
 assert (pure (ST.server_local_event_end_to_end_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   B.empty
   network_out_bytes
   app_out_bytes));
 ST.lemma_local_send_server_hello_payload_irrelevant
   'st0
   st1
   resp
   B.empty
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes;
 assert (pure (ST.server_local_event_end_to_end_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes));
 assert (pure (ST.server_end_to_end_invariant st1));
 lemma_local_event_wire_lengths
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   network_out_bytes
   app_out_bytes;
 assert (pure (SZ.v resp.ST.network_out_len <= B.length network_out_bytes));

 let current_channel = Box.(!d.server_driver_channel);
 assert (pure (current_channel == Some ch));
 assert (pure (Some? current_channel));
 let concrete_ch = Some?.v current_channel;
 assert (pure (current_channel == Some concrete_ch));
 assert (pure (Some concrete_ch == Some ch));
 rewrite (IO.is_channel ch 'received 'sent) as
   (IO.is_channel concrete_ch 'received 'sent);
 let written =
   IO.write
     concrete_ch
     server_hello_out
     resp.ST.network_out_len;
 assert (pure (written == resp.ST.network_out_len));
 assert (pure (SZ.v written <= B.length network_out_bytes));
 rewrite
   (IO.is_channel
     concrete_ch
     'received
     (B.append
       (Ghost.reveal 'sent)
       (if SZ.v written <= B.length network_out_bytes
        then Seq.slice network_out_bytes 0 (SZ.v written)
        else B.empty)))
   as
   (IO.is_channel
     ch
     'received
     (B.append
       (Ghost.reveal 'sent)
       (if SZ.v written <= B.length network_out_bytes
        then Seq.slice network_out_bytes 0 (SZ.v written)
        else B.empty)));
 Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
 assert (pure (Seq.equal
   (if SZ.v written <= B.length network_out_bytes
    then Seq.slice network_out_bytes 0 (SZ.v written)
    else B.empty)
   (ST.response_network_out resp network_out_bytes)));
 let old_consumed =
   Ghost.hide (ID.indefinite_description_ghost
     B.bytes
     (fun consumed ->
       server_driver_wire_logs_match_witness
         'st0
         (Ghost.reveal 'received)
         (Ghost.reveal 'sent)
         consumed
         buffered
         buffered_len));
 assert (pure (server_driver_wire_logs_match_witness
   'st0
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent)
   (Ghost.reveal old_consumed)
   buffered
   buffered_len));
 assert (pure (Seq.equal
   (Ghost.reveal 'sent)
   'st0.CS.cs_wire_log.CL.raw_sent));
 Seq.lemma_eq_elim
   (Ghost.reveal 'sent)
   'st0.CS.cs_wire_log.CL.raw_sent;
 assert (pure (Seq.equal
   st1.CS.cs_wire_log.CL.raw_sent
   (B.append
     'st0.CS.cs_wire_log.CL.raw_sent
     (ST.response_network_out resp network_out_bytes))));
 assert (pure (Seq.equal
   st1.CS.cs_wire_log.CL.raw_received
   'st0.CS.cs_wire_log.CL.raw_received));
 Seq.lemma_eq_elim
   st1.CS.cs_wire_log.CL.raw_received
   'st0.CS.cs_wire_log.CL.raw_received;
 assert (pure (Seq.equal
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   st1.CS.cs_wire_log.CL.raw_sent));
 assert (pure (server_driver_wire_logs_match_witness
   st1
   (Ghost.reveal 'received)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   (Ghost.reveal old_consumed)
   buffered
   buffered_len));
 assert (pure (server_driver_wire_logs_match
   st1
   (Ghost.reveal 'received)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   buffered
   buffered_len));

 V.to_vec_pts_to d.server_driver_app_out;
 fold (server_driver_buffers d buffered buffered_len);
 fold (server_driver_connected
   d
   st1
   'certificate_chain
   'credential_identity
   'received
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty)));
 assert (pure (Seq.equal
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   (B.append
     (Ghost.reveal 'sent)
     (ST.response_network_out resp network_out_bytes))));
 lemma_server_driver_local_write_correct_intro
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))
   network_out_bytes
   app_out_bytes;
 assert (pure (server_driver_local_write_correct
   'st0
   st1
   resp
   ST.LocalSendServerHello
   (Ghost.reveal 'payload_bytes)
   (Ghost.reveal 'sent)
   (B.append
     (Ghost.reveal 'sent)
     (if SZ.v written <= B.length network_out_bytes
      then Seq.slice network_out_bytes 0 (SZ.v written)
      else B.empty))));
 assert (pure (server_driver_send_server_hello_from_payload_success_correct
   'st0
   st1
   resp
   (Ghost.reveal 'payload_bytes)));
 resp
}

fn select_derive_send_server_hello_from_payload_once
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
                SZ.v payload_len == 64 /\
                ST.server_local_event_input_ready
                  'st0
                  ST.LocalSelectServerParameters
                  (Ghost.reveal 'payload_bytes))
 returns result:server_driver_select_derive_server_hello_result
 ensures (match result with
          | ServerDriverSelectDeriveServerHelloOk ->
            exists* st3 sent_after_send.
              server_driver_connected
                d
                st3
                'certificate_chain
                'credential_identity
                'received
                sent_after_send **
              pts_to payload 'payload_bytes
          | ServerDriverSelectDeriveServerHelloDeriveFailed ->
            exists* st2 sent_after_derive.
              server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes
          | ServerDriverSelectDeriveServerHelloSendNotReady ->
            exists* st2 sent_after_derive.
              server_driver_connected
                d
                st2
                'certificate_chain
                'credential_identity
                'received
                sent_after_derive **
              pts_to payload 'payload_bytes)
{
 let derive_resp =
   select_and_derive_shared_secret_from_payload_once
     d
     payload
     payload_len;
 with st2 sent_after_derive.
   assert (
     server_driver_connected
       d
       st2
       'certificate_chain
       'credential_identity
       'received
       sent_after_derive **
     pts_to payload 'payload_bytes **
     pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes)));

 if (derive_resp.ST.status = ST.StepOk) {
   assert (pure (derive_resp.ST.status == ST.StepOk));
   unfold (server_driver_connected
     d
     st2
     'certificate_chain
     'credential_identity
     'received
     sent_after_derive);
   with ch2 buffered2 buffered_len2.
     assert (
       Box.pts_to d.server_driver_channel (Some ch2) **
       IO.is_channel ch2 'received sent_after_derive **
       server_driver_buffers d buffered2 buffered_len2);
   rewrite (S.connection_exactly d.server_driver_server st2)
     as (CR.connection_exactly d.server_driver_server st2);
   let ready =
     CQ.can_send_server_hello_runtime
       d.server_driver_server;
   rewrite (CR.connection_exactly d.server_driver_server st2)
     as (S.connection_exactly d.server_driver_server st2);
   fold (server_driver_connected
     d
     st2
     'certificate_chain
     'credential_identity
     'received
     sent_after_derive);
   if ready {
     assert (pure (ready));
     assert (pure (st2.CS.cs_model.CS.model_control ==
       CS.ControlHandshaking CS.HsClientHelloReceived));
     assert (pure (st2.CS.cs_model.CS.model_config.CS.config_role ==
       CS.ServerEndpoint));
     assert (pure (Some?
       st2.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret));
     assert (pure (
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_hello == None));
     assert (pure (Some?
       st2.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
     assert (pure (
       B.length st2.CS.cs_model.CS.model_handshake.CS.hs_transcript + 90 <=
         Bounds.max_transcript_len));
     lemma_select_derive_success_server_hello_ready
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes);
     assert (pure (ST.server_local_event_input_ready
       st2
       ST.LocalSendServerHello
       (Ghost.reveal 'payload_bytes)));
     let send_resp =
       send_server_hello_from_payload_once
         d
         payload
         payload_len;
     with st3 sent_after_send.
       assert (
         server_driver_connected
           d
           st3
           'certificate_chain
           'credential_identity
           'received
           sent_after_send **
         pts_to payload 'payload_bytes **
         pure (server_driver_local_write_correct
           st2
           st3
           send_resp
           ST.LocalSendServerHello
           (Ghost.reveal 'payload_bytes)
           sent_after_derive
           sent_after_send /\
         server_driver_send_server_hello_from_payload_success_correct
           st2
           st3
           send_resp
           (Ghost.reveal 'payload_bytes)));
     assert (pure (derive_resp.ST.status == ST.StepOk));
     assert (pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes)));
     assert (pure (server_driver_local_write_correct
       st2
       st3
       send_resp
       ST.LocalSendServerHello
       (Ghost.reveal 'payload_bytes)
       sent_after_derive
       sent_after_send));
     assert (pure (server_driver_send_server_hello_from_payload_success_correct
       st2
       st3
       send_resp
       (Ghost.reveal 'payload_bytes)));
     ServerDriverSelectDeriveServerHelloOk
   } else {
     assert (pure (derive_resp.ST.status == ST.StepOk));
     assert (pure (server_driver_select_derive_from_payload_success_correct
       'st0
       st2
       derive_resp
       (Ghost.reveal 'payload_bytes)));
     ServerDriverSelectDeriveServerHelloSendNotReady
   }
 } else {
   assert (pure (derive_resp.ST.status <> ST.StepOk));
   assert (pure (server_driver_select_derive_from_payload_success_correct
     'st0
     st2
     derive_resp
     (Ghost.reveal 'payload_bytes)));
   ServerDriverSelectDeriveServerHelloDeriveFailed
 }
}

fn accept_transport_and_start_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  let status = accept_transport_once d bind_host bind_host_len port;
  match status {
    ServerDriverTransportOk -> {
      let _ = start_server_once d;
      ServerDriverTransportOk
    }
    ServerDriverListenFailed -> {
      ServerDriverListenFailed
    }
    ServerDriverAcceptFailed -> {
      ServerDriverAcceptFailed
    }
  }
}

fn accept_transport_start_and_read_client_hello
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0)
  returns result:server_driver_accept_client_hello_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptClientHelloTransportOk wait ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.server_driver_client_hello_wait_ready == true ==>
                   st1.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloReceived /\
                   st1.CS.cs_model.CS.model_config ==
                     (CM.started_server_state 'st0).CS.cs_model.CS.model_config)
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  let transport =
    accept_transport_and_start_once
      d
      bind_host
      bind_host_len
      port;
  match transport {
    ServerDriverTransportOk -> {
      let wait =
        read_until_client_hello_received
          d
          network_fuel;
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st1.CS.cs_model.CS.model_control ==
             CS.ControlHandshaking CS.HsClientHelloReceived /\
           st1.CS.cs_model.CS.model_config ==
             (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
      ServerDriverAcceptClientHelloTransportOk wait
    }
    ServerDriverListenFailed -> {
      ServerDriverAcceptClientHelloListenFailed
    }
    ServerDriverAcceptFailed -> {
      ServerDriverAcceptClientHelloAcceptFailed
    }
  }
}
