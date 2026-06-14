module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CT = TLS13.Impl.Client.Types
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module IO = TLS13.IO
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec

let driver_network_out_capacity : SZ.t = SZ.uint_to_t 20000
let driver_app_out_capacity : SZ.t = SZ.uint_to_t 16640
let driver_rx_capacity : SZ.t = SZ.uint_to_t 65535
let driver_material_capacity : SZ.t = 64sz
let driver_certificate_verify_input_capacity : SZ.t = SZ.uint_to_t 256
let driver_signature_capacity : SZ.t = SZ.uint_to_t 4096

let pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

let no_channel : option IO.channel = None

let lemma_read_append_buffer_matches_raw_prefix_index
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  (k:nat { k < total_len })
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.index (B.append buffered read_chunk) k ==
      Seq.index (Seq.slice raw_after_read 0 total_len) k)
  =
  Seq.lemma_eq_elim buffered (Seq.slice raw 0 current_len);
  Seq.lemma_eq_elim read_chunk (Seq.slice raw_tail_after 0 read_len);
  Seq.lemma_len_slice raw_after_read 0 total_len;
  if k < current_len then (
    Seq.lemma_index_app1 buffered read_chunk k;
    Seq.lemma_index_slice raw 0 current_len k;
    Seq.lemma_index_slice raw_after_read 0 total_len k
  ) else (
    assert (current_len <= k);
    assert (k - current_len < read_len);
    assert (current_len + (k - current_len) == k);
    Seq.lemma_index_app2 buffered read_chunk k;
    Seq.lemma_index_slice raw_tail_after 0 read_len (k - current_len);
    Seq.lemma_index_slice raw_after_read 0 total_len k
  )

let lemma_read_append_buffer_matches_raw_prefix
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.equal (B.append buffered read_chunk)
        (Seq.slice raw_after_read 0 total_len))
  =
  Seq.lemma_len_append buffered read_chunk;
  Seq.lemma_len_slice raw_after_read 0 total_len;
  let index_proof (k:nat { k < Seq.length (B.append buffered read_chunk) })
    : Lemma
      (Seq.index (B.append buffered read_chunk) k ==
       Seq.index (Seq.slice raw_after_read 0 total_len) k)
    =
    lemma_read_append_buffer_matches_raw_prefix_index
      raw_after_read raw raw_tail_after buffered read_chunk
      current_len read_len total_len k
  in
  FStar.Classical.forall_intro
    #(k:nat { k < Seq.length (B.append buffered read_chunk) })
    #(fun k ->
      Seq.index (B.append buffered read_chunk) k ==
      Seq.index (Seq.slice raw_after_read 0 total_len) k)
    index_proof;
  Seq.lemma_eq_intro
    (B.append buffered read_chunk)
    (Seq.slice raw_after_read 0 total_len)

noeq type server_driver = {
  server_driver_server: S.server;
  server_driver_credentials: O.server_credentials;
  server_driver_channel: Box.box (option IO.channel);
  server_driver_buffered_len: Box.box SZ.t;
  server_driver_empty_payload: V.vec U8.t;
  server_driver_raw: V.vec U8.t;
  server_driver_network_out: V.vec U8.t;
  server_driver_material_payload: V.vec U8.t;
  server_driver_certificate_verify_input: V.vec U8.t;
  server_driver_signature: V.vec U8.t;
  server_driver_app_out: V.vec U8.t;
}

noextract
let logged_received_bytes_accounted
  (logged:B.bytes)
  (consumed:B.bytes)
  : prop =
  B.length logged <= B.length consumed /\
  (forall b. SeqP.count b logged <= SeqP.count b consumed)

noextract
let server_driver_wire_logs_match_witness
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  B.length buffered == SZ.v buffered_len /\
  Seq.equal (B.append consumed buffered) received /\
  logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed

noextract
let server_driver_wire_logs_match
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  exists consumed.
    server_driver_wire_logs_match_witness
      st
      received
      sent
      consumed
      buffered
      buffered_len

let lemma_legal_response_network_out_len
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        SZ.v resp.ST.network_out_len <= B.length network_out /\
        B.length (ST.response_network_out resp network_out) ==
          SZ.v resp.ST.network_out_len)
=
  if SZ.v resp.ST.network_out_len <= B.length network_out then (
    Seq.lemma_len_slice network_out 0 (SZ.v resp.ST.network_out_len)
  ) else (
    assert (Seq.equal (ST.response_network_out resp network_out) raw_sent);
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.lemma_eq_elim raw_sent B.empty
  )

let lemma_legal_response_for_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + B.length raw_sent /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received + B.length raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          (B.append st0.CS.cs_wire_log.CL.raw_received raw_received))
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (st1.CS.cs_wire_log == {
    CL.raw_sent = B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
    CL.raw_received = B.append st0.CS.cs_wire_log.CL.raw_received raw_received;
  });
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_received raw_received

let lemma_local_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.server_local_event_end_to_end_correct
        st0 st1 resp kind payload network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + SZ.v resp.ST.network_out_len /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out resp network_out)) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        SZ.v resp.ST.network_out_len <= B.length network_out)
=
  assert (ST.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
  if (exists ev raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (ST.legal_local_response
      st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    assert (ST.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CS.event_raw_delta_legal st0.CS.cs_model ev raw_sent raw_received);
    assert (ST.local_event_kind_matches kind payload ev);
    (match ev with
     | CS.ConnLocalEvent _ ->
       assert (Seq.equal raw_received B.empty)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_direction with
        | CL.Sent ->
          assert (Seq.equal raw_received B.empty)
        | CL.Received ->
          (match kind with
           | ST.LocalSendApplicationData
           | ST.LocalSendServerHello
           | ST.LocalSendEncryptedExtensions
           | ST.LocalSendCertificate
           | ST.LocalSendCertificateVerify
           | ST.LocalSendServerFinished
           | ST.LocalSendCloseNotify ->
             assert (msg.CL.message_direction == CL.Sent);
             assert False
           | _ ->
             assert False)));
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_received B.empty;
    lemma_legal_response_network_out_len
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (Seq.equal raw_sent (ST.response_network_out resp network_out));
    Seq.lemma_eq_elim raw_sent (ST.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  ) else (
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.UnexpectedMessage)))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.UnexpectedMessage)))
      B.empty
      B.empty
      network_out
      app_out;
    assert (Seq.equal B.empty (ST.response_network_out resp network_out));
    Seq.lemma_eq_elim B.empty (ST.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  )

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

noextract
let server_driver_buffers
  (d:server_driver)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  Box.pts_to d.server_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out material cv_input signature app_out.
    V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.server_driver_raw #1.0R raw **
    V.pts_to d.server_driver_network_out #1.0R network_out **
    V.pts_to d.server_driver_material_payload #1.0R material **
    V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
    V.pts_to d.server_driver_signature #1.0R signature **
    V.pts_to d.server_driver_app_out #1.0R app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length buffered == SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Seq.equal buffered (Seq.slice raw 0 (SZ.v buffered_len)) /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length material == SZ.v driver_material_capacity /\
      B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity /\
      IM.max_signature_len <= SZ.v driver_signature_capacity /\
      IM.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.server_driver_empty_payload /\
      V.is_full_vec d.server_driver_raw /\
      V.is_full_vec d.server_driver_network_out /\
      V.is_full_vec d.server_driver_material_payload /\
      V.is_full_vec d.server_driver_certificate_verify_input /\
      V.is_full_vec d.server_driver_signature /\
      V.is_full_vec d.server_driver_app_out)

noextract
let server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  server_driver_buffers d B.empty 0sz **
  pure (ST.server_end_to_end_invariant st /\
        server_driver_wire_logs_match st B.empty B.empty B.empty 0sz)

noextract
let server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  exists* ch buffered buffered_len.
    Box.pts_to d.server_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st /\
          server_driver_wire_logs_match st received sent buffered buffered_len)

noextract
let server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  exists* buffered buffered_len.
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st)

noextract
let server_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists network_out_bytes app_out_bytes.
    ST.server_local_event_end_to_end_correct
      st0
      st1
      resp
      kind
      payload
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append sent (ST.response_network_out resp network_out_bytes))

noextract
let server_driver_network_process_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists input network_out_bytes app_out_bytes.
    ST.server_network_bytes_end_to_end_correct
    st0
    st1
    resp
    input
    network_out_bytes
    app_out_bytes /\
    ST.server_network_consumed_input_projection
    st0
    st1
    resp
    input
    network_out_bytes
    app_out_bytes /\
    Seq.equal
    sent'
    (B.append
      sent
      (ST.response_network_out resp.ST.response network_out_bytes))

let lemma_server_driver_local_write_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append sent (ST.response_network_out resp network_out_bytes)))
      (ensures server_driver_local_write_correct
        st0 st1 resp kind payload sent sent')
=
  FStar.Classical.exists_intro
    (fun app_out_bytes' ->
      ST.server_local_event_end_to_end_correct
        st0
        st1
        resp
        kind
        payload
        network_out_bytes
        app_out_bytes' /\
      Seq.equal
        sent'
        (B.append sent (ST.response_network_out resp network_out_bytes)))
    app_out_bytes;
  FStar.Classical.exists_intro
    (fun network_out_bytes' ->
      exists app_out_bytes'.
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out_bytes'
          app_out_bytes' /\
        Seq.equal
          sent'
          (B.append sent (ST.response_network_out resp network_out_bytes')))
    network_out_bytes

let lemma_server_driver_network_process_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes)))
      (ensures server_driver_network_process_correct
        st0 st1 resp sent sent')
=
  FStar.Classical.exists_intro
    (fun app_out_bytes' ->
      ST.server_network_bytes_end_to_end_correct
        st0 st1 resp input network_out_bytes app_out_bytes' /\
      ST.server_network_consumed_input_projection
        st0 st1 resp input network_out_bytes app_out_bytes' /\
      Seq.equal
        sent'
        (B.append
          sent
          (ST.response_network_out resp.ST.response network_out_bytes)))
    app_out_bytes;
  FStar.Classical.exists_intro
    (fun network_out_bytes' ->
      exists app_out_bytes'.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes' app_out_bytes' /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes' app_out_bytes' /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes')))
    network_out_bytes;
  FStar.Classical.exists_intro
    (fun input' ->
      exists network_out_bytes' app_out_bytes'.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input' network_out_bytes' app_out_bytes' /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input' network_out_bytes' app_out_bytes' /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes')))
    input

let lemma_server_driver_network_process_need_more_stutter
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        server_driver_network_process_correct st0 st1 resp sent sent' /\
        resp.ST.response.ST.status == ST.NeedMoreInput)
      (ensures
        st1 == st0 /\
        Seq.equal sent' sent)
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out_bytes app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  assert (ST.server_network_consumed_input_projection
    st0 st1 resp input network_out_bytes app_out_bytes);
  assert (st1 == st0);
  assert (resp.ST.response.ST.network_out_len == 0sz);
  Seq.lemma_len_slice network_out_bytes 0 0;
  Seq.lemma_eq_intro B.empty (ST.response_network_out resp.ST.response network_out_bytes);
  Seq.lemma_eq_elim
    (ST.response_network_out resp.ST.response network_out_bytes)
    B.empty;
  Seq.append_empty_r sent;
  assert (Seq.equal
    sent'
    (B.append sent (ST.response_network_out resp.ST.response network_out_bytes)));
  assert (Seq.equal sent' sent)

let lemma_server_driver_network_process_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires server_driver_network_process_correct st0 st1 resp sent sent')
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out_bytes app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  assert (ST.server_network_consumed_input_projection
    st0 st1 resp input network_out_bytes app_out_bytes);
  ST.lemma_server_network_bytes_preserves_config
    st0
    st1
    resp
    input
    network_out_bytes
    app_out_bytes

let lemma_logged_received_bytes_accounted_append_delta
  (old_logged:B.bytes)
  (old_consumed:B.bytes)
  (raw_delta:B.bytes)
  (consumed_delta:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted old_logged old_consumed /\
        (Seq.equal raw_delta B.empty \/ Seq.equal raw_delta consumed_delta))
      (ensures
        logged_received_bytes_accounted
          (B.append old_logged raw_delta)
          (B.append old_consumed consumed_delta))
=
  Seq.lemma_len_append old_logged raw_delta;
  Seq.lemma_len_append old_consumed consumed_delta;
  SeqP.lemma_append_count old_logged raw_delta;
  SeqP.lemma_append_count old_consumed consumed_delta;
  if Seq.equal raw_delta B.empty then (
    Seq.lemma_eq_elim raw_delta B.empty
  ) else (
    Seq.lemma_eq_elim raw_delta consumed_delta
  )

let lemma_slice_append_full
  (s:B.bytes)
  (n:nat)
  : Lemma
      (requires n <= B.length s)
      (ensures Seq.equal
        (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s)))
        s)
=
  Seq.lemma_len_slice s 0 n;
  Seq.lemma_len_slice s n (B.length s);
  Seq.lemma_len_append (Seq.slice s 0 n) (Seq.slice s n (B.length s));
  assert (B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) ==
    B.length s);
  assert (forall (i:nat). i < B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) ==>
    Seq.index (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) i ==
    Seq.index s i);
  Seq.lemma_eq_intro (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) s

let lemma_server_network_wire_accounting
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (old_consumed:B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        logged_received_bytes_accounted
          st0.CS.cs_wire_log.CL.raw_received
          old_consumed)
      (ensures
        SZ.v buffer_resp.ST.response.ST.network_out_len <= B.length network_out /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out buffer_resp.ST.response network_out)) /\
        logged_received_bytes_accounted
          st1.CS.cs_wire_log.CL.raw_received
          (B.append old_consumed
            (ST.server_network_consumed_prefix buffer_resp input)))
=
  let resp = buffer_resp.ST.response in
  match resp.ST.status with
  | ST.NeedMoreInput ->
    assert (st1 == st0);
    assert (buffer_resp.ST.consumed_len == 0sz);
    assert (resp.ST.network_out_len == 0sz);
    assert (SZ.v buffer_resp.ST.consumed_len <= B.length input);
    assert (ST.server_network_consumed_prefix buffer_resp input ==
      Seq.slice input 0 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (ST.response_network_out resp network_out);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.lemma_len_slice input 0 0;
    Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
    Seq.lemma_eq_elim
      (ST.server_network_consumed_prefix buffer_resp input)
      B.empty;
    assert (Seq.equal B.empty (ST.server_network_consumed_prefix buffer_resp input));
    Seq.append_empty_r old_consumed;
    assert (Seq.equal
      (B.append old_consumed (ST.server_network_consumed_prefix buffer_resp input))
      old_consumed)
  | ST.IllegalTransition ->
    assert (st1 == st0);
    assert (buffer_resp.ST.consumed_len == 0sz);
    assert (resp.ST.network_out_len == 0sz);
    assert (SZ.v buffer_resp.ST.consumed_len <= B.length input);
    assert (ST.server_network_consumed_prefix buffer_resp input ==
      Seq.slice input 0 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (ST.response_network_out resp network_out);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.lemma_len_slice input 0 0;
    Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
    Seq.lemma_eq_elim
      (ST.server_network_consumed_prefix buffer_resp input)
      B.empty;
    assert (Seq.equal B.empty (ST.server_network_consumed_prefix buffer_resp input));
    Seq.append_empty_r old_consumed;
    assert (Seq.equal
      (B.append old_consumed (ST.server_network_consumed_prefix buffer_resp input))
      old_consumed)
  | ST.DecodeError ->
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      B.empty
      (ST.server_network_consumed_prefix buffer_resp input)
  | ST.OutputBufferTooSmall ->
    assert False
  | ST.StepOk ->
    assert (ST.server_network_step_ok_received_decode_projection
      st0 st1 buffer_resp input network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal
            st0
            msg
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.server_decoded_message_event_projection
            st0
            st1
            resp
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0
               (ST.server_network_consumed_prefix buffer_resp input)
               msg)) in
    assert (ST.server_decoded_message_event_projection
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out);
    if ST.legal_network_response
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out then (
      assert (ST.legal_response_for_event
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out);
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      lemma_legal_response_network_out_len
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
      Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
      lemma_logged_received_bytes_accounted_append_delta
        st0.CS.cs_wire_log.CL.raw_received
        old_consumed
        (ST.server_network_consumed_prefix buffer_resp input)
        (ST.server_network_consumed_prefix buffer_resp input)
    ) else (
      assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
      assert (resp.ST.status == ST.IllegalTransition);
      assert False
    )
  | ST.ConnectionFailed ->
    assert (ST.server_network_connection_failed_consumed_prefix
      st0 st1 buffer_resp input network_out app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input));
    assert (ST.legal_network_response
      st0
      st1
      resp
      (M.TlsAlert alert)
      raw_received
      network_out
      app_out);
    assert (ST.legal_response_for_event
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out;
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.lemma_eq_elim raw_received (ST.server_network_consumed_prefix buffer_resp input);
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      raw_received
      (ST.server_network_consumed_prefix buffer_resp input)

noextract
let server_driver_selection_from_payload_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (payload:B.bytes)
  : prop =
  B.length payload == 64 /\
  (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
         st0.CS.cs_model.CS.model_config.CS.config_server with
   | Some ch, Some cfg ->
     let selection = {
       CS.server_selected_client_hello = ch;
       CS.server_selected_cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
       CS.server_selected_group = T.X25519;
       CS.server_selected_signature_scheme = T.RsaPssRsaeSha256;
       CS.server_random = CL.raw_slice payload 0 32;
       CS.server_key_share_private = Some (CL.raw_slice payload 32 64);
       CS.server_key_share_public =
         CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64);
       CS.server_selected_credential = cfg.CS.server_credential_identity;
     } in
     st1 == CM.selected_server_parameters_state st0 selection
   | _ -> False)

noextract
let server_driver_derive_shared_secret_success_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : prop =
  resp.ST.status == ST.StepOk ==>
   (exists shared.
     st1 == CM.derived_shared_secret_state st0 shared /\
     (match st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CryptoSpec.x25519_shared payload ch.M.key_share == Some shared
      | None -> False))

let server_driver_select_derive_from_payload_success_correct
  (st0:CS.connection_state)
  (st2:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : prop =
  resp.ST.status == ST.StepOk ==>
   (exists st1 shared.
     server_driver_selection_from_payload_correct st0 st1 payload /\
     st2 == CM.derived_shared_secret_state st1 shared /\
     (match st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        CryptoSpec.x25519_shared
          (CL.raw_slice payload 32 64)
          ch.M.key_share == Some shared
      | None -> False))

noextract
let server_driver_send_server_hello_from_payload_success_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  : prop =
  resp.ST.status == ST.StepOk ==>
    B.length payload == 64 /\
    (let sh = {
      M.random = CL.raw_slice payload 0 32;
      M.key_share =
        CryptoSpec.x25519_public_from_private (CL.raw_slice payload 32 64);
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
     } in
     st1 ==
      CM.sent_server_hello_state
        st0
        sh
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ServerHello sh))))

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

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
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
                         credential_identity))
           | None ->
             emp)
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
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
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy driver_rx_capacity;
      let network_out = V.alloc 0uy driver_network_out_capacity;
      let material_payload = V.alloc 0uy driver_material_capacity;
      let cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy driver_signature_capacity;
      let app_out = V.alloc 0uy driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v driver_app_out_capacity));
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
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy))
        as
        (V.pts_to d.server_driver_material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy));
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v driver_app_out_capacity) 0uy));
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
      fold (server_driver_buffers d B.empty 0sz);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
}

fn server_driver_control_snapshot
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns snapshot:CR.control_snapshot
  ensures server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
          pure (CR.control_snapshot_matches snapshot 'st0)
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
  rewrite (S.connection_exactly d.server_driver_server 'st0)
    as (CR.connection_exactly d.server_driver_server 'st0);
  let snapshot = CQ.get_control_snapshot d.server_driver_server;
  rewrite (CR.connection_exactly d.server_driver_server 'st0)
    as (S.connection_exactly d.server_driver_server 'st0);
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  snapshot
}

fn accept_transport_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  unfold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
  let listener_opt = IO.listen_tcp bind_host bind_host_len port;
  match listener_opt {
    None -> {
      fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
      ServerDriverListenFailed
    }
    Some listener -> {
      let ch_opt = IO.accept_tcp listener;
      match ch_opt {
        None -> {
          IO.close_listener listener;
          fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
          ServerDriverAcceptFailed
        }
        Some ch -> {
          IO.close_listener listener;
          Box.(d.server_driver_channel := Some ch);
          fold (server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            B.empty
            B.empty);
          ServerDriverTransportOk
        }
      }
    }
  }
}

fn close_transport_once
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
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  IO.close concrete_ch;
  Box.(d.server_driver_channel := no_channel);
  fold (server_driver_closed d 'st0 'certificate_chain 'credential_identity);
}

fn read_transport_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns n:SZ.t
  ensures exists* received'.
          server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            received'
            'sent **
          pure (SZ.v n <= 65535)
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
  let current_len = Box.(!d.server_driver_buffered_len);
  assert (pure (current_len == buffered_len));
  if (current_len = 0sz) {
    assert (pure (buffered_len == 0sz));
    assert (pure (B.length buffered == 0));
    assert (pure (forall (i:nat{i < B.length buffered}).
      Seq.index buffered i == Seq.index B.empty i));
    Seq.lemma_eq_intro buffered B.empty;

    let current_channel = Box.(!d.server_driver_channel);
    assert (pure (current_channel == Some ch));
    assert (pure (Some? current_channel));
    let concrete_ch = Some?.v current_channel;
    assert (pure (current_channel == Some concrete_ch));
    assert (pure (Some concrete_ch == Some ch));
    rewrite (IO.is_channel ch 'received 'sent) as
      (IO.is_channel concrete_ch 'received 'sent);
    V.to_array_pts_to d.server_driver_raw;
    let read_len =
      IO.read
        concrete_ch
        (V.vec_to_array d.server_driver_raw)
        driver_rx_capacity;
    with raw_after read_chunk.
      assert (IO.is_channel
                concrete_ch
                (B.append (Ghost.reveal 'received) read_chunk)
                (Ghost.reveal 'sent) **
              pts_to (V.vec_to_array d.server_driver_raw) raw_after);
    rewrite (IO.is_channel
                concrete_ch
                (B.append (Ghost.reveal 'received) read_chunk)
                (Ghost.reveal 'sent)) as
      (IO.is_channel
        ch
        (B.append (Ghost.reveal 'received) read_chunk)
        (Ghost.reveal 'sent));
    assert (pure (B.length raw_after == SZ.v driver_rx_capacity));
    assert (pure (SZ.v read_len <= SZ.v driver_rx_capacity));
    assert (pure (B.length read_chunk == SZ.v read_len));
    assert (pure (Seq.equal
      read_chunk
      (Seq.slice raw_after 0 (SZ.v read_len))));
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
    CL.lemma_append_empty_right (Ghost.reveal old_consumed);
    assert (pure (Seq.equal
      (Ghost.reveal old_consumed)
      (Ghost.reveal 'received)));
    assert (pure (server_driver_wire_logs_match_witness
      'st0
      (B.append (Ghost.reveal 'received) read_chunk)
      (Ghost.reveal 'sent)
      (Ghost.reveal old_consumed)
      read_chunk
      read_len));
    assert (pure (server_driver_wire_logs_match
      'st0
      (B.append (Ghost.reveal 'received) read_chunk)
      (Ghost.reveal 'sent)
      read_chunk
      read_len));
    Box.(d.server_driver_buffered_len := read_len);
    V.to_vec_pts_to d.server_driver_raw;
    fold (server_driver_buffers d read_chunk read_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      (B.append (Ghost.reveal 'received) read_chunk)
      'sent);
    read_len
  } else {
    CL.lemma_append_empty_right (Ghost.reveal 'received);
    fold (server_driver_buffers d buffered buffered_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    0sz
  }
}

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == pending_after_consumed buffered_len consumed_len));
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'raw_bytes) 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes)
        (SZ.v consumed_len)
        (SZ.v buffered_len))));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity /\
              (forall (k:nat). k < SZ.v (R.read i) ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)) /\
              (forall (k:nat). SZ.v (R.read i) <= k /\ k < SZ.v buffered_len ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) k))
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (b == Seq.index (Ghost.reveal 'raw_bytes)
        (SZ.v vi + SZ.v consumed_len)));
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (forall (k:nat). k < SZ.v vi + 1 ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) k));
      assert (pure (SZ.v vi + 1 <= SZ.v new_len));
      SZ.fits_lte (SZ.v vi + 1) (SZ.v new_len);
      let next_i = vi `SZ.add` 1sz;
      R.write i next_i;
    };
    with raw_done.
      assert (pts_to raw raw_done);
    assert (pure (B.length raw_done == SZ.v raw_capacity));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index raw_done k ==
      Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
    Seq.lemma_len_slice raw_done 0 (SZ.v new_len);
    Seq.lemma_len_slice (Ghost.reveal 'raw_bytes)
      (SZ.v consumed_len)
      (SZ.v buffered_len);
    assert (pure (forall (k:nat). k < B.length (Seq.slice raw_done 0 (SZ.v new_len)) ==>
      Seq.index (Seq.slice raw_done 0 (SZ.v new_len)) k ==
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k));
    Seq.lemma_eq_intro
      (Seq.slice raw_done 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len));
    new_len
  }
}

fn process_buffered_network_bytes_compact_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pure (server_driver_network_process_correct
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent')
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
  let current_len = Box.(!d.server_driver_buffered_len);
  assert (pure (current_len == buffered_len));

  V.to_array_pts_to d.server_driver_raw;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  A.pts_to_len (V.vec_to_array d.server_driver_raw);
  assert (pure (A.length (V.vec_to_array d.server_driver_raw) ==
    SZ.v driver_rx_capacity));
  A.to_mask (V.vec_to_array d.server_driver_raw);
  with raw_mask.
    assert (A.pts_to_mask
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      raw_mask
      (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v driver_rx_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index raw i)));
  let raw_prefix_array =
    A.sub
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      #(fun _ -> True)
      0sz
      (SZ.v current_len);
  with raw_prefix_mask.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Some? (Seq.index raw_prefix_mask i)));
  A.from_mask raw_prefix_array;
  with raw_prefix.
    assert (pts_to raw_prefix_array raw_prefix);
  assert (pure (B.length raw_prefix == SZ.v current_len));
  assert (pure (SZ.v current_len == SZ.v buffered_len));
  assert (pure (Seq.equal raw_prefix
    (Seq.slice raw 0 (SZ.v current_len))));
  assert (pure (Seq.equal raw_prefix buffered));

  let buffer_resp =
    S.process_network_bytes
      d.server_driver_server
      raw_prefix_array
      current_len
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (S.connection_exactly d.server_driver_server st1 **
            pts_to raw_prefix_array raw_prefix **
            pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
            pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_network_consumed_input_projection
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= B.length raw_prefix));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= SZ.v current_len));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= SZ.v buffered_len));

  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
  rewrite
    (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub (V.vec_to_array d.server_driver_raw) 0 (SZ.v current_len))
      #1.0R
      raw_prefix_mask_after
      (fun _ -> True));
  A.return_sub
    (V.vec_to_array d.server_driver_raw)
    #1.0R
    #raw_mask
    #raw_prefix_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v current_len))
    #(fun _ -> True)
    #0
    #(SZ.v current_len);
  with raw_joined_mask.
    assert (A.pts_to_mask (V.vec_to_array d.server_driver_raw) #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v current_len)) \/
        (0 <= k /\ k < SZ.v current_len /\ True)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v current_len)) \/
     (0 <= i /\ i < SZ.v current_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask (V.vec_to_array d.server_driver_raw);
  with raw_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_raw) raw_bytes);
  assert (pure (B.length raw_bytes == SZ.v driver_rx_capacity));
  assert (pure (B.length raw == SZ.v driver_rx_capacity));
  assert (pure (forall (i:nat). i < B.length raw_bytes ==>
    Seq.index raw_bytes i == Seq.index raw i));
  Seq.lemma_eq_intro raw_bytes raw;
  assert (pure (Seq.equal raw_bytes raw));

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
  let consumed_prefix =
    Ghost.hide (ST.server_network_consumed_prefix buffer_resp raw_prefix);
  let new_buffered =
    Ghost.hide (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len));
  Seq.lemma_len_slice
    buffered
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len);
  assert (pure (B.length (Ghost.reveal new_buffered) ==
    SZ.v buffered_len - SZ.v buffer_resp.ST.consumed_len));
  let new_len = Ghost.hide (pending_after_consumed buffered_len buffer_resp.ST.consumed_len);
  assert (pure (SZ.v (Ghost.reveal new_len) ==
    SZ.v buffered_len - SZ.v buffer_resp.ST.consumed_len));
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v (Ghost.reveal new_len)));
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice raw_prefix 0 (SZ.v buffer_resp.ST.consumed_len))));
  Seq.lemma_eq_elim raw_prefix buffered;
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice buffered 0 (SZ.v buffer_resp.ST.consumed_len))));
  lemma_slice_append_full
    buffered
    (SZ.v buffer_resp.ST.consumed_len);
  assert (pure (Seq.equal
    (B.append (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered))
    buffered));
  lemma_server_network_wire_accounting
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal old_consumed);
  assert (pure (SZ.v buffer_resp.ST.response.ST.network_out_len <=
    B.length network_out_bytes));
  Seq.append_assoc
    (Ghost.reveal old_consumed)
    (Ghost.reveal consumed_prefix)
    (Ghost.reveal new_buffered);
  assert (pure (Seq.equal
    (B.append
      (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
      (Ghost.reveal new_buffered))
    (Ghost.reveal 'received)));

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
      buffer_resp.ST.response.ST.network_out_len;
  assert (pure (written == buffer_resp.ST.response.ST.network_out_len));
  rewrite (IO.is_channel
             concrete_ch
             (Ghost.reveal 'received)
             (B.append
               (Ghost.reveal 'sent)
               (if SZ.v written <= B.length network_out_bytes
                then Seq.slice network_out_bytes 0 (SZ.v written)
                else B.empty))) as
    (IO.is_channel
      ch
      (Ghost.reveal 'received)
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (ST.response_network_out buffer_resp.ST.response network_out_bytes)));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (ST.response_network_out buffer_resp.ST.response network_out_bytes))));
  assert (pure (Seq.equal (Ghost.reveal 'sent) 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim (Ghost.reveal 'sent) 'st0.CS.cs_wire_log.CL.raw_sent;

  let compact_len =
    compact_buffer_suffix
      (V.vec_to_array d.server_driver_raw)
      driver_rx_capacity
      current_len
      buffer_resp.ST.consumed_len;
  with compacted_raw.
    assert (pts_to (V.vec_to_array d.server_driver_raw) compacted_raw);
  assert (pure (compact_len == Ghost.reveal new_len));
  assert (pure (B.length compacted_raw == SZ.v driver_rx_capacity));
  assert (pure (Seq.equal
    (Seq.slice compacted_raw 0 (SZ.v compact_len))
    (Seq.slice raw_bytes
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  SeqP.slice_slice
    raw
    0
    (SZ.v buffered_len)
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len);
  assert (pure (Seq.equal
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))
    (Seq.slice raw
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  Seq.lemma_eq_elim raw_bytes raw;
  Seq.lemma_eq_elim
    (Ghost.reveal new_buffered)
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len));
  assert (pure (Seq.equal
    (Ghost.reveal new_buffered)
    (Seq.slice compacted_raw 0 (SZ.v compact_len))));

  Box.(d.server_driver_buffered_len := compact_len);
  V.to_vec_pts_to d.server_driver_raw;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d (Ghost.reveal new_buffered) compact_len);
  assert (pure (logged_received_bytes_accounted
    st1.CS.cs_wire_log.CL.raw_received
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))));
  assert (pure (server_driver_wire_logs_match_witness
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
    (Ghost.reveal new_buffered)
    compact_len));
  assert (pure (server_driver_wire_logs_match
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal new_buffered)
    compact_len));
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
  lemma_server_driver_network_process_correct_intro
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  buffer_resp
}

fn read_and_process_network_once
  (d:server_driver)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 received' sent'.
          server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent' **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent')
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
  let current_len = Box.(!d.server_driver_buffered_len);
  assert (pure (current_len == buffered_len));
  assert (pure (SZ.v current_len <= SZ.v driver_rx_capacity));

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

  V.to_array_pts_to d.server_driver_raw;
  A.pts_to_len (V.vec_to_array d.server_driver_raw);
  assert (pure (A.length (V.vec_to_array d.server_driver_raw) ==
    SZ.v driver_rx_capacity));
  A.to_mask (V.vec_to_array d.server_driver_raw);
  with raw_mask.
    assert (A.pts_to_mask
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      raw_mask
      (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v driver_rx_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index raw i)));

  let available = SZ.sub driver_rx_capacity current_len;
  assert (pure (SZ.v available == SZ.v driver_rx_capacity - SZ.v current_len));
  let raw_tail_array =
    A.sub
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      #(fun _ -> True)
      current_len
      (SZ.v driver_rx_capacity);
  with raw_tail_mask.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask == SZ.v available));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask ==>
    Some? (Seq.index raw_tail_mask i)));
  A.from_mask raw_tail_array;
  with raw_tail.
    assert (pts_to raw_tail_array raw_tail);
  assert (pure (B.length raw_tail == SZ.v available));

  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let read_len = IO.read concrete_ch raw_tail_array available;
  with raw_tail_after read_chunk.
    assert (IO.is_channel
              concrete_ch
              (B.append (Ghost.reveal 'received) read_chunk)
              (Ghost.reveal 'sent) **
            pts_to raw_tail_array raw_tail_after);
  rewrite (IO.is_channel
              concrete_ch
              (B.append (Ghost.reveal 'received) read_chunk)
              (Ghost.reveal 'sent)) as
    (IO.is_channel
      ch
      (B.append (Ghost.reveal 'received) read_chunk)
      (Ghost.reveal 'sent));
  assert (pure (B.length raw_tail_after == SZ.v available));
  assert (pure (B.length read_chunk == SZ.v read_len));
  assert (pure (SZ.v read_len <= SZ.v available));
  assert (pure (SZ.v current_len + SZ.v read_len <= SZ.v driver_rx_capacity));
  SZ.fits_lte (SZ.v current_len + SZ.v read_len) (SZ.v driver_rx_capacity);
  let total_len = current_len `SZ.add` read_len;
  assert (pure (SZ.v total_len == SZ.v current_len + SZ.v read_len));
  assert (pure (SZ.v total_len <= SZ.v driver_rx_capacity));
  assert (pure (SZ.v total_len == SZ.v buffered_len + SZ.v read_len));

  let new_buffered =
    Ghost.hide (B.append buffered read_chunk);
  Seq.lemma_len_append buffered read_chunk;
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v total_len));
  Seq.append_assoc (Ghost.reveal old_consumed) buffered read_chunk;
  assert (pure (Seq.equal
    (B.append
      (B.append (Ghost.reveal old_consumed) buffered)
      read_chunk)
    (B.append (Ghost.reveal 'received) read_chunk)));
  assert (pure (Seq.equal
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal new_buffered))
    (B.append (Ghost.reveal 'received) read_chunk)));
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (B.append (Ghost.reveal 'received) read_chunk)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    (Ghost.reveal new_buffered)
    total_len));
  assert (pure (server_driver_wire_logs_match
    'st0
    (B.append (Ghost.reveal 'received) read_chunk)
    (Ghost.reveal 'sent)
    (Ghost.reveal new_buffered)
    total_len));

  A.to_mask raw_tail_array;
  with raw_tail_mask_after.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask_after == B.length raw_tail_after));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Seq.index raw_tail_mask_after i == Some (Seq.index raw_tail_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Some? (Seq.index raw_tail_mask_after i)));
  rewrite
    (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub
        (V.vec_to_array d.server_driver_raw)
        (SZ.v current_len)
        (SZ.v driver_rx_capacity))
      #1.0R
      raw_tail_mask_after
      (fun _ -> True));
  A.return_sub
    (V.vec_to_array d.server_driver_raw)
    #1.0R
    #raw_mask
    #raw_tail_mask_after
    #(fun k -> True /\ ~(SZ.v current_len <= k /\ k < SZ.v driver_rx_capacity))
    #(fun _ -> True)
    #(SZ.v current_len)
    #(SZ.v driver_rx_capacity);
  with raw_joined_mask.
    assert (A.pts_to_mask (V.vec_to_array d.server_driver_raw) #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(SZ.v current_len <= k /\ k < SZ.v driver_rx_capacity)) \/
        (SZ.v current_len <= k /\ k < SZ.v driver_rx_capacity /\ True)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(SZ.v current_len <= i /\ i < SZ.v driver_rx_capacity)) \/
     (SZ.v current_len <= i /\ i < SZ.v driver_rx_capacity /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask (V.vec_to_array d.server_driver_raw);
  with raw_after_read.
    assert (pts_to (V.vec_to_array d.server_driver_raw) raw_after_read);
  assert (pure (B.length raw_after_read == SZ.v driver_rx_capacity));
  assert (pure (Seq.equal buffered (Seq.slice raw 0 (SZ.v current_len))));
  assert (pure (Seq.equal read_chunk
    (Seq.slice raw_tail_after 0 (SZ.v read_len))));
  assert (pure (forall (i:nat). i < B.length raw_after_read ==>
    Some (Seq.index raw_after_read i) == Seq.index raw_joined_mask i));
  assert (pure (forall (i:nat). i < SZ.v current_len ==>
    Seq.index raw_after_read i == Seq.index raw i));
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    Seq.index raw_after_read (SZ.v current_len + i) ==
    Seq.index raw_tail_after i));
  lemma_read_append_buffer_matches_raw_prefix
    raw_after_read
    raw
    raw_tail_after
    buffered
    read_chunk
    (SZ.v current_len)
    (SZ.v read_len)
    (SZ.v total_len);
  Seq.lemma_eq_elim
    (B.append buffered read_chunk)
    (Seq.slice raw_after_read 0 (SZ.v total_len));
  assert (pure (Seq.equal (Ghost.reveal new_buffered)
    (Seq.slice raw_after_read 0 (SZ.v total_len))));

  Box.(d.server_driver_buffered_len := total_len);
  V.to_vec_pts_to d.server_driver_raw;
  fold (server_driver_buffers d (Ghost.reveal new_buffered) total_len);
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    (B.append (Ghost.reveal 'received) read_chunk)
    'sent);
  let resp = process_buffered_network_bytes_compact_once d;
  resp
}

fn rec read_process_network_until_ready
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_network_loop_result
  ensures exists* st1 received' sent'.
          server_driver_connected
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent' **
          pure (result.server_driver_network_loop_exhausted == false ==>
            result.server_driver_network_loop_last.ST.response.ST.status <>
              ST.NeedMoreInput /\
            server_driver_network_process_correct
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent')
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    ST.response = no_op_resp;
    ST.consumed_len = 0sz;
  };
  if (fuel = 0sz) {
    {
      server_driver_network_loop_last = no_op_buffer_resp;
      server_driver_network_loop_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step = read_and_process_network_once d;
    with st1 received' sent'.
      assert (server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        received'
        sent' **
      pure (server_driver_network_process_correct
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent'));
    let need_more = step.ST.response.ST.status = ST.NeedMoreInput;
    if need_more {
      lemma_server_driver_network_process_need_more_stutter
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent';
      assert (pure (st1 == 'st0));
      assert (pure (Seq.equal sent' (Ghost.reveal 'sent)));
      Seq.lemma_eq_elim sent' (Ghost.reveal 'sent);
      let next_fuel = SZ.sub fuel 1sz;
      assert (pure (SZ.v next_fuel < SZ.v fuel));
      let result = read_process_network_until_ready d next_fuel;
      with st2 received2 sent2.
        assert (server_driver_connected
          d
          st2
          'certificate_chain
          'credential_identity
          received2
          sent2 **
        pure (result.server_driver_network_loop_exhausted == false ==>
          result.server_driver_network_loop_last.ST.response.ST.status <>
            ST.NeedMoreInput /\
          server_driver_network_process_correct
            st1
            st2
            result.server_driver_network_loop_last
            sent'
            sent2));
      assert (pure (result.server_driver_network_loop_exhausted == false ==>
        server_driver_network_process_correct
          'st0
          st2
          result.server_driver_network_loop_last
          (Ghost.reveal 'sent)
          sent2));
      result
    } else {
      assert (pure (step.ST.response.ST.status <> ST.NeedMoreInput));
      assert (pure (server_driver_network_process_correct
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent'));
      {
        server_driver_network_loop_last = step;
        server_driver_network_loop_exhausted = false;
      }
    }
  }
}

fn rec read_until_client_hello_received
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_client_hello_wait_result
  ensures exists* st1 received' sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pure (result.server_driver_client_hello_wait_ready == true ==>
            st1.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    ST.response = no_op_resp;
    ST.consumed_len = 0sz;
  };
  let snapshot = server_driver_control_snapshot d;
  assert (pure (CR.control_snapshot_matches snapshot 'st0));
  let client_hello_received =
    (snapshot.CR.snapshot_control_tag = 1uy) &&
    (snapshot.CR.snapshot_handshake_stage_tag = 13uy);
  if client_hello_received {
    assert (pure (snapshot.CR.snapshot_control_tag == 1uy));
    assert (pure (snapshot.CR.snapshot_handshake_stage_tag == 13uy));
    assert_norm (Tags.handshake_stage_tag_matches 13uy CS.HsClientHelloReceived);
    assert (pure (
      'st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure (
      'st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
    {
      server_driver_client_hello_wait_last = no_op_buffer_resp;
      server_driver_client_hello_wait_ready = true;
      server_driver_client_hello_wait_exhausted = false;
    }
  } else if (fuel = 0sz) {
    {
      server_driver_client_hello_wait_last = no_op_buffer_resp;
      server_driver_client_hello_wait_ready = false;
      server_driver_client_hello_wait_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step = read_and_process_network_once d;
    with st1 received' sent'.
      assert (server_driver_connected
        d
        st1
        'certificate_chain
        'credential_identity
        received'
        sent' **
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
    let next_fuel = SZ.sub fuel 1sz;
    assert (pure (SZ.v next_fuel < SZ.v fuel));
    let result = read_until_client_hello_received d next_fuel;
    with st2 received2 sent2.
      assert (server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        received2
        sent2 **
      pure (result.server_driver_client_hello_wait_ready == true ==>
        st2.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        st2.CS.cs_model.CS.model_config ==
          st1.CS.cs_model.CS.model_config));
    assert (pure (result.server_driver_client_hello_wait_ready == true ==>
      st2.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
    result
  }
}

fn start_server_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures server_driver_connected
            d
            (CM.started_server_state 'st0)
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
  assert (pure (Seq.equal empty_payload B.empty));
  V.to_array_pts_to d.server_driver_empty_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  rewrite (S.connection_exactly d.server_driver_server 'st0) as
    (SSetup.connection_exactly d.server_driver_server 'st0);
  let resp =
    SSetup.process_start_server_local_event
      d.server_driver_server
      ST.LocalStartServer
      (V.vec_to_array d.server_driver_empty_payload)
      0sz
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      SSetup.connection_exactly d.server_driver_server st1 **
      pts_to (V.vec_to_array d.server_driver_empty_payload) empty_payload **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  rewrite (SSetup.connection_exactly d.server_driver_server st1) as
    (S.connection_exactly d.server_driver_server st1);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    ST.LocalStartServer
    empty_payload
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  assert (pure (st1 == CM.started_server_state 'st0));
  rewrite (S.connection_exactly d.server_driver_server st1) as
    (S.connection_exactly
      d.server_driver_server
      (CM.started_server_state 'st0));
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (Seq.equal 'sent (CM.started_server_state 'st0).CS.cs_wire_log.CL.raw_sent));
  assert (pure (server_driver_wire_logs_match
    (CM.started_server_state 'st0)
    'received
    'sent
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_empty_payload;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    (CM.started_server_state 'st0)
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
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

fn start_server_if_ready
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               'received
               'sent
           | _ ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent)
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
  assert (pure (ST.server_state_correct 'st0));
  let action = S.next_local_action d.server_driver_server;
  assert (pure (ST.next_local_action_sound 'st0 action));
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  if action.ST.next_local_ready {
    assert (pure (action.ST.next_local_ready == true));
    if (action.ST.next_local_kind = ST.LocalStartServer) {
      assert (pure (action.ST.next_local_kind == ST.LocalStartServer));
      assert (pure (CM.can_start_server 'st0));
      let _ = start_server_once d;
      ServerDriverLocalProcessed
    } else {
      ServerDriverLocalExternalOrUnsupported
    }
  } else {
    ServerDriverLocalNotReady
  }
}

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

fn process_local_event_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
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
                 ST.server_local_event_input_ready_with_credentials
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity))
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
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')
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
    S.process_local_event_with_credentials
      d.server_driver_server
      d.server_driver_credentials
      kind
      payload
      payload_len
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      O.is_server_credentials
        d.server_driver_credentials
        'certificate_chain
        'credential_identity **
      pts_to payload 'payload_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
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
  assert (pure (
    ST.server_local_event_end_to_end_correct
      'st0
      st1
      resp
      kind
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      app_out_bytes /\
    Seq.equal
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
    kind
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
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))));
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

fn select_and_derive_shared_secret_once
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
  ensures exists* st2 sent'.
          server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            'received
            sent'
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

  let _ =
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
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    (CL.raw_slice material_bytes 32 64)));
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
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
  assert (pure (ST.server_local_event_input_ready
    st1
    ST.LocalDeriveSharedSecret
    server_private_key_bytes));
  let resp =
    derive_shared_secret_from_payload_once
      d
      server_private_key
      32sz;
  resp
}

fn select_and_derive_shared_secret_if_ready_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
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
             exists* st2 sent'.
               server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 'received
                 sent'
           | ServerDriverLocalNotReady ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
           | ServerDriverLocalExternalOrUnsupported ->
             pure False)
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
  assert (pure (B.length material == 64));
  assert (pure (CL.raw_slice material 0 32 ==
    Seq.slice material 0 32));
  Seq.lemma_len_slice material 0 32;
  assert (pure (B.length (CL.raw_slice material 0 32) == 32));
  assert (pure (CL.raw_slice material 32 64 ==
    Seq.slice material 32 64));
  Seq.lemma_len_slice material 32 64;
  assert (pure (B.length (CL.raw_slice material 32 64) == 32));
  let server_random : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice material 0 32);
  let server_private_key : erased (b:B.bytes{B.length b == 32}) =
    Ghost.hide (CL.raw_slice material 32 64);
  assert (pure (Ghost.reveal server_random ==
    CL.raw_slice material 0 32));
  assert (pure (Ghost.reveal server_private_key ==
    CL.raw_slice material 32 64));

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
      (CL.raw_slice material 0 32);
    Seq.lemma_eq_elim
      (Ghost.reveal server_private_key)
      (CL.raw_slice material 32 64);
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      material));
    Seq.lemma_create_len 64 0uy;
    lemma_select_server_parameters_ready_payload_irrelevant
      'st0
      material
      (Seq.create 64 0uy);
    assert (pure (ST.server_local_event_input_ready
      'st0
      ST.LocalSelectServerParameters
      (Seq.create 64 0uy)));
    fold (server_driver_buffers d buffered buffered_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    let resp = select_and_derive_shared_secret_once d;
    with st2 sent'.
      assert (server_driver_connected
        d
        st2
        'certificate_chain
        'credential_identity
        'received
        sent');
    ServerDriverLocalProcessed
  } else {
    fold (server_driver_buffers d buffered buffered_len);
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

fn accept_start_read_client_hello_select_derive_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
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
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns result:server_driver_accept_select_derive_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptSelectDeriveListenFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveAcceptFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptSelectDeriveClientHelloWait wait ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.server_driver_client_hello_wait_ready == false)
           | ServerDriverAcceptSelectDeriveMaterialFailed ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlHandshaking CS.HsClientHelloReceived)
           | ServerDriverAcceptSelectDeriveSelectionNotReady ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlHandshaking CS.HsClientHelloReceived)
           | ServerDriverAcceptSelectDeriveInternalUnsupported ->
             pure False
           | ServerDriverAcceptSelectDeriveOk ->
             exists* st2 received sent.
               server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 received
                 sent)
{
  let accepted =
    accept_transport_start_and_read_client_hello
      d
      bind_host
      bind_host_len
      port
      network_fuel;
  match accepted {
    ServerDriverAcceptClientHelloListenFailed -> {
      ServerDriverAcceptSelectDeriveListenFailed
    }
    ServerDriverAcceptClientHelloAcceptFailed -> {
      ServerDriverAcceptSelectDeriveAcceptFailed
    }
    ServerDriverAcceptClientHelloTransportOk wait -> {
      with st_ch received sent.
        assert (server_driver_connected
          d
          st_ch
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
      if wait.server_driver_client_hello_wait_ready {
        assert (pure (wait.server_driver_client_hello_wait_ready == true));
        assert (pure (st_ch.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived));
        assert (pure (
          (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (
          st_ch.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (Some?
          st_ch.CS.cs_model.CS.model_config.CS.config_server));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_config.CS.config_server with
          | Some cfg ->
            CS.cipher_suite_offered
              cfg.CS.server_supported_cipher_suites
              T.TLS_CHACHA20_POLY1305_SHA256 /\
            CS.named_group_offered
              cfg.CS.server_supported_groups
              T.X25519 /\
            CS.signature_scheme_offered
              cfg.CS.server_allowed_signature_schemes
              T.RsaPssRsaeSha256 /\
            cfg.CS.server_sni_policy == None
          | None -> False));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                st_ch.CS.cs_model.CS.model_config.CS.config_server with
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
          | _, _ -> True));
        let material_ok = generate_server_material_once d;
        assert (server_driver_connected
          d
          st_ch
          'certificate_chain
          'credential_identity
          received
          sent);
        if material_ok {
          assert (pure (
            Some? st_ch.CS.cs_model.CS.model_config.CS.config_server /\
            (match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                   st_ch.CS.cs_model.CS.model_config.CS.config_server with
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
             | _, _ -> True)));
          let status = select_and_derive_shared_secret_if_ready_once d;
          match status {
            ServerDriverLocalProcessed -> {
              ServerDriverAcceptSelectDeriveOk
            }
            ServerDriverLocalNotReady -> {
              assert (server_driver_connected
                d
                st_ch
                'certificate_chain
                'credential_identity
                received
                sent);
              assert (pure (st_ch.CS.cs_model.CS.model_control ==
                CS.ControlHandshaking CS.HsClientHelloReceived));
              ServerDriverAcceptSelectDeriveSelectionNotReady
            }
            ServerDriverLocalExternalOrUnsupported -> {
              assert (pure False);
              ServerDriverAcceptSelectDeriveInternalUnsupported
            }
          }
        } else {
          assert (pure (st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived));
          ServerDriverAcceptSelectDeriveMaterialFailed
        }
      } else {
        assert (pure (wait.server_driver_client_hello_wait_ready == false));
        ServerDriverAcceptSelectDeriveClientHelloWait wait
      }
    }
  }
}

fn accept_start_read_client_hello_select_derive_send_server_hello_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
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
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns result:server_driver_accept_server_hello_result
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | ServerDriverAcceptServerHelloListenFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloAcceptFailed ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity
           | ServerDriverAcceptServerHelloClientHelloWait wait ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (wait.server_driver_client_hello_wait_ready == false)
           | ServerDriverAcceptServerHelloMaterialFailed
           | ServerDriverAcceptServerHelloSelectionNotReady ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_control ==
                 CS.ControlHandshaking CS.HsClientHelloReceived)
           | ServerDriverAcceptServerHelloDeriveFailed
           | ServerDriverAcceptServerHelloSendNotReady
           | ServerDriverAcceptServerHelloOk ->
             exists* st2 received sent.
               server_driver_connected
                 d
                 st2
                 'certificate_chain
                 'credential_identity
                 received
                 sent)
{
  let accepted =
    accept_transport_start_and_read_client_hello
      d
      bind_host
      bind_host_len
      port
      network_fuel;
  match accepted {
    ServerDriverAcceptClientHelloListenFailed -> {
      ServerDriverAcceptServerHelloListenFailed
    }
    ServerDriverAcceptClientHelloAcceptFailed -> {
      ServerDriverAcceptServerHelloAcceptFailed
    }
    ServerDriverAcceptClientHelloTransportOk wait -> {
      with st_ch received sent.
        assert (server_driver_connected
          d
          st_ch
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (wait.server_driver_client_hello_wait_ready == true ==>
          st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived /\
          st_ch.CS.cs_model.CS.model_config ==
            (CM.started_server_state 'st0).CS.cs_model.CS.model_config));
      if wait.server_driver_client_hello_wait_ready {
        assert (pure (wait.server_driver_client_hello_wait_ready == true));
        assert (pure (st_ch.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived));
        assert (pure (
          (CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (
          st_ch.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        assert (pure (Some?
          st_ch.CS.cs_model.CS.model_config.CS.config_server));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_config.CS.config_server with
          | Some cfg ->
            CS.cipher_suite_offered
              cfg.CS.server_supported_cipher_suites
              T.TLS_CHACHA20_POLY1305_SHA256 /\
            CS.named_group_offered
              cfg.CS.server_supported_groups
              T.X25519 /\
            CS.signature_scheme_offered
              cfg.CS.server_allowed_signature_schemes
              T.RsaPssRsaeSha256 /\
            cfg.CS.server_sni_policy == None
          | None -> False));
        assert (pure (
          match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                st_ch.CS.cs_model.CS.model_config.CS.config_server with
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
          | _, _ -> True));

        let mut material_payload = [| 0uy; 64sz |];
        let material_ok = Crypto.random_bytes material_payload 64sz;
        with material_bytes.
          assert (pts_to material_payload material_bytes);
        assert (pure (B.length material_bytes == 64));
        if material_ok {
          assert (pure (CL.raw_slice material_bytes 0 32 ==
            Seq.slice material_bytes 0 32));
          Seq.lemma_len_slice material_bytes 0 32;
          assert (pure (B.length (CL.raw_slice material_bytes 0 32) == 32));
          assert (pure (CL.raw_slice material_bytes 32 64 ==
            Seq.slice material_bytes 32 64));
          Seq.lemma_len_slice material_bytes 32 64;
          assert (pure (B.length (CL.raw_slice material_bytes 32 64) == 32));
          let server_random : erased (b:B.bytes{B.length b == 32}) =
            Ghost.hide (CL.raw_slice material_bytes 0 32);
          let server_private_key : erased (b:B.bytes{B.length b == 32}) =
            Ghost.hide (CL.raw_slice material_bytes 32 64);
          assert (pure (Ghost.reveal server_random ==
            CL.raw_slice material_bytes 0 32));
          assert (pure (Ghost.reveal server_private_key ==
            CL.raw_slice material_bytes 32 64));

          unfold (server_driver_connected
            d
            st_ch
            'certificate_chain
            'credential_identity
            received
            sent);
          with ch2 buffered2 buffered_len2.
            assert (
              Box.pts_to d.server_driver_channel (Some ch2) **
              IO.is_channel ch2 received sent **
              server_driver_buffers d buffered2 buffered_len2);
          rewrite (S.connection_exactly d.server_driver_server st_ch)
            as (CR.connection_exactly d.server_driver_server st_ch);
          let ready =
            CQ.can_select_supported_server_parameters_runtime
              d.server_driver_server
              #server_random
              #server_private_key;
          rewrite (CR.connection_exactly d.server_driver_server st_ch)
            as (S.connection_exactly d.server_driver_server st_ch);
          fold (server_driver_connected
            d
            st_ch
            'certificate_chain
            'credential_identity
            received
            sent);
          if ready {
            assert (pure (ready));
            assert (pure (st_ch.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived));
            assert (pure (st_ch.CS.cs_model.CS.model_config.CS.config_role ==
              CS.ServerEndpoint));
            assert (pure (CR.server_selection_absent
              st_ch.CS.cs_model.CS.model_handshake));
            assert (pure (Some?
              st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello));
            assert (pure (Some?
              st_ch.CS.cs_model.CS.model_config.CS.config_server));
            assert (pure (match st_ch.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
                                st_ch.CS.cs_model.CS.model_config.CS.config_server with
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
                CM.can_select_server_parameters st_ch selection
              | _, _ -> False));
            Seq.lemma_eq_elim
              (Ghost.reveal server_random)
              (CL.raw_slice material_bytes 0 32);
            Seq.lemma_eq_elim
              (Ghost.reveal server_private_key)
              (CL.raw_slice material_bytes 32 64);
            assert (pure (ST.server_local_event_input_ready
              st_ch
              ST.LocalSelectServerParameters
              material_bytes));
            let server_hello_result =
              select_derive_send_server_hello_from_payload_once
                d
                material_payload
                64sz;
            match server_hello_result {
              ServerDriverSelectDeriveServerHelloOk -> {
                ServerDriverAcceptServerHelloOk
              }
              ServerDriverSelectDeriveServerHelloDeriveFailed -> {
                ServerDriverAcceptServerHelloDeriveFailed
              }
              ServerDriverSelectDeriveServerHelloSendNotReady -> {
                ServerDriverAcceptServerHelloSendNotReady
              }
            }
          } else {
            assert (server_driver_connected
              d
              st_ch
              'certificate_chain
              'credential_identity
              received
              sent);
            assert (pure (st_ch.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived));
            ServerDriverAcceptServerHelloSelectionNotReady
          }
        } else {
          assert (server_driver_connected
            d
            st_ch
            'certificate_chain
            'credential_identity
            received
            sent);
          assert (pure (st_ch.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived));
          ServerDriverAcceptServerHelloMaterialFailed
        }
      } else {
        assert (pure (wait.server_driver_client_hello_wait_ready == false));
        ServerDriverAcceptServerHelloClientHelloWait wait
      }
    }
  }
}

fn process_empty_local_event_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             kind
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
{
  let mut empty_payload = [| 0uy; 0sz |];
  with empty_payload_bytes.
    assert (pts_to empty_payload empty_payload_bytes);
  assert (pure (B.length empty_payload_bytes == 0));
  assert (pure (forall (i:nat{i < B.length empty_payload_bytes}).
    Seq.index empty_payload_bytes i == Seq.index B.empty i));
  Seq.lemma_eq_intro empty_payload_bytes B.empty;
  assert (pure (Seq.equal empty_payload_bytes B.empty));
  Seq.lemma_eq_elim empty_payload_bytes B.empty;
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    kind
    empty_payload_bytes
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  let resp =
    process_local_event_and_write_once
      d
      kind
      empty_payload
      0sz;
  resp
}

fn process_ready_empty_local_action_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             exists* st1 sent'.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 'received
                 sent'
           | _ ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent)
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
  assert (pure (ST.server_state_correct 'st0));
  let action = S.next_local_action d.server_driver_server;
  assert (pure (ST.next_local_action_sound 'st0 action));
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  if action.ST.next_local_ready {
    assert (pure (action.ST.next_local_ready == true));
    match action.ST.next_local_kind {
      ST.LocalStartServer -> {
        assert (pure (CM.can_start_server 'st0));
        let _ = start_server_once d;
        ServerDriverLocalProcessed
      }
      ST.LocalInstallServerHandshakeTrafficKeys -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalInstallClientHandshakeTrafficKeys -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalInstallServerApplicationTrafficKeys -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalInstallClientApplicationTrafficKeys -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalSendEncryptedExtensions -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalSendCertificateVerify -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      ST.LocalSendServerFinished -> {
        assert (pure (ST.server_local_event_input_ready
          'st0
          action.ST.next_local_kind
          B.empty));
        assert (pure (ST.server_local_event_input_ready_with_credentials
          'st0
          action.ST.next_local_kind
          B.empty
          (Ghost.reveal 'certificate_chain)
          (Ghost.reveal 'credential_identity)));
        let _ =
          process_empty_local_event_and_write_once
            d
            action.ST.next_local_kind;
        ServerDriverLocalProcessed
      }
      _ -> {
        ServerDriverLocalExternalOrUnsupported
      }
    }
  } else {
    ServerDriverLocalNotReady
  }
}

fn rec drain_ready_empty_local_actions
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns result:server_driver_local_drain_result
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    let result:server_driver_local_drain_result = {
      server_driver_local_drain_last = ServerDriverLocalNotReady;
      server_driver_local_drain_exhausted = true;
    };
    result
  } else {
    assert (pure (0 < SZ.v fuel));
    let status = process_ready_empty_local_action_once d;
    match status {
      ServerDriverLocalProcessed -> {
        with st1 sent'.
          assert (server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent');
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        drain_ready_empty_local_actions d next_fuel
      }
      ServerDriverLocalNotReady -> {
        let result:server_driver_local_drain_result = {
          server_driver_local_drain_last = ServerDriverLocalNotReady;
          server_driver_local_drain_exhausted = false;
        };
        result
      }
      ServerDriverLocalExternalOrUnsupported -> {
        let result:server_driver_local_drain_result = {
          server_driver_local_drain_last = ServerDriverLocalExternalOrUnsupported;
          server_driver_local_drain_exhausted = false;
        };
        result
      }
    }
  }
}

fn send_application_data_once
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
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
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
            ST.LocalSendApplicationData
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')
{
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    ST.LocalSendApplicationData
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  process_local_event_and_write_once
    d
    ST.LocalSendApplicationData
    payload
    payload_len
}

fn send_close_notify_once
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
             ST.LocalSendCloseNotify
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
{
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    ST.LocalSendCloseNotify
    B.empty
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  process_empty_local_event_and_write_once
    d
    ST.LocalSendCloseNotify
}

fn send_certificate_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSendCertificate
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
{
  process_empty_local_event_and_write_once
    d
    ST.LocalSendCertificate
}

fn sign_certificate_verify_once
  (d:server_driver)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSignCertificateVerify
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
{
  process_empty_local_event_and_write_once
    d
    ST.LocalSignCertificateVerify
}

fn verify_client_finished_once
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
             ST.LocalVerifyClientFinished
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
{
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    ST.LocalVerifyClientFinished
    B.empty
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  process_empty_local_event_and_write_once
    d
    ST.LocalVerifyClientFinished
}
