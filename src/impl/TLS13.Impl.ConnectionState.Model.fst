module TLS13.Impl.ConnectionState.Model

#lang-pulse

open Pulse.Lib.Pervasives
open FStar.List.Tot

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SM = TLS13.StateMachine
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open TLS13.Impl.ConnectionState.Bounds

let lemma_sizet_lte_plain (x:SZ.t) (y:SZ.t)
  : Lemma (sizet_lte_plain x y == (SZ.v x <= SZ.v y))
=
  ()

let lemma_seal_some_of_keys
  (s:R.direction_state)
  (aad:B.bytes)
  (pt:M.plaintext)
  : Lemma
      (requires (match s.R.key, s.R.static_iv with
                 | Some _, Some _ -> True
                 | _, _ -> False))
      (ensures Some? (R.seal s aad pt))
=
  match s.R.key, s.R.static_iv with
  | Some _, Some _ -> ()
  | _, _ -> ()

let lemma_bounded_u16_sizet_of_sizet
  (n:nat)
  (z:SZ.t)
  : Lemma
      (requires n == SZ.v z /\ n < 65536)
      (ensures bounded_u16_sizet n == z)
=
  SZ.size_v_inj z

let rec lemma_cipher_suites_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Lemma
      (requires IM.cipher_suites_match wire len suites)
      (ensures len == length suites)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match suites with
    | suite :: rest ->
      lemma_cipher_suites_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let rec lemma_signature_schemes_match_length
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes)
      (ensures len == length schemes)
      (decreases len)
=
  if len == 0 then
    ()
  else if len <= Seq.length wire then
    match schemes with
    | scheme :: rest ->
      lemma_signature_schemes_match_length
        (Seq.slice wire 1 (Seq.length wire))
        (len - 1)
        rest
    | [] -> ()
  else
    ()

let lemma_signature_schemes_match_first_rsa_offer
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Lemma
      (requires IM.signature_schemes_match wire len schemes /\
                0 < len /\
                len <= Seq.length wire /\
                U16.v (Seq.index wire 0) == 0x0804)
      (ensures CS.signature_scheme_offered schemes T.RsaPssRsaeSha256)
=
  match schemes with
  | scheme :: _ ->
    assert (IM.signature_scheme_matches (Seq.index wire 0) scheme);
    (match scheme with
    | T.RsaPssRsaeSha256 -> ()
    | T.EcdsaSecp256r1Sha256 -> assert False
    | T.Ed25519 -> assert False
    | T.UnsupportedSignatureScheme _ -> assert False)
  | [] ->
    lemma_signature_schemes_match_length wire len schemes;
    assert False

let lemma_nonempty_cipher_suites_offer
  (suites:list T.cipher_suite)
  (suite:T.cipher_suite)
  : Lemma
      (requires suites <> [])
      (ensures CS.cipher_suite_offered suites suite)
=
  match suites with
  | [] -> ()
  | _ :: _ ->
    match suite with
    | T.TLS_CHACHA20_POLY1305_SHA256 -> ()

let lemma_client_hello_of_start_matches
  (start:CS.handshake_start)
  : Lemma (CS.client_hello_matches_start start (client_hello_of_start start))
=
  ()

let lemma_client_hello_len_helpers_from_start
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (server_name_storage:B.bytes)
  (server_name_len:SZ.t)
  (cipher_suites:Seq.seq U16.t)
  (cipher_suites_len:SZ.t)
  (signature_schemes:Seq.seq U16.t)
  (signature_schemes_len:SZ.t)
  : Lemma
      (requires ch == client_hello_of_start start /\
                B.length server_name_storage == max_hostname_len /\
                B.length start.CS.start_server_name == SZ.v server_name_len /\
                SZ.v server_name_len <= B.length server_name_storage /\
                Seq.length cipher_suites == max_cipher_suites /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                IM.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  start.CS.start_cipher_suites /\
                Seq.length signature_schemes == max_signature_schemes /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                IM.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  start.CS.start_signature_schemes)
      (ensures client_hello_server_name_len_for ch == server_name_len /\
               client_hello_cipher_suites_len_for ch == cipher_suites_len /\
               client_hello_signature_schemes_len_for ch == signature_schemes_len)
=
  assert (ch.M.server_name == Some start.CS.start_server_name);
  assert (B.length start.CS.start_server_name < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (B.length start.CS.start_server_name)
    server_name_len;

  lemma_cipher_suites_match_length
    cipher_suites
    (SZ.v cipher_suites_len)
    start.CS.start_cipher_suites;
  assert (length start.CS.start_cipher_suites == SZ.v cipher_suites_len);
  assert (length start.CS.start_cipher_suites < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (length start.CS.start_cipher_suites)
    cipher_suites_len;

  lemma_signature_schemes_match_length
    signature_schemes
    (SZ.v signature_schemes_len)
    start.CS.start_signature_schemes;
  assert (length start.CS.start_signature_schemes == SZ.v signature_schemes_len);
  assert (length start.CS.start_signature_schemes < 65536);
  lemma_bounded_u16_sizet_of_sizet
    (length start.CS.start_signature_schemes)
    signature_schemes_len

let lemma_application_data_record_count_small
  (bytes:B.bytes)
  : Lemma
      (requires B.length bytes <= SM.max_application_data_fragment_len)
      (ensures SM.application_data_record_count bytes == 1)
=
  SM.lemma_application_data_record_count_len_small (B.length bytes)

let lemma_advance_direction_records_one (s:R.direction_state)
  : Lemma (CS.advance_direction_records s 1 == R.next_seq s)
=
  ()

let lemma_seal_application_success_next_seq
  (s:R.direction_state)
  (aad:B.bytes)
  (payload:B.bytes)
  (ciphertext:B.bytes)
  (s':R.direction_state)
  : Lemma
      (requires R.seal
                  s
                  aad
                  { R.content_type = T.ApplicationData;
                    R.fragment = payload } == Some (ciphertext, s'))
      (ensures s' == R.next_seq s)
=
  match s.R.key, s.R.static_iv with
  | Some _, Some _ -> ()
  | _, _ -> ()

let lemma_local_fail_state_evolves (st:CS.connection_state) (err:T.tls_error)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures CS.connection_state_evolves st (local_fail_state st err) /\
               CS.connection_state_consistent (local_fail_state st err) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (local_fail_state st err))
=
  let delta = {
    CS.delta_event = CS.ConnLocalEvent (CS.LocalFail err);
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_connection_delta st delta (local_fail_state st err));
  assert (CS.connection_state_single_step st (local_fail_state st err));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (local_fail_state st err);
  assert (CS.connection_state_evolves st (local_fail_state st err));
  assert (CS.connection_state_consistent (local_fail_state st err))

let lemma_started_handshake_state_evolves
  (st:CS.connection_state)
  (start:CS.handshake_start)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_start_handshake st start)
      (ensures CS.connection_state_evolves
                 st
                 (started_handshake_state st start) /\
               CS.connection_state_consistent
                 (started_handshake_state st start) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalStartHandshake start);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (started_handshake_state st start))
=
  let ev = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (started_handshake_state st start).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (started_handshake_state st start));
  assert (CS.connection_state_single_step st (started_handshake_state st start));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (started_handshake_state st start);
  assert (CS.connection_state_evolves st (started_handshake_state st start));
  assert (CS.connection_state_consistent (started_handshake_state st start))

let lemma_started_server_state_evolves
  (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_start_server st)
      (ensures CS.connection_state_evolves
                 st
                 (started_server_state st) /\
               CS.connection_state_consistent
                 (started_server_state st) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event = CS.ConnLocalEvent CS.LocalStartServer;
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (started_server_state st))
=
  let ev = CS.ConnLocalEvent CS.LocalStartServer in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (started_server_state st).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (started_server_state st));
  assert (CS.connection_state_single_step st (started_server_state st));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (started_server_state st);
  assert (CS.connection_state_evolves st (started_server_state st));
  assert (CS.connection_state_consistent (started_server_state st))

let lemma_selected_server_parameters_state_evolves
  (st:CS.connection_state)
  (selection:CS.server_handshake_selection)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_select_server_parameters st selection)
      (ensures CS.connection_state_evolves
                 st
                 (selected_server_parameters_state st selection) /\
               CS.connection_state_consistent
                 (selected_server_parameters_state st selection) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (selected_server_parameters_state st selection))
=
  let ev = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (selected_server_parameters_state st selection).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (selected_server_parameters_state st selection));
  assert (CS.connection_state_single_step
    st
    (selected_server_parameters_state st selection));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (selected_server_parameters_state st selection);
  assert (CS.connection_state_evolves
    st
    (selected_server_parameters_state st selection));
  assert (CS.connection_state_consistent
    (selected_server_parameters_state st selection))

let lemma_sent_client_hello_state_evolves
  (st:CS.connection_state)
  (ch:M.client_hello)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_client_hello st ch raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_client_hello_state st ch raw_sent) /\
               CS.connection_state_consistent
                 (sent_client_hello_state st ch raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_hello_state st ch raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_hello_state st ch raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_hello_state st ch raw_sent));
  assert (CS.connection_state_single_step st (sent_client_hello_state st ch raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_client_hello_state st ch raw_sent);
  assert (CS.connection_state_evolves st (sent_client_hello_state st ch raw_sent));
  assert (CS.connection_state_consistent (sent_client_hello_state st ch raw_sent))

let lemma_derived_shared_secret_state_evolves
  (st:CS.connection_state)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)))
      (ensures CS.connection_state_evolves
                 st
                 (derived_shared_secret_state st shared) /\
               CS.connection_state_consistent
                 (derived_shared_secret_state st shared) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st shared))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (derived_shared_secret_state st shared).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (derived_shared_secret_state st shared));
  assert (CS.connection_state_single_step st (derived_shared_secret_state st shared));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (derived_shared_secret_state st shared);
  assert (CS.connection_state_evolves st (derived_shared_secret_state st shared));
  assert (CS.connection_state_consistent (derived_shared_secret_state st shared))

let lemma_installed_traffic_keys_state_evolves
  (st:CS.connection_state)
  (install:CS.traffic_key_install)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures CS.connection_state_evolves
                 st
                 (installed_traffic_keys_state st install) /\
               CS.connection_state_consistent
                 (installed_traffic_keys_state st install) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st install))
=
  let ev = CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (installed_traffic_keys_state st install).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (installed_traffic_keys_state st install));
  assert (CS.connection_state_single_step st (installed_traffic_keys_state st install));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (installed_traffic_keys_state st install);
  assert (CS.connection_state_evolves st (installed_traffic_keys_state st install));
  assert (CS.connection_state_consistent (installed_traffic_keys_state st install))

let lemma_installed_traffic_keys_for_role_state_evolves
  (st:CS.connection_state)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures CS.connection_state_evolves
                 st
                 (installed_traffic_keys_for_role_state st role_install) /\
               CS.connection_state_consistent
                 (installed_traffic_keys_for_role_state st role_install) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeysForRole role_install);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_for_role_state st role_install))
=
  let ev =
    CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole role_install) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (installed_traffic_keys_for_role_state st role_install).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (installed_traffic_keys_for_role_state st role_install));
  assert (CS.connection_state_single_step
    st
    (installed_traffic_keys_for_role_state st role_install));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (installed_traffic_keys_for_role_state st role_install);
  assert (CS.connection_state_evolves
    st
    (installed_traffic_keys_for_role_state st role_install));
  assert (CS.connection_state_consistent
    (installed_traffic_keys_for_role_state st role_install))

let lemma_validated_certificate_state_evolves
  (st:CS.connection_state)
  (peer:X.peer_identity)
  : Lemma
      (requires CS.connection_state_consistent st /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)))
      (ensures CS.connection_state_evolves
                 st
                 (validated_certificate_state st peer) /\
               CS.connection_state_consistent
                 (validated_certificate_state st peer) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (validated_certificate_state st peer))
=
  let ev = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.step_model st.CS.cs_model ev ==
          Some (validated_certificate_state st peer).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta st delta (validated_certificate_state st peer));
  assert (CS.connection_state_single_step st (validated_certificate_state st peer));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (validated_certificate_state st peer);
  assert (CS.connection_state_evolves st (validated_certificate_state st peer));
  assert (CS.connection_state_consistent (validated_certificate_state st peer))

let lemma_client_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.client_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_handshake_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.server_handshake_traffic_secret
                  handshake_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_role_server_handshake_write_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (K.server_handshake_traffic_secret
                    handshake_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_server_role_client_handshake_read_traffic_install_legal
  (model:CS.connection_model)
  (handshake_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
                  Some handshake_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (K.client_handshake_traffic_secret
                    handshake_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_client_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.client_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_application_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material =
              CS.traffic_key_material_for_secret
                (K.server_application_traffic_secret
                  master_secret
                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
          })))
=
  ()

let lemma_server_role_server_application_write_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedSent /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (K.server_application_traffic_secret
                    master_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_server_role_client_application_read_traffic_install_legal
  (model:CS.connection_model)
  (master_secret:TLS13.Crypto.Spec.secret)
  : Lemma
      (requires model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientFinishedReceived /\
                model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret ==
                  Some master_secret)
      (ensures CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material =
                CS.traffic_key_material_for_secret
                  (K.client_application_traffic_secret
                    master_secret
                    (Tr.hash model.CS.model_handshake.CS.hs_transcript));
            };
          })))
=
  ()

let lemma_received_hello_retry_request_rejected_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_hello_retry_request_rejected_state st raw_received) /\
               CS.connection_state_consistent
                 (received_hello_retry_request_rejected_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_hello_retry_request_rejected_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake M.HelloRetryRequest;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model tls_hello_retry_request_rejected_error));
  assert (CS.legal_connection_delta
    st
    delta
    (received_hello_retry_request_rejected_state st raw_received));
  assert (CS.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_hello_retry_request_rejected_state st raw_received);
  assert (CS.connection_state_evolves
    st
    (received_hello_retry_request_rejected_state st raw_received));
  assert (CS.connection_state_consistent
    (received_hello_retry_request_rejected_state st raw_received))

let lemma_received_change_cipher_spec_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                (exists stage.
                  st.CS.cs_model.CS.model_control == CS.ControlHandshaking stage) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsChangeCipherSpec;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_change_cipher_spec_state st raw_received) /\
               CS.connection_state_consistent
                 (received_change_cipher_spec_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsChangeCipherSpec;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_change_cipher_spec_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsChangeCipherSpec;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev == Some st.CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_change_cipher_spec_state st raw_received));
  assert (CS.connection_state_single_step st (received_change_cipher_spec_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_change_cipher_spec_state st raw_received);
  assert (CS.connection_state_evolves st (received_change_cipher_spec_state st raw_received));
  assert (CS.connection_state_consistent (received_change_cipher_spec_state st raw_received))

let lemma_received_server_hello_state_evolves
  (st:CS.connection_state)
  (sh:M.server_hello)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloSent /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  }) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_server_hello_state st sh raw_received) /\
               CS.connection_state_consistent
                 (received_server_hello_state st sh raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_hello_state st sh raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_hello_state st sh raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_server_hello_state st sh raw_received));
  assert (CS.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_server_hello_state st sh raw_received);
  assert (CS.connection_state_evolves
    st
    (received_server_hello_state st sh raw_received));
  assert (CS.connection_state_consistent
    (received_server_hello_state st sh raw_received))

let lemma_sent_server_hello_state_evolves
  (st:CS.connection_state)
  (sh:M.server_hello)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_server_hello st sh raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_server_hello_state st sh raw_sent) /\
               CS.connection_state_consistent
                 (sent_server_hello_state st sh raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_server_hello_state st sh raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_server_hello_state st sh raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_server_hello_state st sh raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_server_hello_state st sh raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_server_hello_state st sh raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_server_hello_state st sh raw_sent));
  assert (CS.connection_state_consistent
    (sent_server_hello_state st sh raw_sent))

let lemma_sent_encrypted_extensions_state_evolves
  (st:CS.connection_state)
  (ee:M.encrypted_extensions)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_encrypted_extensions st ee raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_encrypted_extensions_state st ee raw_sent) /\
               CS.connection_state_consistent
                 (sent_encrypted_extensions_state st ee raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_encrypted_extensions_state st ee raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_encrypted_extensions_state st ee raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_encrypted_extensions_state st ee raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_encrypted_extensions_state st ee raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_encrypted_extensions_state st ee raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_encrypted_extensions_state st ee raw_sent));
  assert (CS.connection_state_consistent
    (sent_encrypted_extensions_state st ee raw_sent))

let lemma_sent_certificate_state_evolves
  (st:CS.connection_state)
  (cert:M.certificate_msg)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_certificate st cert raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_certificate_state st cert raw_sent) /\
               CS.connection_state_consistent
                 (sent_certificate_state st cert raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Certificate cert);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_certificate_state st cert raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_certificate_state st cert raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_certificate_state st cert raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_certificate_state st cert raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_certificate_state st cert raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_certificate_state st cert raw_sent));
  assert (CS.connection_state_consistent
    (sent_certificate_state st cert raw_sent))

let lemma_signed_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_sign_certificate_verify st cv)
      (ensures CS.connection_state_evolves
                 st
                 (signed_certificate_verify_state st cv) /\
               CS.connection_state_consistent
                 (signed_certificate_verify_state st cv) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (signed_certificate_verify_state st cv))
=
  let ev = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (signed_certificate_verify_state st cv).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (signed_certificate_verify_state st cv));
  assert (CS.connection_state_single_step
    st
    (signed_certificate_verify_state st cv));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (signed_certificate_verify_state st cv);
  assert (CS.connection_state_evolves
    st
    (signed_certificate_verify_state st cv));
  assert (CS.connection_state_consistent
    (signed_certificate_verify_state st cv))

let lemma_sent_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_certificate_verify st cv raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_certificate_verify_state st cv raw_sent) /\
               CS.connection_state_consistent
                 (sent_certificate_verify_state st cv raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_certificate_verify_state st cv raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_certificate_verify_state st cv raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_certificate_verify_state st cv raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_certificate_verify_state st cv raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_certificate_verify_state st cv raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_certificate_verify_state st cv raw_sent));
  assert (CS.connection_state_consistent
    (sent_certificate_verify_state st cv raw_sent))

let lemma_sent_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_server_finished st fin raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_server_finished_state st fin raw_sent) /\
               CS.connection_state_consistent
                 (sent_server_finished_state st fin raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_server_finished_state st fin raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_server_finished_state st fin raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_server_finished_state st fin raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_server_finished_state st fin raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_server_finished_state st fin raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_server_finished_state st fin raw_sent));
  assert (CS.connection_state_consistent
    (sent_server_finished_state st fin raw_sent))

let lemma_received_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_receive_client_finished st fin raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_client_finished_state st fin raw_received) /\
               CS.connection_state_consistent
                 (received_client_finished_state st fin raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_client_finished_state st fin raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty raw_received);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_client_finished_state st fin raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_client_finished_state st fin raw_received));
  assert (CS.connection_state_single_step
    st
    (received_client_finished_state st fin raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_client_finished_state st fin raw_received);
  assert (CS.connection_state_evolves
    st
    (received_client_finished_state st fin raw_received));
  assert (CS.connection_state_consistent
    (received_client_finished_state st fin raw_received))

let lemma_verified_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_verify_client_finished st fin)
      (ensures CS.connection_state_evolves
                 st
                 (verified_client_finished_state st fin) /\
               CS.connection_state_consistent
                 (verified_client_finished_state st fin) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_client_finished_state st fin))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_client_finished_state st fin).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.legal_connection_delta
    st
    delta
    (verified_client_finished_state st fin));
  assert (CS.connection_state_single_step
    st
    (verified_client_finished_state st fin));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (verified_client_finished_state st fin);
  assert (CS.connection_state_evolves
    st
    (verified_client_finished_state st fin));
  assert (CS.connection_state_consistent
    (verified_client_finished_state st fin))

let lemma_received_client_hello_state_evolves
  (st:CS.connection_state)
  (ch:M.client_hello)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsAwaitingClientHello /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_client_hello_state st ch raw_received) /\
               CS.connection_state_consistent
                 (received_client_hello_state st ch raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_client_hello_state st ch raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_client_hello_state st ch raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_client_hello_state st ch raw_received));
  assert (CS.connection_state_single_step
    st
    (received_client_hello_state st ch raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_client_hello_state st ch raw_received);
  assert (CS.connection_state_evolves
    st
    (received_client_hello_state st ch raw_received));
  assert (CS.connection_state_consistent
    (received_client_hello_state st ch raw_received))

let lemma_received_encrypted_extensions_state_evolves
  (st:CS.connection_state)
  (ee:M.encrypted_extensions)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerHelloReceived /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_encrypted_extensions_state st ee raw_received) /\
               CS.connection_state_consistent
                 (received_encrypted_extensions_state st ee raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_encrypted_extensions_state st ee raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_encrypted_extensions_state st ee raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_encrypted_extensions_state st ee raw_received));
  assert (CS.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_encrypted_extensions_state st ee raw_received);
  assert (CS.connection_state_evolves
    st
    (received_encrypted_extensions_state st ee raw_received));
  assert (CS.connection_state_consistent
    (received_encrypted_extensions_state st ee raw_received))

let lemma_received_certificate_state_evolves
  (st:CS.connection_state)
  (cert:M.certificate_msg)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                cert.M.chain <> [] /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Certificate cert);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_certificate_state st cert raw_received) /\
               CS.connection_state_consistent
                 (received_certificate_state st cert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Certificate cert);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_state st cert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_state st cert raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_state st cert raw_received));
  assert (CS.connection_state_single_step
    st
    (received_certificate_state st cert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_certificate_state st cert raw_received);
  assert (CS.connection_state_evolves
    st
    (received_certificate_state st cert raw_received));
  assert (CS.connection_state_consistent
    (received_certificate_state st cert raw_received))

let lemma_received_certificate_verify_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateValidated /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some?
                  st.CS.cs_model.CS.model_handshake.CS.hs_validated_peer /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_certificate_verify_state st cv raw_received) /\
               CS.connection_state_consistent
                 (received_certificate_verify_state st cv raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_certificate_verify_state st cv raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_certificate_verify_state st cv raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_certificate_verify_state st cv raw_received));
  assert (CS.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_certificate_verify_state st cv raw_received);
  assert (CS.connection_state_evolves
    st
    (received_certificate_verify_state st cv raw_received));
  assert (CS.connection_state_consistent
    (received_certificate_verify_state st cv raw_received))

let lemma_verified_certificate_signature_state_evolves
  (st:CS.connection_state)
  (cv:M.certificate_verify)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)))
      (ensures CS.connection_state_evolves
                 st
                 (verified_certificate_signature_state st cv) /\
               CS.connection_state_consistent
                 (verified_certificate_signature_state st cv) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_certificate_signature_state st cv))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_certificate_signature_state st cv).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_certificate_signature_state st cv));
  assert (CS.connection_state_single_step st (verified_certificate_signature_state st cv));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (verified_certificate_signature_state st cv);
  assert (CS.connection_state_evolves st (verified_certificate_signature_state st cv));
  assert (CS.connection_state_consistent (verified_certificate_signature_state st cv))

let lemma_received_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
      Some?
        st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
      CS.event_raw_delta_legal
        st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Finished fin);
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_server_finished_state st fin raw_received) /\
               CS.connection_state_consistent
                 (received_server_finished_state st fin raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_server_finished_state st fin raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_server_finished_state st fin raw_received).CS.cs_model);
  assert (CS.legal_connection_delta st delta (received_server_finished_state st fin raw_received));
  assert (CS.connection_state_single_step st (received_server_finished_state st fin raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_server_finished_state st fin raw_received);
  assert (CS.connection_state_evolves st (received_server_finished_state st fin raw_received));
  assert (CS.connection_state_consistent (received_server_finished_state st fin raw_received))

let lemma_verified_server_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedReceived /\
                st.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some fin /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)))
      (ensures CS.connection_state_evolves
                 st
                 (verified_server_finished_state st fin) /\
               CS.connection_state_consistent
                 (verified_server_finished_state st fin) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalVerifyFinished fin);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (verified_server_finished_state st fin))
=
  let ev = CS.ConnLocalEvent (CS.LocalVerifyFinished fin) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.step_model st.CS.cs_model ev ==
          Some (verified_server_finished_state st fin).CS.cs_model);
  assert (CS.legal_connection_delta st delta (verified_server_finished_state st fin));
  assert (CS.connection_state_single_step st (verified_server_finished_state st fin));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (verified_server_finished_state st fin);
  assert (CS.connection_state_evolves st (verified_server_finished_state st fin));
  assert (CS.connection_state_consistent (verified_server_finished_state st fin))

let lemma_sent_client_finished_state_evolves
  (st:CS.connection_state)
  (fin:M.finished)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_client_finished st fin raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_client_finished_state st fin raw_sent) /\
               CS.connection_state_consistent
                 (sent_client_finished_state st fin raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.Finished fin);
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_client_finished_state st fin raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished fin);
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_client_finished_state st fin raw_sent).CS.cs_model);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.legal_connection_delta st delta (sent_client_finished_state st fin raw_sent));
  assert (CS.connection_state_single_step st (sent_client_finished_state st fin raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_client_finished_state st fin raw_sent);
  assert (CS.connection_state_evolves st (sent_client_finished_state st fin raw_sent));
  assert (CS.connection_state_consistent (sent_client_finished_state st fin raw_sent))

let lemma_received_alert_failure_state_evolves
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                alert <> T.CloseNotify /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert alert;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_alert_failure_state st alert raw_received) /\
               CS.connection_state_consistent
                 (received_alert_failure_state st alert raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert alert;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_alert_failure_state st alert raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert alert;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (CS.fail_model st.CS.cs_model (T.AlertError alert)));
  assert (CS.legal_connection_delta st delta (received_alert_failure_state st alert raw_received));
  assert (CS.connection_state_single_step st (received_alert_failure_state st alert raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_alert_failure_state st alert raw_received);
  assert (CS.connection_state_evolves st (received_alert_failure_state st alert raw_received));
  assert (CS.connection_state_consistent (received_alert_failure_state st alert raw_received))

let lemma_received_close_notify_state_evolves_for_role
  (role:CS.endpoint_role)
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                (st.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  role /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.CloseNotify;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_close_notify_state st raw_received) /\
               CS.connection_state_consistent
                 (received_close_notify_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert T.CloseNotify;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_close_notify_state st raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsAlert T.CloseNotify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_close_notify_state st raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_close_notify_state st raw_received));
  assert (CS.connection_state_single_step
    st
    (received_close_notify_state st raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_close_notify_state st raw_received);
  assert (CS.connection_state_evolves
    st
    (received_close_notify_state st raw_received));
  assert (CS.connection_state_consistent
    (received_close_notify_state st raw_received))

let lemma_received_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                (st.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
                 st.CS.cs_model.CS.model_control == CS.ControlClosing) /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsAlert T.CloseNotify;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_close_notify_state st raw_received) /\
               CS.connection_state_consistent
                 (received_close_notify_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsAlert T.CloseNotify;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_close_notify_state st raw_received))
=
  lemma_received_close_notify_state_evolves_for_role
    CS.ClientEndpoint
    st
    raw_received

let lemma_sent_close_notify_state_evolves
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_close_notify st raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_close_notify_state st raw_sent) /\
               CS.connection_state_consistent
                 (sent_close_notify_state st raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsAlert T.CloseNotify;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_close_notify_state st raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.CloseNotify;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_close_notify_state st raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_close_notify_state st raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_close_notify_state st raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_close_notify_state st raw_sent));
  assert (CS.connection_state_consistent
    (sent_close_notify_state st raw_sent))

let lemma_received_application_data_state_evolves_for_role
  (role:CS.endpoint_role)
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role == role /\
                CS.application_traffic_available_for_role
                  role
                  st.CS.cs_model.CS.model_handshake
                  CL.Received /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_application_data_state st bytes raw_received) /\
               CS.connection_state_consistent
                 (received_application_data_state st bytes raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_application_data_state st bytes raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_tls_message st.CS.cs_model CL.Received (M.TlsApplicationData bytes));
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_application_data_state st bytes raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_application_data_state st bytes raw_received));
  assert (CS.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_application_data_state st bytes raw_received);
  assert (CS.connection_state_evolves
    st
    (received_application_data_state st bytes raw_received));
  assert (CS.connection_state_consistent
    (received_application_data_state st bytes raw_received))

let lemma_received_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsApplicationData bytes;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_application_data_state st bytes raw_received) /\
               CS.connection_state_consistent
                 (received_application_data_state st bytes raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_application_data_state st bytes raw_received))
=
  assert_norm (CS.traffic_label_for_endpoint_direction
    CS.ClientEndpoint
    CS.TrafficRead == CS.ServerTraffic);
  assert (CS.application_traffic_available_for_role
    CS.ClientEndpoint
    st.CS.cs_model.CS.model_handshake
    CL.Received);
  lemma_received_application_data_state_evolves_for_role
    CS.ClientEndpoint
    st
    bytes
    raw_received

let lemma_received_ignored_post_handshake_state_evolves
  (st:CS.connection_state)
  (body:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsIgnoredPostHandshake body;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_ignored_post_handshake_state st body raw_received) /\
               CS.connection_state_consistent
                 (received_ignored_post_handshake_state st body raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsIgnoredPostHandshake body;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_ignored_post_handshake_state st body raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsIgnoredPostHandshake body;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_ignored_post_handshake_state st body raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_ignored_post_handshake_state st body raw_received));
  assert (CS.connection_state_single_step
    st
    (received_ignored_post_handshake_state st body raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_ignored_post_handshake_state st body raw_received);
  assert (CS.connection_state_evolves
    st
    (received_ignored_post_handshake_state st body raw_received));
  assert (CS.connection_state_consistent
    (received_ignored_post_handshake_state st body raw_received))

let lemma_received_key_update_state_evolves
  (st:CS.connection_state)
  (req:M.key_update_request)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsKeyUpdate req;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_key_update_state st req raw_received) /\
               CS.connection_state_consistent
                 (received_key_update_state st req raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                      CL.message_value = M.TlsKeyUpdate req;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_key_update_state st req raw_received))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsKeyUpdate req;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = raw_received;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (received_key_update_state st req raw_received).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (received_key_update_state st req raw_received));
  assert (CS.connection_state_single_step
    st
    (received_key_update_state st req raw_received));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (received_key_update_state st req raw_received);
  assert (CS.connection_state_evolves
    st
    (received_key_update_state st req raw_received));
  assert (CS.connection_state_consistent
    (received_key_update_state st req raw_received))

let lemma_received_key_update_not_requested_state_evolves
  (st:CS.connection_state)
  (raw_received:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                st.CS.cs_model.CS.model_config.CS.config_role ==
                  CS.ClientEndpoint /\
                Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
                CS.event_raw_delta_legal
                  st.CS.cs_model
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                  })
                  B.empty
                  raw_received)
      (ensures CS.connection_state_evolves
                 st
                 (received_key_update_not_requested_state st raw_received) /\
               CS.connection_state_consistent
                 (received_key_update_not_requested_state st raw_received) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Received;
                       CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                     };
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = raw_received;
                 }
                 (received_key_update_not_requested_state st raw_received))
=
  lemma_received_key_update_state_evolves st M.UpdateNotRequested raw_received

let lemma_sent_key_update_response_state_evolves
  (st:CS.connection_state)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_key_update st raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_key_update_response_state st raw_sent) /\
               CS.connection_state_consistent
                 (sent_key_update_response_state st raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_key_update_response_state st raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsKeyUpdate M.UpdateNotRequested;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_key_update_response_state st raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta
    st
    delta
    (sent_key_update_response_state st raw_sent));
  assert (CS.connection_state_single_step
    st
    (sent_key_update_response_state st raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_key_update_response_state st raw_sent);
  assert (CS.connection_state_evolves
    st
    (sent_key_update_response_state st raw_sent));
  assert (CS.connection_state_consistent
    (sent_key_update_response_state st raw_sent))

let lemma_delivered_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                CS.legal_event
                  st.CS.cs_model
                  (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)))
      (ensures CS.connection_state_evolves
                 st
                 (delivered_application_data_state st bytes) /\
               CS.connection_state_consistent
                 (delivered_application_data_state st bytes) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (delivered_application_data_state st bytes))
=
  let ev = CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = B.empty;
    CS.delta_raw_received = B.empty;
  } in
  Seq.lemma_eq_intro B.empty B.empty;
  assert (CS.event_raw_delta_legal st.CS.cs_model ev B.empty B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (delivered_application_data_state st bytes).CS.cs_model);
  assert (CS.legal_connection_delta st delta (delivered_application_data_state st bytes));
  assert (CS.connection_state_single_step st (delivered_application_data_state st bytes));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (delivered_application_data_state st bytes);
  assert (CS.connection_state_evolves st (delivered_application_data_state st bytes));
  assert (CS.connection_state_consistent (delivered_application_data_state st bytes))

let lemma_sent_application_data_state_evolves
  (st:CS.connection_state)
  (bytes:B.bytes)
  (raw_sent:B.bytes)
  : Lemma
      (requires CS.connection_state_consistent st /\
                can_send_application_data st bytes raw_sent)
      (ensures CS.connection_state_evolves
                 st
                 (sent_application_data_state st bytes raw_sent) /\
               CS.connection_state_consistent
                 (sent_application_data_state st bytes raw_sent) /\
               CS.legal_connection_delta
                 st
                 {
                   CS.delta_event =
                     CS.ConnNetworkEvent {
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsApplicationData bytes;
                     };
                   CS.delta_raw_sent = raw_sent;
                   CS.delta_raw_received = B.empty;
                 }
                 (sent_application_data_state st bytes raw_sent))
=
  let ev =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData bytes;
    } in
  let delta = {
    CS.delta_event = ev;
    CS.delta_raw_sent = raw_sent;
    CS.delta_raw_received = B.empty;
  } in
  lemma_application_data_record_count_small bytes;
  lemma_advance_direction_records_one st.CS.cs_model.CS.model_record.CS.record_write;
  assert (CS.legal_event st.CS.cs_model ev);
  assert (CS.event_raw_delta_legal st.CS.cs_model ev raw_sent B.empty);
  assert (CS.step_model st.CS.cs_model ev ==
          Some (sent_application_data_state st bytes raw_sent).CS.cs_model);
  assert (CS.legal_connection_delta st delta (sent_application_data_state st bytes raw_sent));
  assert (CS.connection_state_single_step st (sent_application_data_state st bytes raw_sent));
  FStar.ReflexiveTransitiveClosure.closure_step
    CS.connection_state_single_step
    st
    (sent_application_data_state st bytes raw_sent);
  assert (CS.connection_state_evolves st (sent_application_data_state st bytes raw_sent));
  assert (CS.connection_state_consistent (sent_application_data_state st bytes raw_sent))
