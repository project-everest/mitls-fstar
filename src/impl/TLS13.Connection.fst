module TLS13.Connection

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Cast = FStar.Int.Cast
module CL = TLS13.ConnectionLog
module E = TLS13.Connection.External
module H = TLS13.Handshake.Spec
module IO = TLS13.IO
module Rec = TLS13.Record
module RF = TLS13.Record.Framing
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module X = TLS13.X509.Spec

let lemma_nat_add_sub_cancel
  (a:nat)
  (b:nat)
  (c:nat{b <= c})
  : Lemma (a + b + (c - b) == a + c)
=
  ()

noeq
type connection = {
  backend: E.connection;
  live: box bool;
  client_application_key: V.vec U8.t;
  client_application_iv: V.vec U8.t;
  server_application_key: V.vec U8.t;
  server_application_iv: V.vec U8.t;
  client_application_record_state: Rec.record_state;
  server_application_record_state: Rec.record_state;
  application_keys_installed: box bool;
  pending_read_buffer: V.vec U8.t;
  pending_read_offset: box SZ.t;
  pending_read_len: box SZ.t;
  log: ST.log_ref;  // Ghost log for layered correctness proof
}

let connection_exactly (c:connection) (st:ST.state_ref) (s:S.conn_state) (view:CL.connection_view) : slprop =
  exists* live app_keys_installed pending_read_offset pending_read_len
          client_key client_iv server_key server_iv pending_read_buffer
          client_record_state server_record_state.
    E.is_connection c.backend **
    Box.pts_to c.live live **
    Box.pts_to c.application_keys_installed app_keys_installed **
    Box.pts_to c.pending_read_offset pending_read_offset **
    Box.pts_to c.pending_read_len pending_read_len **
    V.pts_to c.client_application_key client_key **
    V.pts_to c.client_application_iv client_iv **
    V.pts_to c.server_application_key server_key **
    V.pts_to c.server_application_iv server_iv **
    V.pts_to c.pending_read_buffer pending_read_buffer **
    Rec.is_record_state c.client_application_record_state client_record_state **
    Rec.is_record_state c.server_application_record_state server_record_state **
    ST.current st s **
    ST.log_current c.log view **
    pure (V.is_full_vec c.client_application_key /\
          V.is_full_vec c.client_application_iv /\
          V.is_full_vec c.server_application_key /\
          V.is_full_vec c.server_application_iv /\
          V.is_full_vec c.pending_read_buffer /\
          V.length c.client_application_key == 32 /\
          V.length c.client_application_iv == 12 /\
          V.length c.server_application_key == 32 /\
          V.length c.server_application_iv == 12 /\
          V.length c.pending_read_buffer == 4096 /\
          SZ.v pending_read_offset <= SZ.v pending_read_len /\
          SZ.v pending_read_len <= 4096 /\
          CL.connection_view_consistent view /\
          view.CL.state == s)

let is_connection (c:connection) (st:ST.state_ref) (s:S.conn_state) : slprop =
  exists* view. connection_exactly c st s view

ghost
fn reveal_connection_view (c: connection)
  requires is_connection c 'st 's
  ensures exists* view. connection_exactly c 'st 's view
{
  unfold (is_connection c 'st 's);
}

ghost
fn hide_connection_view (c: connection)
  requires connection_exactly c 'st 's 'view
  ensures is_connection c 'st 's
{
  fold (is_connection c 'st 's);
}

let zeros32 : B.bytes = B.zeros 32
let app_record_chunk_len : SZ.t = 4096sz
let pending_read_buffer_capacity : SZ.t = 4096sz
let max_application_read_records : U8.t = 255uy
let read_status_failed : U8.t = 0uy
let read_status_complete : U8.t = 1uy
let read_status_close_notify : U8.t = 2uy
let read_status_alert_decode_error : U8.t = 3uy
let read_status_alert_unexpected_message : U8.t = 4uy
let read_status_alert_bad_record_mac : U8.t = 5uy
let read_status_alert_handshake_failure : U8.t = 6uy
let read_status_alert_decrypt_error : U8.t = 7uy
let read_status_alert_protocol_version : U8.t = 8uy
let read_status_alert_unsupported_extension : U8.t = 9uy
let read_status_alert_certificate_unknown : U8.t = 10uy
let read_status_alert_illegal_parameter : U8.t = 11uy

let dummy_client_hello : H.client_hello = {
  H.random = zeros32;
  H.server_name = None;
  H.key_share = zeros32;
  H.cipher_suites = [T.TLS_CHACHA20_POLY1305_SHA256];
  H.signature_schemes = [T.RsaPssRsaeSha256];
}

let dummy_server_hello : H.server_hello = {
  H.random = zeros32;
  H.key_share = zeros32;
  H.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
}

let dummy_encrypted_extensions : H.encrypted_extensions = {
  H.negotiated_alpn = None;
}

let dummy_certificate : H.certificate_msg = {
  H.chain = [];
}

let dummy_peer : X.peer_identity = {
  X.validated_hostname = B.empty;
  X.leaf_public_key = B.empty;
  X.permitted_signature_schemes = [T.RsaPssRsaeSha256];
}

let dummy_certificate_verify : H.certificate_verify = {
  H.scheme = T.RsaPssRsaeSha256;
  H.signature = B.empty;
}

let dummy_finished : H.finished = {
  H.verify_data = zeros32;
}

let hs_client_hello_sent (s:S.conn_state) = S.with_phase s S.ClientHelloSent
let hs_server_hello_received (s:S.conn_state) = S.with_phase (hs_client_hello_sent s) S.ServerHelloReceived
let hs_encrypted_extensions_received (s:S.conn_state) = S.with_phase (hs_server_hello_received s) S.EncryptedExtensionsReceived
let hs_certificate_received (s:S.conn_state) = S.with_phase (hs_encrypted_extensions_received s) S.CertificateReceived
let hs_certificate_validated (s:S.conn_state) = S.with_validated_peer (hs_certificate_received s) dummy_peer
let hs_certificate_verified (s:S.conn_state) = S.with_phase (hs_certificate_validated s) S.CertificateVerified
let hs_server_finished_verified (s:S.conn_state) = S.with_phase (hs_certificate_verified s) S.ServerFinishedVerified
let hs_application_data (s:S.conn_state) = S.with_phase (hs_server_finished_verified s) S.ApplicationData

let lemma_successful_handshake_state_evolves
  (s:S.conn_state)
  : Lemma
      (requires s.S.phase == S.Start)
      (ensures S.conn_evolves s (hs_application_data s))
  =
  let s1 = hs_client_hello_sent s in
  let s2 = hs_server_hello_received s in
  let s3 = hs_encrypted_extensions_received s in
  let s4 = hs_certificate_received s in
  let s5 = hs_certificate_validated s in
  let s6 = hs_certificate_verified s in
  let s7 = hs_server_finished_verified s in
  let s8 = hs_application_data s in
  assert (S.step s (S.SendClientHello dummy_client_hello) == Some s1);
  assert (S.state_single_step s s1);
  RTC.closure_step S.state_single_step s s1;
  assert (S.step s1 (S.RecvServerHello dummy_server_hello) == Some s2);
  assert (S.state_single_step s1 s2);
  RTC.closure_step S.state_single_step s1 s2;
  assert (S.step s2 (S.RecvEncryptedExtensions dummy_encrypted_extensions) == Some s3);
  assert (S.state_single_step s2 s3);
  RTC.closure_step S.state_single_step s2 s3;
  assert (S.step s3 (S.RecvCertificate dummy_certificate) == Some s4);
  assert (S.state_single_step s3 s4);
  RTC.closure_step S.state_single_step s3 s4;
  assert (S.step s4 (S.ValidateCertificate dummy_peer) == Some s5);
  assert (S.state_single_step s4 s5);
  RTC.closure_step S.state_single_step s4 s5;
  assert (S.step s5 (S.RecvCertificateVerify dummy_certificate_verify) == Some s6);
  assert (S.state_single_step s5 s6);
  RTC.closure_step S.state_single_step s5 s6;
  assert (S.step s6 (S.RecvServerFinished dummy_finished) == Some s7);
  assert (S.state_single_step s6 s7);
  RTC.closure_step S.state_single_step s6 s7;
  assert (S.step s7 (S.SendClientFinished dummy_finished) == Some s8);
  assert (S.state_single_step s7 s8);
  RTC.closure_step S.state_single_step s7 s8;
  assert (RTC.transitive S.conn_evolves);
  assert (S.conn_evolves s s2);
  assert (S.conn_evolves s s3);
  assert (S.conn_evolves s s4);
  assert (S.conn_evolves s s5);
  assert (S.conn_evolves s s6);
  assert (S.conn_evolves s s7);
  assert (S.conn_evolves s s8)

ghost
fn advance_successful_handshake (st:ST.state_ref) (#s:S.conn_state)
  requires ST.current st s
  requires pure (s.S.phase == S.Start)
  ensures ST.current st (hs_application_data s)
{
  ST.advance st (S.SendClientHello dummy_client_hello) (hs_client_hello_sent s);
  ST.advance st (S.RecvServerHello dummy_server_hello) (hs_server_hello_received s);
  ST.advance st (S.RecvEncryptedExtensions dummy_encrypted_extensions) (hs_encrypted_extensions_received s);
  ST.advance st (S.RecvCertificate dummy_certificate) (hs_certificate_received s);
  ST.advance st (S.ValidateCertificate dummy_peer) (hs_certificate_validated s);
  ST.advance st (S.RecvCertificateVerify dummy_certificate_verify) (hs_certificate_verified s);
  ST.advance st (S.RecvServerFinished dummy_finished) (hs_server_finished_verified s);
  ST.advance st (S.SendClientFinished dummy_finished) (hs_application_data s);
}

let received_alert_event (alert:T.alert_description) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Received; CL.message_value = CL.TlsAlert alert }

let sent_handshake_event (msg:H.handshake_msg) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Sent; CL.message_value = CL.TlsHandshake msg }

let received_handshake_event (msg:H.handshake_msg) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Received; CL.message_value = CL.TlsHandshake msg }

let hs_log_view1 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (sent_handshake_event (H.ClientHello dummy_client_hello)) (hs_client_hello_sent s)

let hs_log_view2 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view1 view s) (received_handshake_event (H.ServerHello dummy_server_hello)) (hs_server_hello_received s)

let hs_log_view3 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view2 view s) (received_handshake_event (H.EncryptedExtensions dummy_encrypted_extensions)) (hs_encrypted_extensions_received s)

let hs_log_view4 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view3 view s) (received_handshake_event (H.Certificate dummy_certificate)) (hs_certificate_received s)

let hs_log_view5 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view4 view s) (CL.LocalEvent (CL.LocalValidateCertificate dummy_peer)) (hs_certificate_validated s)

let hs_log_view6 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view5 view s) (received_handshake_event (H.CertificateVerify dummy_certificate_verify)) (hs_certificate_verified s)

let hs_log_view7 (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view6 view s) (received_handshake_event (H.Finished dummy_finished)) (hs_server_finished_verified s)

let successful_handshake_view (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view7 view s) (sent_handshake_event (H.Finished dummy_finished)) (hs_application_data s)

let note_sent_app_view (view:CL.connection_view) (bytes:B.bytes) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (CL.sent_app_event bytes) (S.advance_write_records s (S.application_data_record_count bytes))

let note_recv_app_view (view:CL.connection_view) (bytes:B.bytes) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (CL.received_app_event bytes) (S.advance_read_record s)

let note_local_fail_view (view:CL.connection_view) (err:T.tls_error) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (CL.local_fail_event err) (S.fail s err)

let note_recv_alert_view (view:CL.connection_view) (alert:T.alert_description) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (received_alert_event alert) (S.fail s (T.AlertError alert))

let note_recv_close_view (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view CL.received_close_notify_event (S.recv_close_state s)

let note_send_close_view (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view CL.sent_close_notify_event (S.send_close_state s)

ghost
fn advance_log_event
  (log:ST.log_ref)
  (#view:CL.connection_view)
  (ev:CL.host_event)
  (state_ev:S.event)
  (state:S.conn_state)
  requires ST.log_current log view
  requires pure (CL.connection_view_consistent view /\
                 CL.state_event_of_host_event ev == Some state_ev /\
                 S.step view.CL.state state_ev == Some state)
  ensures ST.log_current log (CL.note_host_event view ev state) **
          pure (CL.connection_view_consistent (CL.note_host_event view ev state) /\
                (CL.note_host_event view ev state).CL.state == state /\
                CL.connection_view_single_step view (CL.note_host_event view ev state))
{
  let next = CL.note_host_event view ev state;
  CL.lemma_connection_view_consistent_note_host_event view ev state_ev state;
  CL.lemma_connection_view_step_host_event view ev state;
  ST.advance_log log next;
}

ghost
fn advance_log_raw_sent_slice
  (log:ST.log_ref)
  (#view:CL.connection_view)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat)
  requires ST.log_current log view
  requires pure (CL.connection_view_consistent view /\
                 lo <= hi /\ hi <= B.length bytes)
  ensures ST.log_current log (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state) **
          pure (CL.connection_view_consistent (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state) /\
                (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.state == view.CL.state /\
                (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.app_view == view.CL.app_view /\
                CL.raw_io_log_extends view.CL.raw_log
                  (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.raw_log /\
                CL.raw_io_log_same_received view.CL.raw_log
                  (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.raw_log /\
                CL.connection_view_single_step view (CL.sync_raw_state view (CL.append_raw_sent_slice view.CL.raw_log bytes lo hi) view.CL.state))
{
  let raw = CL.append_raw_sent_slice view.CL.raw_log bytes lo hi;
  let next = CL.sync_raw_state view raw view.CL.state;
  CL.lemma_raw_io_log_extends_sent_slice view.CL.raw_log bytes lo hi;
  CL.lemma_raw_io_log_same_received_sent_slice view.CL.raw_log bytes lo hi;
  CL.lemma_connection_view_consistent_sync_raw_same_state view raw;
  CL.lemma_connection_view_step_raw_state view raw view.CL.state;
  ST.advance_log log next;
  assert (pure (CL.connection_view_consistent next));
  assert (pure (next.CL.state == view.CL.state));
  assert (pure (next.CL.app_view == view.CL.app_view));
  assert (pure (CL.raw_io_log_extends view.CL.raw_log next.CL.raw_log));
  assert (pure (CL.raw_io_log_same_received view.CL.raw_log next.CL.raw_log));
  assert (pure (CL.connection_view_single_step view next))
}

ghost
fn advance_log_raw_received_slice
  (log:ST.log_ref)
  (#view:CL.connection_view)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat)
  requires ST.log_current log view
  requires pure (CL.connection_view_consistent view /\
                 lo <= hi /\ hi <= B.length bytes)
  ensures ST.log_current log (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state) **
          pure (CL.connection_view_consistent (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state) /\
                (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.state == view.CL.state /\
                (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.app_view == view.CL.app_view /\
                CL.raw_io_log_extends view.CL.raw_log
                  (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.raw_log /\
                CL.raw_io_log_same_sent view.CL.raw_log
                  (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state).CL.raw_log /\
                CL.connection_view_single_step view (CL.sync_raw_state view (CL.append_raw_received_slice view.CL.raw_log bytes lo hi) view.CL.state))
{
  let raw = CL.append_raw_received_slice view.CL.raw_log bytes lo hi;
  let next = CL.sync_raw_state view raw view.CL.state;
  CL.lemma_raw_io_log_extends_received_slice view.CL.raw_log bytes lo hi;
  CL.lemma_raw_io_log_same_sent_received_slice view.CL.raw_log bytes lo hi;
  CL.lemma_connection_view_consistent_sync_raw_same_state view raw;
  CL.lemma_connection_view_step_raw_state view raw view.CL.state;
  ST.advance_log log next;
  assert (pure (CL.connection_view_consistent next));
  assert (pure (next.CL.state == view.CL.state));
  assert (pure (next.CL.app_view == view.CL.app_view));
  assert (pure (CL.raw_io_log_extends view.CL.raw_log next.CL.raw_log));
  assert (pure (CL.raw_io_log_same_sent view.CL.raw_log next.CL.raw_log));
  assert (pure (CL.connection_view_single_step view next))
}

ghost
fn advance_successful_handshake_log
  (log:ST.log_ref)
  (#view:CL.connection_view)
  (s:S.conn_state)
  requires ST.log_current log view
  requires pure (CL.connection_view_consistent view /\
                 view.CL.state == s /\
                 s.S.phase == S.Start)
  ensures ST.log_current log (successful_handshake_view view s) **
          pure (CL.connection_view_consistent (successful_handshake_view view s) /\
                (successful_handshake_view view s).CL.state == hs_application_data s /\
                (successful_handshake_view view s).CL.raw_log == view.CL.raw_log /\
                (successful_handshake_view view s).CL.app_view == view.CL.app_view /\
                CL.connection_view_single_step view (successful_handshake_view view s))
{
  advance_log_event
    log
    (sent_handshake_event (H.ClientHello dummy_client_hello))
    (S.SendClientHello dummy_client_hello)
    (hs_client_hello_sent s);
  advance_log_event
    log
    (received_handshake_event (H.ServerHello dummy_server_hello))
    (S.RecvServerHello dummy_server_hello)
    (hs_server_hello_received s);
  advance_log_event
    log
    (received_handshake_event (H.EncryptedExtensions dummy_encrypted_extensions))
    (S.RecvEncryptedExtensions dummy_encrypted_extensions)
    (hs_encrypted_extensions_received s);
  advance_log_event
    log
    (received_handshake_event (H.Certificate dummy_certificate))
    (S.RecvCertificate dummy_certificate)
    (hs_certificate_received s);
  advance_log_event
    log
    (CL.LocalEvent (CL.LocalValidateCertificate dummy_peer))
    (S.ValidateCertificate dummy_peer)
    (hs_certificate_validated s);
  advance_log_event
    log
    (received_handshake_event (H.CertificateVerify dummy_certificate_verify))
    (S.RecvCertificateVerify dummy_certificate_verify)
    (hs_certificate_verified s);
  advance_log_event
    log
    (received_handshake_event (H.Finished dummy_finished))
    (S.RecvServerFinished dummy_finished)
    (hs_server_finished_verified s);
  advance_log_event
    log
    (sent_handshake_event (H.Finished dummy_finished))
    (S.SendClientFinished dummy_finished)
    (hs_application_data s);
  assert (pure (CL.connection_view_consistent (successful_handshake_view view s)));
  assert (pure ((successful_handshake_view view s).CL.state == hs_application_data s));
  assert (pure ((successful_handshake_view view s).CL.raw_log == view.CL.raw_log));
  assert (pure ((successful_handshake_view view s).CL.app_view == view.CL.app_view));
  CL.lemma_connection_view_step_same_app view (successful_handshake_view view s);
  assert (pure (CL.connection_view_single_step view (successful_handshake_view view s)))
}

fn client_new
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (#trust_store: X.trust_store)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns c: connection
  ensures exists* st.
          pts_to hostname 'hostname_bytes **
          connection_exactly c st S.initial CL.empty_connection_view
{
  let backend = E.client_new hostname hostname_len #trust_store;
  let live = Box.alloc true;
  let app_keys_installed = Box.alloc false;
  let pending_read_offset = Box.alloc 0sz;
  let pending_read_len = Box.alloc 0sz;
  let client_application_key = V.alloc 0uy 32sz;
  let client_application_iv = V.alloc 0uy 12sz;
  let server_application_key = V.alloc 0uy 32sz;
  let server_application_iv = V.alloc 0uy 12sz;
  let pending_read_buffer = V.alloc 0uy pending_read_buffer_capacity;
  let client_application_record_state = Rec.record_state_new ();
  let server_application_record_state = Rec.record_state_new ();
  let st = ST.alloc_initial ();
  let log = ST.alloc_initial_log ();
  let c = {
    backend;
    live;
    client_application_key;
    client_application_iv;
    server_application_key;
    server_application_iv;
    client_application_record_state;
    server_application_record_state;
    application_keys_installed = app_keys_installed;
    pending_read_buffer;
    pending_read_offset;
    pending_read_len;
    log;
  };
  with backend_s. rewrite (E.is_connection backend) as (E.is_connection c.backend);
  with live_s. rewrite (Box.pts_to live live_s) as (Box.pts_to c.live live_s);
  with installed_s. rewrite (Box.pts_to app_keys_installed installed_s) as (Box.pts_to c.application_keys_installed installed_s);
  with pending_offset_s. rewrite (Box.pts_to pending_read_offset pending_offset_s) as (Box.pts_to c.pending_read_offset pending_offset_s);
  with pending_len_s. rewrite (Box.pts_to pending_read_len pending_len_s) as (Box.pts_to c.pending_read_len pending_len_s);
  with ck_s. rewrite (V.pts_to client_application_key ck_s) as (V.pts_to c.client_application_key ck_s);
  with ci_s. rewrite (V.pts_to client_application_iv ci_s) as (V.pts_to c.client_application_iv ci_s);
  with sk_s. rewrite (V.pts_to server_application_key sk_s) as (V.pts_to c.server_application_key sk_s);
  with si_s. rewrite (V.pts_to server_application_iv si_s) as (V.pts_to c.server_application_iv si_s);
  with pending_s. rewrite (V.pts_to pending_read_buffer pending_s) as (V.pts_to c.pending_read_buffer pending_s);
  with crs. rewrite (Rec.is_record_state client_application_record_state crs) as (Rec.is_record_state c.client_application_record_state crs);
  with srs. rewrite (Rec.is_record_state server_application_record_state srs) as (Rec.is_record_state c.server_application_record_state srs);
  rewrite (ST.log_current log CL.empty_connection_view) as (ST.log_current c.log CL.empty_connection_view);
  assert (pure (CL.connection_view_consistent CL.empty_connection_view));
  assert (pure (CL.empty_connection_view.CL.state == S.initial));
  fold (connection_exactly c st S.initial CL.empty_connection_view);
  c
}

fn client_free (c: connection)
  requires connection_exactly c 'st 's 'view
  ensures emp
{
  unfold (connection_exactly c 'st 's 'view);
  E.client_free c.backend;
  Box.free c.live;
  Box.free c.application_keys_installed;
  Box.free c.pending_read_offset;
  Box.free c.pending_read_len;
  V.free c.client_application_key;
  V.free c.client_application_iv;
  V.free c.server_application_key;
  V.free c.server_application_iv;
  V.free c.pending_read_buffer;
  Rec.record_state_free c.client_application_record_state;
  Rec.record_state_free c.server_application_record_state;
  drop_ (ST.current 'st 's);
  drop_ (ST.log_current c.log 'view);
}

fn client_connect (c: connection) (ch: IO.channel)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists server_name resp.
                   CL.step 'view0 (CL.request_no_network_in (CL.OpStart server_name)) view1 resp /\
                   (ok ==> resp.CL.status == CL.HandshakeComplete) /\
                   (not ok ==> resp.CL.status == CL.Failed T.IoError)) /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                        (not ok ==> s'.S.phase == S.Failed))
{
          unfold (connection_exactly c 'st 's 'view0);
          let mut client_key = [| 0uy; 32sz |];
          let mut client_iv = [| 0uy; 12sz |];
          let mut server_key = [| 0uy; 32sz |];
          let mut server_iv = [| 0uy; 12sz |];
          let handshake_ok = E.client_connect c.backend ch;
          if handshake_ok {
            let keys_ok = E.derive_application_keys c.backend client_key client_iv server_key server_iv;
            if keys_ok {
              pts_to_len client_key;
              pts_to_len client_iv;
              pts_to_len server_key;
              pts_to_len server_iv;
              V.pts_to_len c.client_application_key;
              V.pts_to_len c.client_application_iv;
              V.pts_to_len c.server_application_key;
              V.pts_to_len c.server_application_iv;
              V.to_array_pts_to c.client_application_key;
              V.to_array_pts_to c.client_application_iv;
              V.to_array_pts_to c.server_application_key;
              V.to_array_pts_to c.server_application_iv;
              Arr.memcpy 32sz client_key (V.vec_to_array c.client_application_key);
              Arr.memcpy 12sz client_iv (V.vec_to_array c.client_application_iv);
              Arr.memcpy 32sz server_key (V.vec_to_array c.server_application_key);
              Arr.memcpy 12sz server_iv (V.vec_to_array c.server_application_iv);
              Rec.install_application_keys_runtime
               c.client_application_record_state
               (V.vec_to_array c.client_application_key)
               (V.vec_to_array c.client_application_iv);
              Rec.install_application_keys_runtime
               c.server_application_record_state
               (V.vec_to_array c.server_application_key)
               (V.vec_to_array c.server_application_iv);
              V.to_vec_pts_to c.client_application_key;
              V.to_vec_pts_to c.client_application_iv;
              V.to_vec_pts_to c.server_application_key;
              V.to_vec_pts_to c.server_application_iv;
              c.application_keys_installed := true;
              advance_successful_handshake 'st;
              advance_successful_handshake_log c.log 's;
              lemma_successful_handshake_state_evolves 's;
              assert (pure ('view0.CL.state == 's));
              assert (pure ((successful_handshake_view 'view0 's).CL.raw_log == 'view0.CL.raw_log));
              assert (pure ((successful_handshake_view 'view0 's).CL.app_view == 'view0.CL.app_view));
              assert (pure ((successful_handshake_view 'view0 's).CL.state.S.phase == S.ApplicationData));
              assert (pure (S.conn_evolves 'view0.CL.state (successful_handshake_view 'view0 's).CL.state));
              CL.lemma_step_start_success_abstract
                'view0
                (successful_handshake_view 'view0 's)
                B.empty;
              let resp = CL.response_no_network_out B.empty CL.HandshakeComplete;
              assert (pure (CL.step 'view0
                (CL.request_no_network_in (CL.OpStart B.empty))
                (successful_handshake_view 'view0 's)
                resp));
              assert (pure (resp.CL.status == CL.HandshakeComplete));
              assert (pure (exists server_name step_resp.
                CL.step 'view0
                  (CL.request_no_network_in (CL.OpStart server_name))
                  (successful_handshake_view 'view0 's)
                  step_resp /\
                (true ==> step_resp.CL.status == CL.HandshakeComplete) /\
                (not true ==> step_resp.CL.status == CL.Failed T.IoError)));
              assert (pure (CL.connection_view_consistent (successful_handshake_view 'view0 's)));
              assert (pure ((successful_handshake_view 'view0 's).CL.state == hs_application_data 's));
              fold (connection_exactly c 'st (hs_application_data 's) (successful_handshake_view 'view0 's));
              true
            } else {
              ST.advance_fail 'st T.IoError;
              advance_log_event
                c.log
                (CL.local_fail_event T.IoError)
                (S.Fail T.IoError)
                (S.fail 's T.IoError);
              CL.lemma_step_start_failed
                'view0
                B.empty
                T.IoError
                (S.fail 's T.IoError);
              let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
              assert (pure (CL.step 'view0
                (CL.request_no_network_in (CL.OpStart B.empty))
                (note_local_fail_view 'view0 T.IoError 's)
                resp));
              assert (pure (resp.CL.status == CL.Failed T.IoError));
              assert (pure (exists server_name step_resp.
                CL.step 'view0
                  (CL.request_no_network_in (CL.OpStart server_name))
                  (note_local_fail_view 'view0 T.IoError 's)
                  step_resp /\
                (false ==> step_resp.CL.status == CL.HandshakeComplete) /\
                (not false ==> step_resp.CL.status == CL.Failed T.IoError)));
              assert (pure (CL.connection_view_consistent (note_local_fail_view 'view0 T.IoError 's)));
              assert (pure ((note_local_fail_view 'view0 T.IoError 's).CL.state == S.fail 's T.IoError));
              fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view 'view0 T.IoError 's));
              false
            }
          } else {
            ST.advance_fail 'st T.IoError;
            advance_log_event
              c.log
              (CL.local_fail_event T.IoError)
              (S.Fail T.IoError)
              (S.fail 's T.IoError);
            CL.lemma_step_start_failed
              'view0
              B.empty
              T.IoError
              (S.fail 's T.IoError);
            let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
            assert (pure (CL.step 'view0
              (CL.request_no_network_in (CL.OpStart B.empty))
              (note_local_fail_view 'view0 T.IoError 's)
              resp));
            assert (pure (resp.CL.status == CL.Failed T.IoError));
            assert (pure (exists server_name step_resp.
              CL.step 'view0
                (CL.request_no_network_in (CL.OpStart server_name))
                (note_local_fail_view 'view0 T.IoError 's)
                step_resp /\
              (false ==> step_resp.CL.status == CL.HandshakeComplete) /\
              (not false ==> step_resp.CL.status == CL.Failed T.IoError)));
            assert (pure (CL.connection_view_consistent (note_local_fail_view 'view0 T.IoError 's)));
            assert (pure ((note_local_fail_view 'view0 T.IoError 's).CL.state == S.fail 's T.IoError));
            fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view 'view0 T.IoError 's));
            false
          }
}

fn rec client_write_raw_exact
  (backend: E.connection)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  (log:ST.log_ref)
  requires   E.is_connection backend **
  IO.is_channel ch **
  pts_to buf 'bytes **
  ST.log_current log 'view **
  pure (B.length 'bytes == SZ.v total_len /\
        CL.connection_view_consistent 'view /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* view'.
          E.is_connection backend **
          IO.is_channel ch **
          pts_to buf 'bytes **
          ST.log_current log view' **
          pure (CL.connection_view_consistent view' /\
                view'.CL.state == 'view.CL.state /\
                view'.CL.app_view == 'view.CL.app_view /\
                CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log /\
                CL.raw_io_log_same_received 'view.CL.raw_log view'.CL.raw_log)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
    assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log 'view.CL.raw_log));
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.client_write_raw backend ch buf total_len offset remaining;
    if (n = 0sz) {
      CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
      assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log 'view.CL.raw_log));
      false
    } else {
      let offset' = SZ.(offset +^ n);
      let remaining' = SZ.(remaining -^ n);
      advance_log_raw_sent_slice log (Ghost.reveal 'bytes) (SZ.v offset) (SZ.v offset');
      with mid_view. assert (ST.log_current log mid_view);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      let ok = client_write_raw_exact backend ch buf total_len offset' remaining' log;
      with view'. _;
      CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log mid_view.CL.raw_log view'.CL.raw_log;
      CL.lemma_raw_io_log_same_received_trans 'view.CL.raw_log mid_view.CL.raw_log view'.CL.raw_log;
      assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
      assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log view'.CL.raw_log));
      ok
    }
  }
}

fn rec client_write_application_records
  (backend: E.connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  (log:ST.log_ref)
  requires   E.is_connection backend **
  Rec.is_record_state record_state 'record_s **
  IO.is_channel ch **
  pts_to buf 'bytes **
  ST.log_current log 'view **
  pure (B.length 'bytes == SZ.v total_len /\
        CL.connection_view_consistent 'view /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* record_s' view'.
          E.is_connection backend **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          pts_to buf 'bytes **
          ST.log_current log view' **
          pure (CL.connection_view_consistent view' /\
                view'.CL.state == 'view.CL.state /\
                view'.CL.app_view == 'view.CL.app_view /\
                CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log /\
                CL.raw_io_log_same_received 'view.CL.raw_log view'.CL.raw_log)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
    assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log 'view.CL.raw_log));
    true
  } else {
    let chunk_len =
      if SZ.(remaining <^ app_record_chunk_len) {
        remaining
      } else {
        app_record_chunk_len
      };
    assert (pure (SZ.v chunk_len > 0));
    assert (pure (SZ.v chunk_len <= 4096));
    assert (pure (SZ.v offset + SZ.v chunk_len <= SZ.v total_len));
    let inner_len = SZ.(chunk_len +^ 1sz);
    let cipher_len = SZ.(inner_len +^ 16sz);
    let mut header = [| 0uy; 5sz |];
    let mut inner_plaintext = [| 0uy; inner_len |];
    let mut cipher = [| 0uy; cipher_len |];
    assert (pure (SZ.v cipher_len <= 4113));
    RF.serialize_application_data_header
      (Cast.uint32_to_uint16 (SZ.sizet_to_uint32 cipher_len))
      header
      5sz;
    RF.encode_inner_plaintext_no_padding_slice
      buf
      total_len
      offset
      chunk_len
      23uy
      inner_plaintext
      inner_len;
    with inner_bytes. assert (pts_to inner_plaintext inner_bytes);
    assert (pure (B.length inner_bytes == SZ.v inner_len));
    let sealed = Rec.seal_application_runtime
      record_state
      header
      5sz
      inner_plaintext
      inner_len
      cipher;
    with header_bytes. assert (pts_to header header_bytes);
    with cipher_bytes. assert (pts_to cipher cipher_bytes);
    assert (pure (B.length header_bytes == 5));
    assert (pure (B.length cipher_bytes == SZ.v cipher_len));
    if sealed {
      let header_ok = client_write_raw_exact backend ch header 5sz 0sz 5sz log;
      with header_view. _;
      if header_ok {
        let cipher_ok = client_write_raw_exact backend ch cipher cipher_len 0sz cipher_len log;
        with cipher_view. _;
        CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
        CL.lemma_raw_io_log_same_received_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
        if cipher_ok {
          let offset' = SZ.(offset +^ chunk_len);
          let remaining' = SZ.(remaining -^ chunk_len);
          assert (pure (SZ.v remaining' < SZ.v remaining));
          assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
          let ok = client_write_application_records backend ch record_state buf total_len offset' remaining' log;
          with record_s' view'. _;
          CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
          CL.lemma_raw_io_log_same_received_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
          assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
          assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log view'.CL.raw_log));
          ok
        } else {
          assert (pure (CL.raw_io_log_extends 'view.CL.raw_log cipher_view.CL.raw_log));
          assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log cipher_view.CL.raw_log));
          false
        }
      } else {
        false
      }
    } else {
      CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
      assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log 'view.CL.raw_log));
      false
    }
  }
}

inline_for_extraction
fn client_send_close_notify_record
  (backend: E.connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (log:ST.log_ref)
  requires   E.is_connection backend **
  Rec.is_record_state record_state 'record_s **
  IO.is_channel ch **
  ST.log_current log 'view **
  pure (CL.connection_view_consistent 'view)
  returns ok: bool
  ensures exists* record_s' view'.
          E.is_connection backend **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          ST.log_current log view' **
          pure (CL.connection_view_consistent view' /\
                view'.CL.state == 'view.CL.state /\
                view'.CL.app_view == 'view.CL.app_view /\
                CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log /\
                CL.raw_io_log_same_received 'view.CL.raw_log view'.CL.raw_log)
{
  let mut header = [| 0uy; 5sz |];
  let mut inner_plaintext = [| 0uy; 3sz |];
  let mut cipher = [| 0uy; 19sz |];
  RF.serialize_application_data_header
    (Cast.uint32_to_uint16 (SZ.sizet_to_uint32 19sz))
    header
    5sz;
  inner_plaintext.(0sz) <- 1uy;
  inner_plaintext.(1sz) <- 0uy;
  inner_plaintext.(2sz) <- 21uy;
  let sealed = Rec.seal_application_runtime
    record_state
    header
    5sz
    inner_plaintext
    3sz
    cipher;
  with header_bytes. assert (pts_to header header_bytes);
  with cipher_bytes. assert (pts_to cipher cipher_bytes);
  assert (pure (B.length header_bytes == 5));
  assert (pure (B.length cipher_bytes == 19));
  if sealed {
    let header_ok = client_write_raw_exact backend ch header 5sz 0sz 5sz log;
    with header_view. _;
    if header_ok {
      let cipher_ok = client_write_raw_exact backend ch cipher 19sz 0sz 19sz log;
      with cipher_view. _;
      CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
      CL.lemma_raw_io_log_same_received_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
      cipher_ok
    } else {
      false
    }
  } else {
    CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
    assert (pure (CL.raw_io_log_same_received 'view.CL.raw_log 'view.CL.raw_log));
    false
  }
}

fn client_write_all (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns ok: bool
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in (CL.OpSendApplicationData 'bytes)) view1 resp) /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (connection_exactly c 'st 's 'view0);
  let keys_installed = !c.application_keys_installed;
  if keys_installed {
    assert (pure (B.length 'bytes == SZ.v len));
    assert (pure (0 + SZ.v len == SZ.v len));
    let ok =
      client_write_application_records
        c.backend
        ch
        c.client_application_record_state
        buf
        len
        0sz
        len
        c.log;
    with record_s' raw_view. _;
    if ok {
      let send_state : erased S.conn_state =
        S.advance_write_records 's (S.application_data_record_count (Ghost.reveal 'bytes));
      ST.advance 'st (S.SendApplicationData (Ghost.reveal 'bytes)) (Ghost.reveal send_state);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (CL.sent_app_event (Ghost.reveal 'bytes))
        (S.SendApplicationData (Ghost.reveal 'bytes))
        (Ghost.reveal send_state);
      assert (pure (CL.connection_view_consistent (note_sent_app_view raw_view (Ghost.reveal 'bytes) 's)));
      assert (pure ((note_sent_app_view raw_view (Ghost.reveal 'bytes) 's).CL.state == Ghost.reveal send_state));
      CL.lemma_app_log_extends_sent raw_view.CL.app_view (Ghost.reveal 'bytes);
      assert (pure (CL.connection_view_single_step 'view0 (note_sent_app_view raw_view (Ghost.reveal 'bytes) 's)));
      CL.lemma_step_send_application_data_success
        'view0
        raw_view
        (Ghost.reveal 'bytes)
        (Ghost.reveal send_state);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_no_network_in (CL.OpSendApplicationData (Ghost.reveal 'bytes)))
        (note_sent_app_view raw_view (Ghost.reveal 'bytes) 's)
        resp));
      fold (connection_exactly c 'st (Ghost.reveal send_state) (note_sent_app_view raw_view (Ghost.reveal 'bytes) 's));
      true
    } else {
      ST.advance_fail 'st T.IoError;
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (CL.local_fail_event T.IoError)
        (S.Fail T.IoError)
        (S.fail 's T.IoError);
      assert (pure (CL.connection_view_consistent (note_local_fail_view raw_view T.IoError 's)));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.state == S.fail 's T.IoError));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_local_fail_view raw_view T.IoError 's)));
      CL.lemma_step_send_application_data_failed
        'view0
        raw_view
        (Ghost.reveal 'bytes)
        T.IoError
        (S.fail 's T.IoError);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_no_network_in (CL.OpSendApplicationData (Ghost.reveal 'bytes)))
        (note_local_fail_view raw_view T.IoError 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view raw_view T.IoError 's));
      false
    }
  } else {
    ST.advance_fail 'st T.IoError;
    advance_log_event
      c.log
      (CL.local_fail_event T.IoError)
      (S.Fail T.IoError)
      (S.fail 's T.IoError);
    assert (pure (CL.connection_view_consistent (note_local_fail_view 'view0 T.IoError 's)));
    assert (pure ((note_local_fail_view 'view0 T.IoError 's).CL.state == S.fail 's T.IoError));
    CL.lemma_raw_io_log_extends_refl 'view0.CL.raw_log;
    assert (pure (CL.raw_io_log_same_received 'view0.CL.raw_log 'view0.CL.raw_log));
    CL.lemma_step_send_application_data_failed
      'view0
      'view0
      (Ghost.reveal 'bytes)
      T.IoError
      (S.fail 's T.IoError);
    assert (pure (exists resp. CL.step 'view0
      (CL.request_no_network_in (CL.OpSendApplicationData (Ghost.reveal 'bytes)))
      (note_local_fail_view 'view0 T.IoError 's)
      resp));
    fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view 'view0 T.IoError 's));
    false
  }
}

fn client_write (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns written: SZ.t
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in (CL.OpSendApplicationData 'bytes)) view1 resp) /\
                SZ.v written <= SZ.v len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Failed))
{
  let ok = client_write_all c ch buf len;
  if ok {
    len
  } else {
    0sz
  }
}

fn rec copy_payload_to_output_loop
  (payload: array U8.t)
  (payload_total_len: SZ.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (src_index: SZ.t)
  (dst_index: SZ.t)
  (remaining: SZ.t)
  requires pts_to payload 'payload_bytes **
           pts_to out 'old **
           pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                 B.length 'old == SZ.v total_len /\
                 SZ.v src_index + SZ.v remaining <= SZ.v payload_total_len /\
                 SZ.v dst_index + SZ.v remaining <= SZ.v total_len)
  ensures exists* bytes.
          pts_to payload 'payload_bytes **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length bytes == SZ.v total_len));
  } else {
    assert (pure (SZ.v src_index < SZ.v payload_total_len));
    assert (pure (SZ.v dst_index < SZ.v total_len));
    let b = payload.(src_index);
    out.(dst_index) <- b;
    let src_index' = SZ.(src_index +^ 1sz);
    let dst_index' = SZ.(dst_index +^ 1sz);
    let remaining' = SZ.(remaining -^ 1sz);
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length bytes == SZ.v total_len));
    assert (pure (SZ.v remaining' < SZ.v remaining));
    assert (pure (SZ.v src_index' + SZ.v remaining' <= SZ.v payload_total_len));
    assert (pure (SZ.v dst_index' + SZ.v remaining' <= SZ.v total_len));
    copy_payload_to_output_loop payload payload_total_len out total_len src_index' dst_index' remaining'
  }
}

fn copy_payload_to_output
  (payload: array U8.t)
  (payload_total_len: SZ.t)
  (copy_len: SZ.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  requires pts_to payload 'payload_bytes **
           pts_to out 'old **
           pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                 B.length 'old == SZ.v total_len /\
                 SZ.v copy_len <= SZ.v payload_total_len /\
                 SZ.v offset + SZ.v copy_len <= SZ.v total_len)
  ensures exists* bytes.
          pts_to payload 'payload_bytes **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len)
{
  copy_payload_to_output_loop payload payload_total_len out total_len 0sz offset copy_len
}

fn rec client_read_raw_exact
  (backend: E.connection)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  (log:ST.log_ref)
  requires   E.is_connection backend **
  IO.is_channel ch **
  pts_to buf 'old **
  ST.log_current log 'view **
  pure (B.length 'old == SZ.v total_len /\
        CL.connection_view_consistent 'view /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* bytes view'.
          E.is_connection backend **
          IO.is_channel ch **
          pts_to buf bytes **
          ST.log_current log view' **
          pure (B.length bytes == SZ.v total_len /\
                CL.connection_view_consistent view' /\
                view'.CL.state == 'view.CL.state /\
                view'.CL.app_view == 'view.CL.app_view /\
                CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log /\
                CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
    assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log 'view.CL.raw_log));
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.client_read_raw backend ch buf total_len offset remaining;
    if (n = 0sz) {
      CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
      assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log 'view.CL.raw_log));
      false
    } else {
      with bytes. assert (pts_to buf bytes);
      let offset' = SZ.(offset +^ n);
      let remaining' = SZ.(remaining -^ n);
      advance_log_raw_received_slice log bytes (SZ.v offset) (SZ.v offset');
      with mid_view. assert (ST.log_current log mid_view);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      let ok = client_read_raw_exact backend ch buf total_len offset' remaining' log;
      with bytes' view'. _;
      CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log mid_view.CL.raw_log view'.CL.raw_log;
      CL.lemma_raw_io_log_same_sent_trans 'view.CL.raw_log mid_view.CL.raw_log view'.CL.raw_log;
      assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
      assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log));
      ok
    }
  }
}

fn rec client_read_application_records
  (backend: E.connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (read_buffer: V.vec U8.t)
  (pending_read_offset_box: box SZ.t)
  (pending_read_len_box: box SZ.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  (fuel: U8.t)
  (log:ST.log_ref)
  requires   E.is_connection backend **
  Rec.is_record_state record_state 'record_s **
  IO.is_channel ch **
  V.pts_to read_buffer 'read_buffer_bytes **
  Box.pts_to pending_read_offset_box 'pending_read_offset **
  Box.pts_to pending_read_len_box 'pending_read_len **
  pts_to out 'old **
  ST.log_current log 'view **
  pure (V.is_full_vec read_buffer /\
        V.length read_buffer == 4096 /\
        SZ.v 'pending_read_offset <= SZ.v 'pending_read_len /\
        SZ.v 'pending_read_len <= 4096 /\
        B.length 'old == SZ.v total_len /\
        CL.connection_view_consistent 'view /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns status: U8.t
  ensures exists* record_s' read_buffer_bytes pending_read_offset pending_read_len bytes view'.
          E.is_connection backend **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          V.pts_to read_buffer read_buffer_bytes **
          Box.pts_to pending_read_offset_box pending_read_offset **
          Box.pts_to pending_read_len_box pending_read_len **
          pts_to out bytes **
          ST.log_current log view' **
          pure (V.is_full_vec read_buffer /\
                V.length read_buffer == 4096 /\
                SZ.v pending_read_offset <= SZ.v pending_read_len /\
                SZ.v pending_read_len <= 4096 /\
                B.length bytes == SZ.v total_len /\
                CL.connection_view_consistent view' /\
                view'.CL.state == 'view.CL.state /\
                view'.CL.app_view == 'view.CL.app_view /\
                CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log /\
                CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log)
  decreases (U8.v fuel, SZ.v remaining)
{
  if (remaining = 0sz) {
    CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
    assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log 'view.CL.raw_log));
    read_status_complete
  } else {
    assert (pure (SZ.v remaining > 0));
    let pending_read_offset = !pending_read_offset_box;
    let pending_read_len = !pending_read_len_box;
    assert (pure (SZ.v pending_read_offset <= SZ.v pending_read_len));
    assert (pure (SZ.v pending_read_len <= 4096));
    if SZ.(pending_read_offset <^ pending_read_len) {
      let pending_available_refined = SZ.(pending_read_len -^ pending_read_offset);
      let pending_available : SZ.t = pending_available_refined;
      assert (pure (SZ.v pending_available > 0));
      let copy_len : SZ.t =
        if SZ.(remaining <^ pending_available) {
          remaining
        } else {
          pending_available
        };
      assert (pure (SZ.v copy_len > 0));
      assert (pure (SZ.v copy_len <= SZ.v remaining));
      assert (pure (SZ.v pending_read_offset + SZ.v copy_len <= SZ.v pending_read_len));
      assert (pure (SZ.v pending_read_offset + SZ.v copy_len <= SZ.v pending_read_buffer_capacity));
      assert (pure (SZ.v offset + SZ.v copy_len <= SZ.v total_len));
      V.pts_to_len read_buffer;
      V.to_array_pts_to read_buffer;
      copy_payload_to_output_loop
        (V.vec_to_array read_buffer)
        pending_read_buffer_capacity
        out
        total_len
        pending_read_offset
        offset
        copy_len;
      V.to_vec_pts_to read_buffer;
      let pending_read_offset' = SZ.(pending_read_offset +^ copy_len);
      assert (pure (SZ.v pending_read_offset' <= SZ.v pending_read_len));
      pending_read_offset_box := pending_read_offset';
      with bytes. assert (pts_to out bytes);
      if (copy_len = remaining) {
        CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
        assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log 'view.CL.raw_log));
        read_status_complete
      } else {
        let offset' = SZ.(offset +^ copy_len);
        let remaining' = SZ.(remaining -^ copy_len);
        assert (pure (SZ.v remaining' < SZ.v remaining));
        assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
        let status = client_read_application_records
          backend
          ch
          record_state
          read_buffer
          pending_read_offset_box
          pending_read_len_box
          out
          total_len
          offset'
          remaining'
          fuel
          log;
        with record_s' read_buffer_bytes pending_read_offset pending_read_len bytes' view'. _;
        assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
        assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log));
        status
      }
    } else if (fuel = 0uy) {
      CL.lemma_raw_io_log_extends_refl 'view.CL.raw_log;
      assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log 'view.CL.raw_log));
      read_status_failed
    } else {
      let mut header = [| 0uy; 5sz |];
      let header_ok = client_read_raw_exact backend ch header 5sz 0sz 5sz log;
      with header_bytes header_view. _;
      with bytes. assert (pts_to out bytes);
      let fuel' = U8.(fuel -^ 1uy);
      if header_ok {
        let mut content_type_out = [| 0uy; 1sz |];
        let mut fragment_len_out = [| 0uy; 2sz |];
        let header_parse_ok =
          RF.parse_record_header header 5sz content_type_out 1sz fragment_len_out 2sz;
        if header_parse_ok {
          let content_type = content_type_out.(0sz);
          let frag_hi = fragment_len_out.(0sz);
          let frag_lo = fragment_len_out.(1sz);
          let frag_hi16 = Cast.uint8_to_uint16 frag_hi;
          let frag_lo16 = Cast.uint8_to_uint16 frag_lo;
          let frag16 = U16.logor (U16.shift_left frag_hi16 8ul) frag_lo16;
          let fragment_len = SZ.uint16_to_sizet frag16;
          if not (content_type = 23uy) {
            read_status_failed
          } else if SZ.(16sz <^ fragment_len) {
            let mut cipher = [| 0uy; fragment_len |];
            let fragment_ok = client_read_raw_exact backend ch cipher fragment_len 0sz fragment_len log;
            with cipher_bytes cipher_view. _;
            CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
            CL.lemma_raw_io_log_same_sent_trans 'view.CL.raw_log header_view.CL.raw_log cipher_view.CL.raw_log;
            if fragment_ok {
              let inner_len = SZ.(fragment_len -^ 16sz);
              assert (pure (SZ.v inner_len > 0));
              let mut inner = [| 0uy; inner_len |];
              let opened =
                Rec.open_application_runtime record_state header 5sz cipher fragment_len inner;
              with opened_bytes. assert (pts_to out opened_bytes);
              if opened {
                let mut inner_content_type_out = [| 0uy; 1sz |];
                let response_len =
                  RF.decode_inner_plaintext inner inner_len inner_content_type_out 1sz;
                let inner_content_type = inner_content_type_out.(0sz);
                if (inner_content_type = 22uy) {
                  assert (pure (U8.v fuel' < U8.v fuel));
                  let status = client_read_application_records
                    backend
                    ch
                    record_state
                    read_buffer
                    pending_read_offset_box
                    pending_read_len_box
                    out
                    total_len
                    offset
                    remaining
                    fuel'
                    log;
                  with record_s' read_buffer_bytes pending_read_offset pending_read_len bytes' view'. _;
                  CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
                  CL.lemma_raw_io_log_same_sent_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
                  assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
                  assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log));
                  status
                } else if (inner_content_type = 21uy) {
                  if SZ.(1sz <^ inner_len) {
                    pts_to_len inner;
                    let alert_level = inner.(0sz);
                    let alert_description = inner.(1sz);
                    if ((alert_level = 1uy || alert_level = 2uy) &&
                        alert_description = 0uy) {
                      read_status_close_notify
                    } else if (alert_level = 1uy || alert_level = 2uy) {
                      if (alert_description = 10uy) {
                        read_status_alert_unexpected_message
                      } else if (alert_description = 20uy) {
                        read_status_alert_bad_record_mac
                      } else if (alert_description = 40uy) {
                        read_status_alert_handshake_failure
                      } else if (alert_description = 51uy) {
                        read_status_alert_decrypt_error
                      } else if (alert_description = 70uy) {
                        read_status_alert_protocol_version
                      } else if (alert_description = 110uy) {
                        read_status_alert_unsupported_extension
                      } else if (alert_description = 46uy) {
                        read_status_alert_certificate_unknown
                      } else if (alert_description = 47uy) {
                        read_status_alert_illegal_parameter
                      } else {
                        read_status_alert_decode_error
                      }
                    } else {
                      read_status_failed
                    }
                  } else {
                    read_status_failed
                  }
                } else if (not (inner_content_type = 23uy)) {
                  read_status_failed
                } else if SZ.(remaining <^ response_len) {
                  if SZ.(response_len <=^ pending_read_buffer_capacity) {
                    copy_payload_to_output inner inner_len remaining out total_len offset;
                    with copied_bytes. assert (pts_to out copied_bytes);
                    let leftover_len = SZ.(response_len -^ remaining);
                    assert (pure (SZ.v leftover_len == SZ.v response_len - SZ.v remaining));
                    assert (pure (SZ.v leftover_len > 0));
                    assert (pure (SZ.v leftover_len <= SZ.v pending_read_buffer_capacity));
                    lemma_nat_add_sub_cancel
                      0
                      (SZ.v remaining)
                      (SZ.v response_len);
                    assert (pure (0 + SZ.v remaining + (SZ.v response_len - SZ.v remaining) ==
                                  0 + SZ.v response_len));
                    assert (pure (SZ.v remaining + SZ.v leftover_len == SZ.v response_len));
                    assert (pure (SZ.v remaining + SZ.v leftover_len <= SZ.v inner_len));
                    pts_to_len inner;
                    with inner_bytes. assert (pts_to inner inner_bytes);
                    assert (pure (B.length inner_bytes == SZ.v inner_len));
                    assert (pure (0 + SZ.v leftover_len <= SZ.v pending_read_buffer_capacity));
                    V.pts_to_len read_buffer;
                    V.to_array_pts_to read_buffer;
                    copy_payload_to_output_loop
                      inner
                      inner_len
                      (V.vec_to_array read_buffer)
                      pending_read_buffer_capacity
                      remaining
                      0sz
                      leftover_len;
                    V.to_vec_pts_to read_buffer;
                    pending_read_offset_box := 0sz;
                    pending_read_len_box := leftover_len;
                    read_status_complete
                  } else {
                    read_status_failed
                  }
                } else {
                  assert (pure (SZ.v response_len <= SZ.v remaining));
                  copy_payload_to_output inner inner_len response_len out total_len offset;
                  with copied_bytes. assert (pts_to out copied_bytes);
                  let offset' = SZ.(offset +^ response_len);
                  let remaining' = SZ.(remaining -^ response_len);
                  assert (pure (U8.v fuel' < U8.v fuel));
                  assert (pure (SZ.v offset' == SZ.v offset + SZ.v response_len));
                  assert (pure (SZ.v remaining' == SZ.v remaining - SZ.v response_len));
                  assert (pure (SZ.v offset + SZ.v remaining == SZ.v total_len));
                  lemma_nat_add_sub_cancel
                    (SZ.v offset)
                    (SZ.v response_len)
                    (SZ.v remaining);
                  assert (pure (SZ.v offset + SZ.v response_len +
                                (SZ.v remaining - SZ.v response_len) ==
                                SZ.v total_len));
                  assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
                  let status = client_read_application_records
                    backend
                    ch
                    record_state
                    read_buffer
                    pending_read_offset_box
                    pending_read_len_box
                    out
                    total_len
                    offset'
                    remaining'
                    fuel'
                    log;
                  with record_s' read_buffer_bytes pending_read_offset pending_read_len bytes' view'. _;
                  CL.lemma_raw_io_log_extends_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
                  CL.lemma_raw_io_log_same_sent_trans 'view.CL.raw_log cipher_view.CL.raw_log view'.CL.raw_log;
                  assert (pure (CL.raw_io_log_extends 'view.CL.raw_log view'.CL.raw_log));
                  assert (pure (CL.raw_io_log_same_sent 'view.CL.raw_log view'.CL.raw_log));
                  status
                }
              } else {
                read_status_failed
              }
            } else {
              read_status_failed
            }
          } else {
            read_status_failed
          }
        } else {
          read_status_failed
        }
      } else {
        read_status_failed
      }
    }
  }
}

fn client_read_exact (c: connection) (ch: IO.channel) (out: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to out 'old **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v len)
  returns ok: bool
  ensures exists* s' view1 bytes. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to out bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0
                  (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log view1.CL.raw_log)
                  view1 resp) /\
                B.length bytes == SZ.v len /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))
{
  unfold (connection_exactly c 'st 's 'view0);
  let keys_installed = !c.application_keys_installed;
  if keys_installed {
    assert (pure (B.length 'old == SZ.v len));
    assert (pure (0 + SZ.v len == SZ.v len));
    let status =
      client_read_application_records
        c.backend
        ch
        c.server_application_record_state
        c.pending_read_buffer
        c.pending_read_offset
        c.pending_read_len
        out
        len
        0sz
        len
        max_application_read_records
        c.log;
    with record_s' read_buffer_bytes pending_read_offset pending_read_len bytes_after_read raw_view. _;
    if (status = read_status_complete) {
      ST.advance 'st (S.RecvApplicationData bytes_after_read) (S.advance_read_record 's);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (CL.received_app_event bytes_after_read)
        (S.RecvApplicationData bytes_after_read)
        (S.advance_read_record 's);
      assert (pure (CL.connection_view_consistent (note_recv_app_view raw_view bytes_after_read 's)));
      assert (pure ((note_recv_app_view raw_view bytes_after_read 's).CL.state == S.advance_read_record 's));
      CL.lemma_app_log_extends_received raw_view.CL.app_view bytes_after_read;
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_app_view raw_view bytes_after_read 's)));
      CL.lemma_step_read_application_data_success
        'view0
        raw_view
        (SZ.v len)
        bytes_after_read
        (S.advance_read_record 's);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_app_view raw_view bytes_after_read 's).CL.raw_log)
        (note_recv_app_view raw_view bytes_after_read 's)
        resp));
      fold (connection_exactly c 'st (S.advance_read_record 's) (note_recv_app_view raw_view bytes_after_read 's));
      true
    } else if (status = read_status_close_notify) {
      ST.advance 'st S.RecvCloseNotify (S.recv_close_state 's);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        CL.received_close_notify_event
        S.RecvCloseNotify
        (S.recv_close_state 's);
      assert (pure (CL.connection_view_consistent (note_recv_close_view raw_view 's)));
      assert (pure ((note_recv_close_view raw_view 's).CL.state == S.recv_close_state 's));
      assert (pure ((note_recv_close_view raw_view 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_close_view raw_view 's)));
      CL.lemma_step_read_close_notify
        'view0
        raw_view
        (SZ.v len)
        (S.recv_close_state 's);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_close_view raw_view 's).CL.raw_log)
        (note_recv_close_view raw_view 's)
        resp));
      fold (connection_exactly c 'st (S.recv_close_state 's) (note_recv_close_view raw_view 's));
      false
    } else if (status = read_status_alert_unexpected_message) {
      ST.advance_fail 'st (T.AlertError T.UnexpectedMessage);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.UnexpectedMessage)
        (S.Fail (T.AlertError T.UnexpectedMessage))
        (S.fail 's (T.AlertError T.UnexpectedMessage));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.UnexpectedMessage 's)));
      assert (pure ((note_recv_alert_view raw_view T.UnexpectedMessage 's).CL.state == S.fail 's (T.AlertError T.UnexpectedMessage)));
      assert (pure ((note_recv_alert_view raw_view T.UnexpectedMessage 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.UnexpectedMessage 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.UnexpectedMessage
        (S.fail 's (T.AlertError T.UnexpectedMessage));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.UnexpectedMessage 's).CL.raw_log)
        (note_recv_alert_view raw_view T.UnexpectedMessage 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.UnexpectedMessage)) (note_recv_alert_view raw_view T.UnexpectedMessage 's));
      false
    } else if (status = read_status_alert_bad_record_mac) {
      ST.advance_fail 'st (T.AlertError T.BadRecordMac);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.BadRecordMac)
        (S.Fail (T.AlertError T.BadRecordMac))
        (S.fail 's (T.AlertError T.BadRecordMac));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.BadRecordMac 's)));
      assert (pure ((note_recv_alert_view raw_view T.BadRecordMac 's).CL.state == S.fail 's (T.AlertError T.BadRecordMac)));
      assert (pure ((note_recv_alert_view raw_view T.BadRecordMac 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.BadRecordMac 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.BadRecordMac
        (S.fail 's (T.AlertError T.BadRecordMac));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.BadRecordMac 's).CL.raw_log)
        (note_recv_alert_view raw_view T.BadRecordMac 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.BadRecordMac)) (note_recv_alert_view raw_view T.BadRecordMac 's));
      false
    } else if (status = read_status_alert_handshake_failure) {
      ST.advance_fail 'st (T.AlertError T.HandshakeFailure);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.HandshakeFailure)
        (S.Fail (T.AlertError T.HandshakeFailure))
        (S.fail 's (T.AlertError T.HandshakeFailure));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.HandshakeFailure 's)));
      assert (pure ((note_recv_alert_view raw_view T.HandshakeFailure 's).CL.state == S.fail 's (T.AlertError T.HandshakeFailure)));
      assert (pure ((note_recv_alert_view raw_view T.HandshakeFailure 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.HandshakeFailure 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.HandshakeFailure
        (S.fail 's (T.AlertError T.HandshakeFailure));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.HandshakeFailure 's).CL.raw_log)
        (note_recv_alert_view raw_view T.HandshakeFailure 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.HandshakeFailure)) (note_recv_alert_view raw_view T.HandshakeFailure 's));
      false
    } else if (status = read_status_alert_decrypt_error) {
      ST.advance_fail 'st (T.AlertError T.DecryptError);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.DecryptError)
        (S.Fail (T.AlertError T.DecryptError))
        (S.fail 's (T.AlertError T.DecryptError));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.DecryptError 's)));
      assert (pure ((note_recv_alert_view raw_view T.DecryptError 's).CL.state == S.fail 's (T.AlertError T.DecryptError)));
      assert (pure ((note_recv_alert_view raw_view T.DecryptError 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.DecryptError 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.DecryptError
        (S.fail 's (T.AlertError T.DecryptError));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.DecryptError 's).CL.raw_log)
        (note_recv_alert_view raw_view T.DecryptError 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.DecryptError)) (note_recv_alert_view raw_view T.DecryptError 's));
      false
    } else if (status = read_status_alert_protocol_version) {
      ST.advance_fail 'st (T.AlertError T.ProtocolVersion);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.ProtocolVersion)
        (S.Fail (T.AlertError T.ProtocolVersion))
        (S.fail 's (T.AlertError T.ProtocolVersion));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.ProtocolVersion 's)));
      assert (pure ((note_recv_alert_view raw_view T.ProtocolVersion 's).CL.state == S.fail 's (T.AlertError T.ProtocolVersion)));
      assert (pure ((note_recv_alert_view raw_view T.ProtocolVersion 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.ProtocolVersion 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.ProtocolVersion
        (S.fail 's (T.AlertError T.ProtocolVersion));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.ProtocolVersion 's).CL.raw_log)
        (note_recv_alert_view raw_view T.ProtocolVersion 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.ProtocolVersion)) (note_recv_alert_view raw_view T.ProtocolVersion 's));
      false
    } else if (status = read_status_alert_unsupported_extension) {
      ST.advance_fail 'st (T.AlertError T.UnsupportedExtension);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.UnsupportedExtension)
        (S.Fail (T.AlertError T.UnsupportedExtension))
        (S.fail 's (T.AlertError T.UnsupportedExtension));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.UnsupportedExtension 's)));
      assert (pure ((note_recv_alert_view raw_view T.UnsupportedExtension 's).CL.state == S.fail 's (T.AlertError T.UnsupportedExtension)));
      assert (pure ((note_recv_alert_view raw_view T.UnsupportedExtension 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.UnsupportedExtension 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.UnsupportedExtension
        (S.fail 's (T.AlertError T.UnsupportedExtension));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.UnsupportedExtension 's).CL.raw_log)
        (note_recv_alert_view raw_view T.UnsupportedExtension 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.UnsupportedExtension)) (note_recv_alert_view raw_view T.UnsupportedExtension 's));
      false
    } else if (status = read_status_alert_certificate_unknown) {
      ST.advance_fail 'st (T.AlertError T.CertificateUnknown);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.CertificateUnknown)
        (S.Fail (T.AlertError T.CertificateUnknown))
        (S.fail 's (T.AlertError T.CertificateUnknown));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.CertificateUnknown 's)));
      assert (pure ((note_recv_alert_view raw_view T.CertificateUnknown 's).CL.state == S.fail 's (T.AlertError T.CertificateUnknown)));
      assert (pure ((note_recv_alert_view raw_view T.CertificateUnknown 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.CertificateUnknown 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.CertificateUnknown
        (S.fail 's (T.AlertError T.CertificateUnknown));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.CertificateUnknown 's).CL.raw_log)
        (note_recv_alert_view raw_view T.CertificateUnknown 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.CertificateUnknown)) (note_recv_alert_view raw_view T.CertificateUnknown 's));
      false
    } else if (status = read_status_alert_illegal_parameter) {
      ST.advance_fail 'st (T.AlertError T.IllegalParameter);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.IllegalParameter)
        (S.Fail (T.AlertError T.IllegalParameter))
        (S.fail 's (T.AlertError T.IllegalParameter));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.IllegalParameter 's)));
      assert (pure ((note_recv_alert_view raw_view T.IllegalParameter 's).CL.state == S.fail 's (T.AlertError T.IllegalParameter)));
      assert (pure ((note_recv_alert_view raw_view T.IllegalParameter 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.IllegalParameter 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.IllegalParameter
        (S.fail 's (T.AlertError T.IllegalParameter));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.IllegalParameter 's).CL.raw_log)
        (note_recv_alert_view raw_view T.IllegalParameter 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.IllegalParameter)) (note_recv_alert_view raw_view T.IllegalParameter 's));
      false
    } else if (status = read_status_alert_decode_error) {
      ST.advance_fail 'st (T.AlertError T.DecodeError);
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (received_alert_event T.DecodeError)
        (S.Fail (T.AlertError T.DecodeError))
        (S.fail 's (T.AlertError T.DecodeError));
      assert (pure (CL.connection_view_consistent (note_recv_alert_view raw_view T.DecodeError 's)));
      assert (pure ((note_recv_alert_view raw_view T.DecodeError 's).CL.state == S.fail 's (T.AlertError T.DecodeError)));
      assert (pure ((note_recv_alert_view raw_view T.DecodeError 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_recv_alert_view raw_view T.DecodeError 's)));
      CL.lemma_step_read_alert_failed
        'view0
        raw_view
        (SZ.v len)
        T.DecodeError
        (S.fail 's (T.AlertError T.DecodeError));
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_recv_alert_view raw_view T.DecodeError 's).CL.raw_log)
        (note_recv_alert_view raw_view T.DecodeError 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's (T.AlertError T.DecodeError)) (note_recv_alert_view raw_view T.DecodeError 's));
      false
    } else {
      ST.advance_fail 'st T.IoError;
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (CL.local_fail_event T.IoError)
        (S.Fail T.IoError)
        (S.fail 's T.IoError);
      assert (pure (CL.connection_view_consistent (note_local_fail_view raw_view T.IoError 's)));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.state == S.fail 's T.IoError));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_local_fail_view raw_view T.IoError 's)));
      CL.lemma_step_read_failed
        'view0
        raw_view
        (SZ.v len)
        T.IoError
        (S.fail 's T.IoError);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_local_fail_view raw_view T.IoError 's).CL.raw_log)
        (note_local_fail_view raw_view T.IoError 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view raw_view T.IoError 's));
      false
    }
  } else {
    ST.advance_fail 'st T.IoError;
    advance_log_event
      c.log
      (CL.local_fail_event T.IoError)
      (S.Fail T.IoError)
      (S.fail 's T.IoError);
    assert (pure (CL.connection_view_consistent (note_local_fail_view 'view0 T.IoError 's)));
    assert (pure ((note_local_fail_view 'view0 T.IoError 's).CL.state == S.fail 's T.IoError));
    CL.lemma_raw_io_log_extends_refl 'view0.CL.raw_log;
    assert (pure (CL.raw_io_log_same_sent 'view0.CL.raw_log 'view0.CL.raw_log));
    CL.lemma_step_read_failed
      'view0
      'view0
      (SZ.v len)
      T.IoError
      (S.fail 's T.IoError);
    assert (pure (exists resp. CL.step 'view0
      (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log (note_local_fail_view 'view0 T.IoError 's).CL.raw_log)
      (note_local_fail_view 'view0 T.IoError 's)
      resp));
    fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view 'view0 T.IoError 's));
    false
  }
}

fn client_read (c: connection) (ch: IO.channel) (out: array U8.t) (max_len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
           IO.is_channel ch **
           pts_to out 'old **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* s' view1 bytes. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to out bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0
                  (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v max_len)) 'view0.CL.raw_log view1.CL.raw_log)
                  view1 resp) /\
                B.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Closing \/
                 s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))
{
  let ok = client_read_exact c ch out max_len;
  if ok {
    max_len
  } else {
    0sz
  }
}

fn client_close (c: connection) (ch: IO.channel)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pure ('s.S.phase == S.ApplicationData)
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in CL.OpClose) view1 resp) /\
                (s'.S.phase == S.Closing \/ s'.S.phase == S.Failed))
{
  unfold (connection_exactly c 'st 's 'view0);
  let keys_installed = !c.application_keys_installed;
  if keys_installed {
    let close_notify_sent =
      client_send_close_notify_record c.backend ch c.client_application_record_state c.log;
    with record_s' raw_view. _;
    if close_notify_sent {
      let ok = E.client_close c.backend ch;
      if ok {
        ST.advance 'st S.SendCloseNotify (S.send_close_state 's);
        assert (pure (raw_view.CL.state == 's));
        advance_log_event
          c.log
          CL.sent_close_notify_event
          S.SendCloseNotify
          (S.send_close_state 's);
        assert (pure (CL.connection_view_consistent (note_send_close_view raw_view 's)));
        assert (pure ((note_send_close_view raw_view 's).CL.state == S.send_close_state 's));
        assert (pure ((note_send_close_view raw_view 's).CL.app_view == raw_view.CL.app_view));
        assert (pure (CL.connection_view_single_step 'view0 (note_send_close_view raw_view 's)));
        CL.lemma_step_close_success
          'view0
          raw_view
          (S.send_close_state 's);
        assert (pure (exists resp. CL.step 'view0
          (CL.request_no_network_in CL.OpClose)
          (note_send_close_view raw_view 's)
          resp));
        fold (connection_exactly c 'st (S.send_close_state 's) (note_send_close_view raw_view 's));
      } else {
        ST.advance_fail 'st T.IoError;
        assert (pure (raw_view.CL.state == 's));
        advance_log_event
          c.log
          (CL.local_fail_event T.IoError)
          (S.Fail T.IoError)
          (S.fail 's T.IoError);
        assert (pure (CL.connection_view_consistent (note_local_fail_view raw_view T.IoError 's)));
        assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.state == S.fail 's T.IoError));
        assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.app_view == raw_view.CL.app_view));
        assert (pure (CL.connection_view_single_step 'view0 (note_local_fail_view raw_view T.IoError 's)));
        CL.lemma_step_close_failed
          'view0
          raw_view
          T.IoError
          (S.fail 's T.IoError);
        assert (pure (exists resp. CL.step 'view0
          (CL.request_no_network_in CL.OpClose)
          (note_local_fail_view raw_view T.IoError 's)
          resp));
        fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view raw_view T.IoError 's));
      }
    } else {
      ST.advance_fail 'st T.IoError;
      assert (pure (raw_view.CL.state == 's));
      advance_log_event
        c.log
        (CL.local_fail_event T.IoError)
        (S.Fail T.IoError)
        (S.fail 's T.IoError);
      assert (pure (CL.connection_view_consistent (note_local_fail_view raw_view T.IoError 's)));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.state == S.fail 's T.IoError));
      assert (pure ((note_local_fail_view raw_view T.IoError 's).CL.app_view == raw_view.CL.app_view));
      assert (pure (CL.connection_view_single_step 'view0 (note_local_fail_view raw_view T.IoError 's)));
      CL.lemma_step_close_failed
        'view0
        raw_view
        T.IoError
        (S.fail 's T.IoError);
      assert (pure (exists resp. CL.step 'view0
        (CL.request_no_network_in CL.OpClose)
        (note_local_fail_view raw_view T.IoError 's)
        resp));
      fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view raw_view T.IoError 's));
    }
  } else {
    ST.advance_fail 'st T.IoError;
    advance_log_event
      c.log
      (CL.local_fail_event T.IoError)
      (S.Fail T.IoError)
      (S.fail 's T.IoError);
    assert (pure (CL.connection_view_consistent (note_local_fail_view 'view0 T.IoError 's)));
    assert (pure ((note_local_fail_view 'view0 T.IoError 's).CL.state == S.fail 's T.IoError));
    CL.lemma_raw_io_log_extends_refl 'view0.CL.raw_log;
    assert (pure (CL.raw_io_log_same_received 'view0.CL.raw_log 'view0.CL.raw_log));
    CL.lemma_step_close_failed
      'view0
      'view0
      T.IoError
      (S.fail 's T.IoError);
    assert (pure (exists resp. CL.step 'view0
      (CL.request_no_network_in CL.OpClose)
      (note_local_fail_view 'view0 T.IoError 's)
      resp));
    fold (connection_exactly c 'st (S.fail 's T.IoError) (note_local_fail_view 'view0 T.IoError 's));
  }
}
