module TLS13.Connection.HandshakeWitness

module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module X = TLS13.X509.Spec

type handshake_evidence = {
  client_hello: H.client_hello;
  server_hello: (sh:H.server_hello{H.is_supported_cipher_suite sh.H.cipher_suite});
  encrypted_extensions: H.encrypted_extensions;
  certificate: H.certificate_msg;
  peer: X.peer_identity;
  certificate_verify: H.certificate_verify;
  server_finished: H.finished;
  client_finished: H.finished;
}

let hs_client_hello_sent (s:S.conn_state) = S.with_phase s S.ClientHelloSent
let hs_server_hello_received (s:S.conn_state) = S.with_phase (hs_client_hello_sent s) S.ServerHelloReceived
let hs_encrypted_extensions_received (s:S.conn_state) = S.with_phase (hs_server_hello_received s) S.EncryptedExtensionsReceived
let hs_certificate_received (s:S.conn_state) = S.with_phase (hs_encrypted_extensions_received s) S.CertificateReceived
let hs_certificate_validated_with (peer:X.peer_identity) (s:S.conn_state) =
  S.with_validated_peer (hs_certificate_received s) peer
let hs_certificate_verified_with (peer:X.peer_identity) (s:S.conn_state) =
  S.with_phase (hs_certificate_validated_with peer s) S.CertificateVerified
let hs_server_finished_verified_with (peer:X.peer_identity) (s:S.conn_state) =
  S.with_phase (hs_certificate_verified_with peer s) S.ServerFinishedVerified
let hs_application_data_with (peer:X.peer_identity) (s:S.conn_state) =
  S.with_phase (hs_server_finished_verified_with peer s) S.ApplicationData

let sent_handshake_event (msg:H.handshake_msg) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Sent; CL.message_value = CL.TlsHandshake msg }

let received_handshake_event (msg:H.handshake_msg) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Received; CL.message_value = CL.TlsHandshake msg }

let hs_log_view1_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event view (sent_handshake_event (H.ClientHello ev.client_hello)) (hs_client_hello_sent s)

let hs_log_view2_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view1_with ev view s) (received_handshake_event (H.ServerHello ev.server_hello)) (hs_server_hello_received s)

let hs_log_view3_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view2_with ev view s) (received_handshake_event (H.EncryptedExtensions ev.encrypted_extensions)) (hs_encrypted_extensions_received s)

let hs_log_view4_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view3_with ev view s) (received_handshake_event (H.Certificate ev.certificate)) (hs_certificate_received s)

let hs_log_view5_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view4_with ev view s) (CL.LocalEvent (CL.LocalValidateCertificate ev.peer)) (hs_certificate_validated_with ev.peer s)

let hs_log_view6_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view5_with ev view s) (received_handshake_event (H.CertificateVerify ev.certificate_verify)) (hs_certificate_verified_with ev.peer s)

let hs_log_view7_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view6_with ev view s) (received_handshake_event (H.Finished ev.server_finished)) (hs_server_finished_verified_with ev.peer s)

let successful_handshake_view_with (ev:handshake_evidence) (view:CL.connection_view) (s:S.conn_state) : CL.connection_view =
  CL.note_host_event (hs_log_view7_with ev view s) (sent_handshake_event (H.Finished ev.client_finished)) (hs_application_data_with ev.peer s)

let lemma_successful_handshake_state_evolves_with
  (ev:handshake_evidence)
  (s:S.conn_state)
  : Lemma
      (requires s.S.phase == S.Start)
      (ensures S.conn_evolves s (hs_application_data_with ev.peer s))
  =
  let s1 = hs_client_hello_sent s in
  let s2 = hs_server_hello_received s in
  let s3 = hs_encrypted_extensions_received s in
  let s4 = hs_certificate_received s in
  let s5 = hs_certificate_validated_with ev.peer s in
  let s6 = hs_certificate_verified_with ev.peer s in
  let s7 = hs_server_finished_verified_with ev.peer s in
  let s8 = hs_application_data_with ev.peer s in
  assert (S.step s (S.SendClientHello ev.client_hello) == Some s1);
  assert (S.state_single_step s s1);
  RTC.closure_step S.state_single_step s s1;
  assert (S.step s1 (S.RecvServerHello ev.server_hello) == Some s2);
  assert (S.state_single_step s1 s2);
  RTC.closure_step S.state_single_step s1 s2;
  assert (S.step s2 (S.RecvEncryptedExtensions ev.encrypted_extensions) == Some s3);
  assert (S.state_single_step s2 s3);
  RTC.closure_step S.state_single_step s2 s3;
  assert (S.step s3 (S.RecvCertificate ev.certificate) == Some s4);
  assert (S.state_single_step s3 s4);
  RTC.closure_step S.state_single_step s3 s4;
  assert (S.step s4 (S.ValidateCertificate ev.peer) == Some s5);
  assert (S.state_single_step s4 s5);
  RTC.closure_step S.state_single_step s4 s5;
  assert (S.step s5 (S.RecvCertificateVerify ev.certificate_verify) == Some s6);
  assert (S.state_single_step s5 s6);
  RTC.closure_step S.state_single_step s5 s6;
  assert (S.step s6 (S.RecvServerFinished ev.server_finished) == Some s7);
  assert (S.state_single_step s6 s7);
  RTC.closure_step S.state_single_step s6 s7;
  assert (S.step s7 (S.SendClientFinished ev.client_finished) == Some s8);
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
