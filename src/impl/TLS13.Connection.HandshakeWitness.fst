module TLS13.Connection.HandshakeWitness

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module T = TLS13.Types
module X = TLS13.X509.Spec

let zeros32 : B.bytes = B.zeros 32

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
