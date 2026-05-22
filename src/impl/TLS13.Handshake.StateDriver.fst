module TLS13.Handshake.StateDriver

#lang-pulse

open Pulse.Lib.Pervasives

module H = TLS13.Handshake.Spec
module S = TLS13.StateMachine
module ST = TLS13.State
module X = TLS13.X509.Spec

ghost
fn run_controlled_handshake
  (st:ST.state_ref)
  (ch:H.client_hello)
  (sh:H.server_hello)
  (ee:H.encrypted_extensions)
  (cert:H.certificate_msg)
  (peer:X.peer_identity)
  (cv:H.certificate_verify)
  (sf:H.finished)
  (cf:H.finished)
  requires ST.current st S.initial
  requires pure (H.is_supported_cipher_suite sh.H.cipher_suite == true)
  ensures exists* s.
          ST.current st s **
          ST.snapshot st S.initial **
          pure (S.conn_evolves S.initial s /\ s.S.phase == S.ApplicationData)
{
  ST.take_snapshot st;

  let s1 = S.with_phase S.initial S.ClientHelloSent;
  ST.advance st (S.SendClientHello ch) s1;

  let s2 = S.with_phase s1 S.ServerHelloReceived;
  ST.advance st (S.RecvServerHello sh) s2;

  let s3 = S.with_phase s2 S.EncryptedExtensionsReceived;
  ST.advance st (S.RecvEncryptedExtensions ee) s3;

  let s4 = S.with_phase s3 S.CertificateReceived;
  ST.advance st (S.RecvCertificate cert) s4;

  let s5 = S.with_validated_peer s4 peer;
  ST.advance st (S.ValidateCertificate peer) s5;

  let s6 = S.with_phase s5 S.CertificateVerified;
  ST.advance st (S.RecvCertificateVerify cv) s6;

  let s7 = S.with_phase s6 S.ServerFinishedVerified;
  ST.advance st (S.RecvServerFinished sf) s7;

  let s8 = S.with_phase s7 S.ApplicationData;
  ST.advance st (S.SendClientFinished cf) s8;

  ST.recall_snapshot st;
}
