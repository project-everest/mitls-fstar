module TLS13.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module E = TLS13.Handshake.External
module H = TLS13.Handshake.Spec
module IO = TLS13.IO
module RF = TLS13.Record.Framing
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

type handshake_context = E.handshake_context

let is_handshake_context (ctx:handshake_context) (st:ST.state_ref) (s:S.conn_state) : slprop =
  E.is_context ctx ** ST.current st s

let zeros32 : B.bytes = B.zeros 32
let server_hello_fragment_capacity : SZ.t = 4096sz

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

fn handshake_context_new ()
  returns ctx: handshake_context
  ensures exists* st. is_handshake_context ctx st S.initial
{
  let ctx = E.context_new ();
  let st = ST.alloc_initial ();
  fold (is_handshake_context ctx st S.initial);
  ctx
}

fn handshake_context_free (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's
  ensures emp
{
  unfold (is_handshake_context ctx 'st 's);
  E.context_free ctx;
  drop_ (ST.current 'st 's);
}

fn send_client_hello (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure (s'.S.phase == S.ClientHelloSent)
{
  unfold (is_handshake_context ctx 'st 's);
  E.send_client_hello ctx ch;
  assert (pure (S.step 's (S.SendClientHello dummy_client_hello) == Some (S.with_phase 's S.ClientHelloSent)));
  ST.advance 'st (S.SendClientHello dummy_client_hello) (S.with_phase 's S.ClientHelloSent);
  fold (is_handshake_context ctx 'st (S.with_phase 's S.ClientHelloSent));
}

fn rec read_raw_exact
  (ctx: handshake_context)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires E.is_context ctx **
           IO.is_channel ch **
           pts_to buf 'old **
           pure (B.length 'old == SZ.v total_len /\
                 SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* bytes.
          E.is_context ctx **
          IO.is_channel ch **
          pts_to buf bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.read_raw ctx ch buf total_len offset remaining;
    if (n = 0sz) {
      false
    } else {
      with bytes. assert (pts_to buf bytes);
      let offset' = SZ.(offset +^ n);
      let remaining' = SZ.(remaining -^ n);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      read_raw_exact ctx ch buf total_len offset' remaining'
    }
  }
}

inline_for_extraction
fn recv_server_hello_record (ctx: handshake_context) (ch: IO.channel)
  requires E.is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx ** IO.is_channel ch
{
  let mut header = [| 0uy; 5sz |];
  let header_ok = read_raw_exact ctx ch header 5sz 0sz 5sz;
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
      if ((content_type = 22uy) &&
          SZ.(0sz <^ fragment_len) &&
          SZ.(fragment_len <=^ server_hello_fragment_capacity)) {
        let mut fragment = [| 0uy; fragment_len |];
        let fragment_ok = read_raw_exact ctx ch fragment fragment_len 0sz fragment_len;
        if fragment_ok {
          E.process_server_hello_record ctx header 5sz fragment fragment_len
        } else {
          false
        }
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

fn recv_server_hello (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ClientHelloSent)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ServerHelloReceived) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = recv_server_hello_record ctx ch;
  if ok {
    assert (pure (S.step 's (S.RecvServerHello dummy_server_hello) == Some (S.with_phase 's S.ServerHelloReceived)));
    ST.advance 'st (S.RecvServerHello dummy_server_hello) (S.with_phase 's S.ServerHelloReceived);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.ServerHelloReceived));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.UnsupportedCipherSuite) == Some (S.fail 's T.UnsupportedCipherSuite)));
    ST.advance_fail 'st T.UnsupportedCipherSuite;
    fold (is_handshake_context ctx 'st (S.fail 's T.UnsupportedCipherSuite));
    false
  }
}

fn recv_encrypted_extensions (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ServerHelloReceived)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.EncryptedExtensionsReceived) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.recv_encrypted_extensions ctx ch;
  if ok {
    assert (pure (S.step 's (S.RecvEncryptedExtensions dummy_encrypted_extensions) == Some (S.with_phase 's S.EncryptedExtensionsReceived)));
    ST.advance 'st (S.RecvEncryptedExtensions dummy_encrypted_extensions) (S.with_phase 's S.EncryptedExtensionsReceived);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.EncryptedExtensionsReceived));
    true
  } else {
    assert (pure (S.step 's (S.Fail (T.AlertError T.DecodeError)) == Some (S.fail 's (T.AlertError T.DecodeError))));
    ST.advance_fail 'st (T.AlertError T.DecodeError);
    fold (is_handshake_context ctx 'st (S.fail 's (T.AlertError T.DecodeError)));
    false
  }
}

fn recv_certificate (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.EncryptedExtensionsReceived)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.CertificateReceived) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.recv_certificate ctx ch;
  if ok {
    assert (pure (S.step 's (S.RecvCertificate dummy_certificate) == Some (S.with_phase 's S.CertificateReceived)));
    ST.advance 'st (S.RecvCertificate dummy_certificate) (S.with_phase 's S.CertificateReceived);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.CertificateReceived));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.BadCertificate) == Some (S.fail 's T.BadCertificate)));
    ST.advance_fail 'st T.BadCertificate;
    fold (is_handshake_context ctx 'st (S.fail 's T.BadCertificate));
    false
  }
}

fn validate_certificate (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's **
           pure ('s.S.phase == S.CertificateReceived)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          pure ((ok ==> s'.S.phase == S.CertificateValidated /\ Some? s'.S.peer) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.validate_certificate ctx;
  if ok {
    assert (pure (S.step 's (S.ValidateCertificate dummy_peer) == Some (S.with_validated_peer 's dummy_peer)));
    ST.advance 'st (S.ValidateCertificate dummy_peer) (S.with_validated_peer 's dummy_peer);
    fold (is_handshake_context ctx 'st (S.with_validated_peer 's dummy_peer));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.BadCertificate) == Some (S.fail 's T.BadCertificate)));
    ST.advance_fail 'st T.BadCertificate;
    fold (is_handshake_context ctx 'st (S.fail 's T.BadCertificate));
    false
  }
}

fn recv_certificate_verify (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.CertificateValidated /\ Some? 's.S.peer)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.CertificateVerified) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.recv_certificate_verify ctx ch;
  if ok {
    assert (pure (S.step 's (S.RecvCertificateVerify dummy_certificate_verify) == Some (S.with_phase 's S.CertificateVerified)));
    ST.advance 'st (S.RecvCertificateVerify dummy_certificate_verify) (S.with_phase 's S.CertificateVerified);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.CertificateVerified));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.BadCertificateVerify) == Some (S.fail 's T.BadCertificateVerify)));
    ST.advance_fail 'st T.BadCertificateVerify;
    fold (is_handshake_context ctx 'st (S.fail 's T.BadCertificateVerify));
    false
  }
}

fn recv_server_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.CertificateVerified)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ServerFinishedVerified) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.recv_server_finished ctx ch;
  if ok {
    assert (pure (S.step 's (S.RecvServerFinished dummy_finished) == Some (S.with_phase 's S.ServerFinishedVerified)));
    ST.advance 'st (S.RecvServerFinished dummy_finished) (S.with_phase 's S.ServerFinishedVerified);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.ServerFinishedVerified));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.BadFinished) == Some (S.fail 's T.BadFinished)));
    ST.advance_fail 'st T.BadFinished;
    fold (is_handshake_context ctx 'st (S.fail 's T.BadFinished));
    false
  }
}

fn send_client_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ServerFinishedVerified)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let ok = E.send_client_finished ctx ch;
  if ok {
    assert (pure (S.step 's (S.SendClientFinished dummy_finished) == Some (S.with_phase 's S.ApplicationData)));
    ST.advance 'st (S.SendClientFinished dummy_finished) (S.with_phase 's S.ApplicationData);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.ApplicationData));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
    ST.advance_fail 'st T.IoError;
    fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
    false
  }
}
