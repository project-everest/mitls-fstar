module TLS13.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BD = TLS13.Handshake.ByteDriver
module BDE = TLS13.Handshake.ByteDriver.External
module Cast = FStar.Int.Cast
module E = TLS13.Handshake.External
module FS = TLS13.Handshake.FlightState
module H = TLS13.Handshake.Spec
module HW = TLS13.Connection.HandshakeWitness
module HF = TLS13.Handshake.Framing
module IO = TLS13.IO
module RF = TLS13.Record.Framing
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

noeq
type handshake_context = {
  backend: E.handshake_context;
  flight: FS.flight_state;
}

let is_handshake_context (ctx:handshake_context) (st:ST.state_ref) (s:S.conn_state) : slprop =
  E.is_context ctx.backend ** FS.is_flight_state ctx.flight ** ST.current st s

let server_hello_fragment_capacity : SZ.t = 4096sz

inline_for_extraction
fn write_fixed_client_random (random: array U8.t)
  requires pts_to random 'old **
           pure (B.length 'old == 32)
  ensures exists* bytes. pts_to random bytes ** pure (B.length bytes == 32)
{
  pts_to_len random;
  random.(0sz) <- 0x00uy;
  random.(1sz) <- 0x01uy;
  random.(2sz) <- 0x02uy;
  random.(3sz) <- 0x03uy;
  random.(4sz) <- 0x04uy;
  random.(5sz) <- 0x05uy;
  random.(6sz) <- 0x06uy;
  random.(7sz) <- 0x07uy;
  random.(8sz) <- 0x08uy;
  random.(9sz) <- 0x09uy;
  random.(10sz) <- 0x0auy;
  random.(11sz) <- 0x0buy;
  random.(12sz) <- 0x0cuy;
  random.(13sz) <- 0x0duy;
  random.(14sz) <- 0x0euy;
  random.(15sz) <- 0x0fuy;
  random.(16sz) <- 0x10uy;
  random.(17sz) <- 0x11uy;
  random.(18sz) <- 0x12uy;
  pts_to_len random;
  with random_mid. assert (pts_to random random_mid);
  assert (pure (B.length random_mid == 32));
  random.(19sz) <- 0x13uy;
  random.(20sz) <- 0x14uy;
  random.(21sz) <- 0x15uy;
  random.(22sz) <- 0x16uy;
  random.(23sz) <- 0x17uy;
  random.(24sz) <- 0x18uy;
  random.(25sz) <- 0x19uy;
  random.(26sz) <- 0x1auy;
  random.(27sz) <- 0x1buy;
  random.(28sz) <- 0x1cuy;
  random.(29sz) <- 0x1duy;
  random.(30sz) <- 0x1euy;
  random.(31sz) <- 0x1fuy;
  pts_to_len random;
  with bytes. assert (pts_to random bytes);
  assert (pure (B.length bytes == 32));
}

inline_for_extraction
fn write_fixed_client_key_share (key_share: array U8.t)
  requires pts_to key_share 'old **
           pure (B.length 'old == 32)
  ensures exists* bytes. pts_to key_share bytes ** pure (B.length bytes == 32)
{
  pts_to_len key_share;
  key_share.(0sz) <- 0x99uy;
  key_share.(1sz) <- 0x38uy;
  key_share.(2sz) <- 0x1duy;
  key_share.(3sz) <- 0xe5uy;
  key_share.(4sz) <- 0x60uy;
  key_share.(5sz) <- 0xe4uy;
  key_share.(6sz) <- 0xbduy;
  key_share.(7sz) <- 0x43uy;
  key_share.(8sz) <- 0xd2uy;
  key_share.(9sz) <- 0x3duy;
  key_share.(10sz) <- 0x8euy;
  key_share.(11sz) <- 0x43uy;
  key_share.(12sz) <- 0x5auy;
  key_share.(13sz) <- 0x7duy;
  key_share.(14sz) <- 0xbauy;
  key_share.(15sz) <- 0xfeuy;
  key_share.(16sz) <- 0xb3uy;
  key_share.(17sz) <- 0xc0uy;
  key_share.(18sz) <- 0x6euy;
  pts_to_len key_share;
  with key_share_mid. assert (pts_to key_share key_share_mid);
  assert (pure (B.length key_share_mid == 32));
  key_share.(19sz) <- 0x51uy;
  pts_to_len key_share;
  with mid. assert (pts_to key_share mid);
  assert (pure (B.length mid == 32));
  key_share.(20sz) <- 0xc1uy;
  key_share.(21sz) <- 0x3cuy;
  key_share.(22sz) <- 0xaeuy;
  key_share.(23sz) <- 0x4duy;
  key_share.(24sz) <- 0x54uy;
  key_share.(25sz) <- 0x13uy;
  key_share.(26sz) <- 0x69uy;
  key_share.(27sz) <- 0x1euy;
  key_share.(28sz) <- 0x52uy;
  key_share.(29sz) <- 0x9auy;
  key_share.(30sz) <- 0xafuy;
  key_share.(31sz) <- 0x2cuy;
  pts_to_len key_share;
  with bytes. assert (pts_to key_share bytes);
  assert (pure (B.length bytes == 32));
}

fn handshake_context_new ()
  returns ctx: handshake_context
  ensures exists* st. is_handshake_context ctx st S.initial
{
  let backend = E.context_new ();
  let flight = FS.flight_state_new ();
  let st = ST.alloc_initial ();
  let ctx = { backend; flight };
  rewrite (E.is_context backend) as (E.is_context ctx.backend);
  rewrite (FS.is_flight_state flight) as (FS.is_flight_state ctx.flight);
  fold (is_handshake_context ctx st S.initial);
  ctx
}

fn handshake_context_free (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's
  ensures emp
{
  unfold (is_handshake_context ctx 'st 's);
  E.context_free ctx.backend;
  FS.flight_state_free ctx.flight;
  drop_ (ST.current 'st 's);
}

fn rec read_raw_exact
  (ctx: handshake_context)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires E.is_context ctx.backend **
           IO.is_channel ch **
           pts_to buf 'old **
           pure (B.length 'old == SZ.v total_len /\
                 SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* bytes.
          E.is_context ctx.backend **
          IO.is_channel ch **
          pts_to buf bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.read_raw ctx.backend ch buf total_len offset remaining;
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

fn rec write_raw_exact
  (ctx: handshake_context)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires E.is_context ctx.backend **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure (B.length 'bytes == SZ.v total_len /\
                 SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures E.is_context ctx.backend **
          IO.is_channel ch **
          pts_to buf 'bytes
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.write_raw ctx.backend ch buf total_len offset remaining;
    if (n = 0sz) {
      false
    } else {
      let offset' = SZ.(offset +^ n);
      let remaining' = SZ.(remaining -^ n);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      write_raw_exact ctx ch buf total_len offset' remaining'
    }
  }
}

fn send_client_hello (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ClientHelloSent) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_handshake_context ctx 'st 's);
  let mut random = [| 0uy; 32sz |];
  let mut key_share = [| 0uy; 32sz |];
  let mut hello = [| 0uy; 130sz |];
  let mut header = [| 0uy; 5sz |];
  write_fixed_client_random random;
  write_fixed_client_key_share key_share;
  let built = HF.build_supported_client_hello_localhost random key_share hello 130sz;
  if built {
    let stored = E.store_client_hello ctx.backend hello 130sz;
    if stored {
      FS.set_client_hello_fragment ctx.flight hello 130sz;
      HF.serialize_client_hello_record_header header 5sz;
      let connected = E.connect ctx.backend ch;
      if connected {
        let header_ok = write_raw_exact ctx ch header 5sz 0sz 5sz;
        let hello_ok =
          if header_ok {
            write_raw_exact ctx ch hello 130sz 0sz 130sz
          } else {
            false
          };
        if hello_ok {
          assert (pure (S.step 's (S.SendClientHello HW.dummy_client_hello) == Some (S.with_phase 's S.ClientHelloSent)));
          ST.advance 'st (S.SendClientHello HW.dummy_client_hello) (S.with_phase 's S.ClientHelloSent);
          fold (is_handshake_context ctx 'st (S.with_phase 's S.ClientHelloSent));
          true
        } else {
          assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
          ST.advance_fail 'st T.IoError;
          fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
          false
        }
      } else {
        assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
        ST.advance_fail 'st T.IoError;
        fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
        false
      }
    } else {
      assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
      ST.advance_fail 'st T.IoError;
      fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
      false
    }
  } else {
    assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
    ST.advance_fail 'st T.IoError;
    fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
    false
  }
}

inline_for_extraction
fn recv_server_hello_record (ctx: handshake_context) (ch: IO.channel)
  requires E.is_context ctx.backend ** FS.is_flight_state ctx.flight ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx.backend ** FS.is_flight_state ctx.flight ** IO.is_channel ch
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
          let mut server_random = [| 0uy; 32sz |];
          let mut key_share = [| 0uy; 32sz |];
          let parsed =
            HF.parse_supported_server_hello
              fragment
              fragment_len
              server_random
              32sz
              key_share
              32sz;
          if parsed {
            let backend_ok =
              E.process_server_hello_record
                ctx.backend
                header
                5sz
                fragment
                fragment_len
                key_share
                32sz;
            if backend_ok {
              FS.set_server_hello_fragment ctx.flight fragment fragment_len;
              FS.derive_server_handshake_keys_from_share ctx.flight key_share 32sz
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
    assert (pure (S.step 's (S.RecvServerHello HW.dummy_server_hello) == Some (S.with_phase 's S.ServerHelloReceived)));
    ST.advance 'st (S.RecvServerHello HW.dummy_server_hello) (S.with_phase 's S.ServerHelloReceived);
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
  unfold (E.is_context ctx.backend);
  with p. assert (BDE.is_context ctx.backend p);
  let ok = BD.recv_encrypted_handshake ctx.backend ctx.flight ch;
  fold (E.is_context ctx.backend);
  if ok {
    assert (pure (S.step 's (S.RecvEncryptedExtensions HW.dummy_encrypted_extensions) == Some (S.with_phase 's S.EncryptedExtensionsReceived)));
    ST.advance 'st (S.RecvEncryptedExtensions HW.dummy_encrypted_extensions) (S.with_phase 's S.EncryptedExtensionsReceived);
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
  let backend_ok = E.certificate_received ctx.backend;
  FS.reveal_flight_view ctx.flight;
  let flight_ok = FS.saw_certificate_exact ctx.flight;
  FS.hide_flight_view ctx.flight;
  let ok = backend_ok && flight_ok;
  if ok {
    assert (pure (S.step 's (S.RecvCertificate HW.dummy_certificate) == Some (S.with_phase 's S.CertificateReceived)));
    ST.advance 'st (S.RecvCertificate HW.dummy_certificate) (S.with_phase 's S.CertificateReceived);
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
  let ok = E.validate_certificate ctx.backend;
  if ok {
    assert (pure (S.step 's (S.ValidateCertificate HW.dummy_peer) == Some (S.with_validated_peer 's HW.dummy_peer)));
    ST.advance 'st (S.ValidateCertificate HW.dummy_peer) (S.with_validated_peer 's HW.dummy_peer);
    fold (is_handshake_context ctx 'st (S.with_validated_peer 's HW.dummy_peer));
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
  let backend_ok = E.certificate_verify_verified ctx.backend;
  FS.reveal_flight_view ctx.flight;
  let saw_cv = FS.saw_certificate_verify_exact ctx.flight;
  let ok =
    if (saw_cv && backend_ok) {
      FS.mark_certificate_verify_verified_exact ctx.flight;
      FS.hide_flight_view ctx.flight;
      true
    } else {
      FS.hide_flight_view ctx.flight;
      false
    };
  if ok {
    assert (pure (S.step 's (S.RecvCertificateVerify HW.dummy_certificate_verify) == Some (S.with_phase 's S.CertificateVerified)));
    ST.advance 'st (S.RecvCertificateVerify HW.dummy_certificate_verify) (S.with_phase 's S.CertificateVerified);
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
  FS.reveal_flight_view ctx.flight;
  let cv_ok = FS.certificate_verify_verified_exact ctx.flight;
  let saw_finished = FS.saw_finished_exact ctx.flight;
  FS.hide_flight_view ctx.flight;
  let ok =
    if (cv_ok && saw_finished) {
      FS.verify_server_finished ctx.flight
    } else {
      false
    };
  if ok {
    assert (pure (S.step 's (S.RecvServerFinished HW.dummy_finished) == Some (S.with_phase 's S.ServerFinishedVerified)));
    ST.advance 'st (S.RecvServerFinished HW.dummy_finished) (S.with_phase 's S.ServerFinishedVerified);
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
  let mut record = [| 0uy; 58sz |];
  let built = FS.build_client_finished_record ctx.flight record 58sz;
  let ok =
    if built {
      write_raw_exact ctx ch record 58sz 0sz 58sz
    } else {
      false
    };
  if ok {
    assert (pure (S.step 's (S.SendClientFinished HW.dummy_finished) == Some (S.with_phase 's S.ApplicationData)));
    ST.advance 'st (S.SendClientFinished HW.dummy_finished) (S.with_phase 's S.ApplicationData);
    fold (is_handshake_context ctx 'st (S.with_phase 's S.ApplicationData));
    true
  } else {
    assert (pure (S.step 's (S.Fail T.IoError) == Some (S.fail 's T.IoError)));
    ST.advance_fail 'st T.IoError;
    fold (is_handshake_context ctx 'st (S.fail 's T.IoError));
    false
  }
}
