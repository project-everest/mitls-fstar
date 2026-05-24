module TLS13.Connection

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Cast = FStar.Int.Cast
module E = TLS13.Connection.External
module H = TLS13.Handshake.Spec
module IO = TLS13.IO
module Rec = TLS13.Record
module RF = TLS13.Record.Framing
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module X = TLS13.X509.Spec

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
}

let is_connection (c:connection) (st:ST.state_ref) (s:S.conn_state) : slprop =
  exists* live app_keys_installed client_key client_iv server_key server_iv
          client_record_state server_record_state.
    E.is_connection c.backend **
    Box.pts_to c.live live **
    Box.pts_to c.application_keys_installed app_keys_installed **
    V.pts_to c.client_application_key client_key **
    V.pts_to c.client_application_iv client_iv **
    V.pts_to c.server_application_key server_key **
    V.pts_to c.server_application_iv server_iv **
    Rec.is_record_state c.client_application_record_state client_record_state **
    Rec.is_record_state c.server_application_record_state server_record_state **
    ST.current st s **
    pure (V.is_full_vec c.client_application_key /\
          V.is_full_vec c.client_application_iv /\
          V.is_full_vec c.server_application_key /\
          V.is_full_vec c.server_application_iv /\
          V.length c.client_application_key == 32 /\
          V.length c.client_application_iv == 12 /\
          V.length c.server_application_key == 32 /\
          V.length c.server_application_iv == 12)

let zeros32 : B.bytes = B.zeros 32
let app_record_chunk_len : SZ.t = 4096sz
let max_application_read_records : U8.t = 255uy

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

fn client_new
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (#trust_store: X.trust_store)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns c: connection
  ensures exists* st.
          pts_to hostname 'hostname_bytes **
          is_connection c st S.initial
{
  let backend = E.client_new hostname hostname_len #trust_store;
  let live = Box.alloc true;
  let app_keys_installed = Box.alloc false;
  let client_application_key = V.alloc 0uy 32sz;
  let client_application_iv = V.alloc 0uy 12sz;
  let server_application_key = V.alloc 0uy 32sz;
  let server_application_iv = V.alloc 0uy 12sz;
  let client_application_record_state = Rec.record_state_new ();
  let server_application_record_state = Rec.record_state_new ();
  let st = ST.alloc_initial ();
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
  };
  with backend_s. rewrite (E.is_connection backend) as (E.is_connection c.backend);
  with live_s. rewrite (Box.pts_to live live_s) as (Box.pts_to c.live live_s);
  with installed_s. rewrite (Box.pts_to app_keys_installed installed_s) as (Box.pts_to c.application_keys_installed installed_s);
  with ck_s. rewrite (V.pts_to client_application_key ck_s) as (V.pts_to c.client_application_key ck_s);
  with ci_s. rewrite (V.pts_to client_application_iv ci_s) as (V.pts_to c.client_application_iv ci_s);
  with sk_s. rewrite (V.pts_to server_application_key sk_s) as (V.pts_to c.server_application_key sk_s);
  with si_s. rewrite (V.pts_to server_application_iv si_s) as (V.pts_to c.server_application_iv si_s);
  with crs. rewrite (Rec.is_record_state client_application_record_state crs) as (Rec.is_record_state c.client_application_record_state crs);
  with srs. rewrite (Rec.is_record_state server_application_record_state srs) as (Rec.is_record_state c.server_application_record_state srs);
  fold (is_connection c st S.initial);
  c
}

fn client_free (c: connection)
  requires is_connection c 'st 's
  ensures emp
{
  unfold (is_connection c 'st 's);
  E.client_free c.backend;
  Box.free c.live;
  Box.free c.application_keys_installed;
  V.free c.client_application_key;
  V.free c.client_application_iv;
  V.free c.server_application_key;
  V.free c.server_application_iv;
  Rec.record_state_free c.client_application_record_state;
  Rec.record_state_free c.server_application_record_state;
  drop_ (ST.current 'st 's);
}

fn client_connect (c: connection) (ch: IO.channel)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                        (not ok ==> s'.S.phase == S.Failed))
{
          unfold (is_connection c 'st 's);
          let mut client_key = [| 0uy; 32sz |];
          let mut client_iv = [| 0uy; 12sz |];
          let mut server_key = [| 0uy; 32sz |];
          let mut server_iv = [| 0uy; 12sz |];
          let ok = E.client_connect c.backend ch client_key client_iv server_key server_iv;
          if ok {
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
      fold (is_connection c 'st (hs_application_data 's));
      true
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    false
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
  requires   E.is_connection backend **
  Rec.is_record_state record_state 'record_s **
  IO.is_channel ch **
  pts_to buf 'bytes **
  pure (B.length 'bytes == SZ.v total_len /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* record_s'.
          E.is_connection backend **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          pts_to buf 'bytes
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
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
    let ok =
      if sealed {
        E.client_write_raw_record backend ch header 5sz cipher cipher_len
      } else {
        false
      };
    if ok {
      let offset' = SZ.(offset +^ chunk_len);
      let remaining' = SZ.(remaining -^ chunk_len);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      client_write_application_records backend ch record_state buf total_len offset' remaining'
    } else {
      false
    }
  }
}

fn client_write_all (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns ok: bool
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_connection c 'st 's);
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
        len;
    if ok {
      ST.advance 'st (S.SendApplicationData (Ghost.reveal 'bytes)) (S.advance_write_record 's);
      fold (is_connection c 'st (S.advance_write_record 's));
      true
    } else {
      ST.advance_fail 'st T.IoError;
      fold (is_connection c 'st (S.fail 's T.IoError));
      false
    }
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    false
  }
}

fn client_write (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns written: SZ.t
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (SZ.v written <= SZ.v len /\
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

fn rec client_read_application_records
  (backend: E.connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (out: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  (fuel: U8.t)
  requires   E.is_connection backend **
  Rec.is_record_state record_state 'record_s **
  IO.is_channel ch **
  pts_to out 'old **
  pure (B.length 'old == SZ.v total_len /\
        SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* record_s' bytes.
          E.is_connection backend **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (U8.v fuel)
{
  if (remaining = 0sz) {
    true
  } else if (fuel = 0uy) {
    false
  } else {
    assert (pure (SZ.v remaining > 0));
    let mut header = [| 0uy; 5sz |];
    let header_ok = E.client_read_raw_record_header backend ch header 5sz;
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
          false
        } else if SZ.(16sz <^ fragment_len) {
          let mut cipher = [| 0uy; fragment_len |];
          let fragment_ok = E.client_read_raw_record_fragment backend ch cipher fragment_len;
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
                  RF.decode_inner_plaintext_no_padding inner inner_len inner_content_type_out 1sz;
                let inner_content_type = inner_content_type_out.(0sz);
                if (inner_content_type = 22uy) {
                  assert (pure (U8.v fuel' < U8.v fuel));
                  client_read_application_records backend ch record_state out total_len offset remaining fuel'
                } else if (not (inner_content_type = 23uy) || SZ.(remaining <^ response_len)) {
                  false
                } else {
                  copy_payload_to_output inner inner_len response_len out total_len offset;
                  with copied_bytes. assert (pts_to out copied_bytes);
                  let offset' = SZ.(offset +^ response_len);
                  let remaining' = SZ.(remaining -^ response_len);
                  assert (pure (U8.v fuel' < U8.v fuel));
                  assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
                  client_read_application_records backend ch record_state out total_len offset' remaining' fuel'
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
}

fn client_read_exact (c: connection) (ch: IO.channel) (out: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to out 'old **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v len)
  returns ok: bool
  ensures exists* s' bytes. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v len /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  unfold (is_connection c 'st 's);
  let keys_installed = !c.application_keys_installed;
  if keys_installed {
    assert (pure (B.length 'old == SZ.v len));
    assert (pure (0 + SZ.v len == SZ.v len));
    let ok =
      client_read_application_records
        c.backend
        ch
        c.server_application_record_state
        out
        len
        0sz
        len
        max_application_read_records;
  with bytes. assert (pts_to out bytes);
  if ok {
    ST.advance 'st (S.RecvApplicationData bytes) (S.advance_read_record 's);
    fold (is_connection c 'st (S.advance_read_record 's));
    true
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    false
  }
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    false
  }
}

fn client_read (c: connection) (ch: IO.channel) (out: array U8.t) (max_len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to out 'old **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* s' bytes. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\
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
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ApplicationData)
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pure (s'.S.phase == S.Closing \/ s'.S.phase == S.Failed)
{
  unfold (is_connection c 'st 's);
  let ok = E.client_close c.backend ch;
  if ok {
    ST.advance 'st S.SendCloseNotify (S.send_close_state 's);
    fold (is_connection c 'st (S.send_close_state 's));
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
  }
}
