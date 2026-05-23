module TLS13.Connection

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module E = TLS13.Connection.External
module H = TLS13.Handshake.Spec
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

noeq
type connection = {
  backend: E.connection;
  live: box bool;
}

let is_connection (c:connection) (st:ST.state_ref) (s:S.conn_state) : slprop =
  exists* live.
    E.is_connection c.backend ** Box.pts_to c.live live ** ST.current st s

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
  let st = ST.alloc_initial ();
  let c = { backend; live };
  with backend_s. rewrite (E.is_connection backend) as (E.is_connection c.backend);
  with live_s. rewrite (Box.pts_to live live_s) as (Box.pts_to c.live live_s);
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
  let ok = E.client_connect c.backend ch;
  if ok {
    advance_successful_handshake 'st;
    fold (is_connection c 'st (hs_application_data 's));
    true
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
  unfold (is_connection c 'st 's);
  let written = E.client_write c.backend ch buf len;
  if (written = len) {
    ST.advance 'st (S.SendApplicationData (Ghost.reveal 'bytes)) (S.advance_write_record 's);
    fold (is_connection c 'st (S.advance_write_record 's));
    written
  } else {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    written
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
  let ok = E.client_write_all c.backend ch buf len;
  if ok {
    ST.advance 'st (S.SendApplicationData (Ghost.reveal 'bytes)) (S.advance_write_record 's);
    fold (is_connection c 'st (S.advance_write_record 's));
    true
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
  unfold (is_connection c 'st 's);
  let n = E.client_read c.backend ch out max_len;
  with bytes. assert (pts_to out bytes);
  if (n = 0sz) {
    ST.advance_fail 'st T.IoError;
    fold (is_connection c 'st (S.fail 's T.IoError));
    n
  } else {
    ST.advance 'st (S.RecvApplicationData bytes) (S.advance_read_record 's);
    fold (is_connection c 'st (S.advance_read_record 's));
    n
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
  let ok = E.client_read_exact c.backend ch out len;
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
