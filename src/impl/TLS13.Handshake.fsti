module TLS13.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module FS = TLS13.Handshake.FlightState
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

val handshake_context : Type0

val is_handshake_context: handshake_context -> ST.state_ref -> S.conn_state -> slprop
val handshake_context_exactly: handshake_context -> ST.state_ref -> S.conn_state -> FS.flight_view -> slprop

ghost
fn reveal_handshake_flight_view (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's
  ensures exists* flight_view. handshake_context_exactly ctx 'st 's flight_view

ghost
fn hide_handshake_flight_view (ctx: handshake_context)
  requires handshake_context_exactly ctx 'st 's 'flight_view
  ensures is_handshake_context ctx 'st 's

fn handshake_context_new ()
  returns ctx: handshake_context
  ensures exists* st. is_handshake_context ctx st S.initial

fn handshake_context_free (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's
  ensures emp

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

fn validate_certificate (ctx: handshake_context)
  requires is_handshake_context ctx 'st 's **
           pure ('s.S.phase == S.CertificateReceived)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          pure ((ok ==> s'.S.phase == S.CertificateValidated /\ Some? s'.S.peer) /\
                (not ok ==> s'.S.phase == S.Failed))

fn recv_certificate_verify (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.CertificateValidated /\ Some? 's.S.peer)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.CertificateVerified /\
                        s'.S.peer == 's.S.peer) /\
               (not ok ==> s'.S.phase == S.Failed))

fn recv_server_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.CertificateVerified /\ Some? 's.S.peer)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ServerFinishedVerified /\
                        s'.S.peer == 's.S.peer) /\
               (not ok ==> s'.S.phase == S.Failed))

fn send_client_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ServerFinishedVerified /\ Some? 's.S.peer)
  returns ok: bool
  ensures exists* s'.
          is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ApplicationData /\
                        s'.S.peer == 's.S.peer) /\
               (not ok ==> s'.S.phase == S.Failed))

fn derive_application_keys
  (ctx: handshake_context)
  (client_key: array U8.t)
  (client_iv: array U8.t)
  (server_key: array U8.t)
  (server_iv: array U8.t)
  requires is_handshake_context ctx 'st 's **
          pts_to client_key 'old_client_key **
          pts_to client_iv 'old_client_iv **
          pts_to server_key 'old_server_key **
          pts_to server_iv 'old_server_iv **
          pure ('s.S.phase == S.ApplicationData /\
                B.length 'old_client_key == 32 /\
                B.length 'old_client_iv == 12 /\
                B.length 'old_server_key == 32 /\
                B.length 'old_server_iv == 12)
  returns ok: bool
  ensures exists* client_key_bytes client_iv_bytes server_key_bytes server_iv_bytes.
          is_handshake_context ctx 'st 's **
          pts_to client_key client_key_bytes **
          pts_to client_iv client_iv_bytes **
          pts_to server_key server_key_bytes **
          pts_to server_iv server_iv_bytes **
          pure (B.length client_key_bytes == 32 /\
               B.length client_iv_bytes == 12 /\
               B.length server_key_bytes == 32 /\
               B.length server_iv_bytes == 12)
