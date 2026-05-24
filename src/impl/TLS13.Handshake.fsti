module TLS13.Handshake

#lang-pulse

open Pulse.Lib.Pervasives

module H = TLS13.Handshake.Spec
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State
module T = TLS13.Types
module X = TLS13.X509.Spec

val handshake_context : Type0

val is_handshake_context: handshake_context -> ST.state_ref -> S.conn_state -> slprop

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
          pure ((ok ==> s'.S.phase == S.CertificateVerified) /\
                (not ok ==> s'.S.phase == S.Failed))

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
