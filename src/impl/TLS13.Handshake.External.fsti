module TLS13.Handshake.External

#lang-pulse

open Pulse.Lib.Pervasives

module IO = TLS13.IO

val handshake_context : Type0
val is_context: handshake_context -> slprop

fn context_new ()
  returns ctx: handshake_context
  ensures is_context ctx

fn context_free (ctx: handshake_context)
  requires is_context ctx
  ensures emp

fn send_client_hello (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  ensures is_context ctx ** IO.is_channel ch

fn recv_server_hello (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn recv_encrypted_extensions (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn recv_certificate (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn validate_certificate (ctx: handshake_context)
  requires is_context ctx
  returns ok: bool
  ensures is_context ctx

fn recv_certificate_verify (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn recv_server_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn send_client_finished (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch
