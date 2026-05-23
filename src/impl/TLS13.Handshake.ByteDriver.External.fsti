module TLS13.Handshake.ByteDriver.External

#lang-pulse

open Pulse.Lib.Pervasives

module IO = TLS13.IO
module U8 = FStar.UInt8

val context : Type0
val is_context: context -> slprop

fn reset_encrypted_handshake (ctx: context)
  requires is_context ctx
  ensures is_context ctx

fn read_next_encrypted_handshake_record (ctx: context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn pending_handshake_message_complete (ctx: context)
  requires is_context ctx
  returns complete: bool
  ensures is_context ctx

fn pending_handshake_message_type (ctx: context)
  requires is_context ctx
  returns msg_type: U8.t
  ensures is_context ctx

fn accept_encrypted_extensions (ctx: context)
  requires is_context ctx
  returns ok: bool
  ensures is_context ctx

fn accept_certificate (ctx: context)
  requires is_context ctx
  returns ok: bool
  ensures is_context ctx

fn accept_certificate_verify (ctx: context)
  requires is_context ctx
  returns ok: bool
  ensures is_context ctx

fn accept_finished (ctx: context)
  requires is_context ctx
  returns ok: bool
  ensures is_context ctx

fn encrypted_handshake_complete (ctx: context)
  requires is_context ctx
  returns done: bool
  ensures is_context ctx
