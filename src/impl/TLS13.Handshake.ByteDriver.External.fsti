module TLS13.Handshake.ByteDriver.External

#lang-pulse

open Pulse.Lib.Pervasives

module IO = TLS13.IO
module U8 = FStar.UInt8

type progress =
  | ExpectEncryptedExtensions
  | ExpectCertificate
  | ExpectCertificateVerify
  | ExpectFinished
  | Complete

val context : Type0
val is_context: context -> progress -> slprop

fn reset_encrypted_handshake (ctx: context)
  requires is_context ctx 'p
  ensures is_context ctx ExpectEncryptedExtensions

fn read_next_encrypted_handshake_record (ctx: context) (ch: IO.channel)
  requires is_context ctx 'p ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx 'p ** IO.is_channel ch

fn pending_handshake_message_complete (ctx: context)
  requires is_context ctx 'p
  returns complete: bool
  ensures is_context ctx 'p

fn pending_handshake_message_type (ctx: context)
  requires is_context ctx 'p
  returns msg_type: U8.t
  ensures is_context ctx 'p

fn accept_encrypted_extensions (ctx: context)
  requires is_context ctx ExpectEncryptedExtensions
  returns ok: bool
  ensures is_context ctx (if ok then ExpectCertificate else ExpectEncryptedExtensions)

fn accept_certificate (ctx: context)
  requires is_context ctx ExpectCertificate
  returns ok: bool
  ensures is_context ctx (if ok then ExpectCertificateVerify else ExpectCertificate)

fn accept_certificate_verify (ctx: context)
  requires is_context ctx ExpectCertificateVerify
  returns ok: bool
  ensures is_context ctx (if ok then ExpectFinished else ExpectCertificateVerify)

fn accept_finished (ctx: context)
  requires is_context ctx ExpectFinished
  returns ok: bool
  ensures is_context ctx (if ok then Complete else ExpectFinished)

fn encrypted_handshake_complete (ctx: context)
  requires is_context ctx 'p
  returns done: bool
  ensures is_context ctx 'p **
          pure (done ==> 'p == Complete)
