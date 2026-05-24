module TLS13.Handshake.ByteDriver.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module IO = TLS13.IO
module SZ = FStar.SizeT
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

fn read_raw (ctx: context) (ch: IO.channel) (buf: array U8.t)
  (total_len: SZ.t) (offset: SZ.t) (remaining: SZ.t)
  requires is_context ctx 'p ** IO.is_channel ch
           ** pts_to buf 'old
           ** pure (B.length 'old == SZ.v total_len /\
                    SZ.v remaining > 0 /\
                    SZ.v offset + SZ.v remaining <= SZ.v total_len)
  returns n: SZ.t
  ensures exists* bytes.
          is_context ctx 'p ** IO.is_channel ch
          ** pts_to buf bytes
          ** pure (B.length bytes == SZ.v total_len /\
                   SZ.v n <= SZ.v remaining)

fn process_encrypted_handshake_record
  (ctx: context)
  (header: array U8.t)
  (header_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  requires is_context ctx 'p **
           pts_to header 'header_bytes **
           pts_to cipher 'cipher_bytes **
           pure (B.length 'header_bytes == SZ.v header_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 SZ.v header_len == 5 /\
                 SZ.v cipher_len > 16)
  returns ok: bool
  ensures is_context ctx 'p **
          pts_to header 'header_bytes **
          pts_to cipher 'cipher_bytes

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
