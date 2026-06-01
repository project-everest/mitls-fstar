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
