module TLS13.Handshake.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BDE = TLS13.Handshake.ByteDriver.External
module IO = TLS13.IO
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type handshake_context = BDE.context
let is_context (ctx:handshake_context) : slprop =
  BDE.is_context ctx

fn context_new ()
  returns ctx: handshake_context
  ensures is_context ctx

fn context_free (ctx: handshake_context)
  requires is_context ctx
  ensures emp

fn connect (ctx: handshake_context) (ch: IO.channel)
  requires is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures is_context ctx ** IO.is_channel ch

fn read_raw (ctx: handshake_context) (ch: IO.channel) (buf: array U8.t)
  (total_len: SZ.t) (offset: SZ.t) (remaining: SZ.t)
  requires is_context ctx ** IO.is_channel ch
           ** pts_to buf 'old
           ** pure (B.length 'old == SZ.v total_len /\
                    SZ.v remaining > 0 /\
                    SZ.v offset + SZ.v remaining <= SZ.v total_len)
  returns n: SZ.t
  ensures exists* bytes.
          is_context ctx ** IO.is_channel ch
          ** pts_to buf bytes
          ** pure (B.length bytes == SZ.v total_len /\
                   SZ.v n <= SZ.v remaining)

fn write_raw (ctx: handshake_context) (ch: IO.channel) (buf: array U8.t)
  (total_len: SZ.t) (offset: SZ.t) (remaining: SZ.t)
  requires is_context ctx ** IO.is_channel ch
           ** pts_to buf 'bytes
           ** pure (B.length 'bytes == SZ.v total_len /\
                    SZ.v remaining > 0 /\
                    SZ.v offset + SZ.v remaining <= SZ.v total_len)
  returns n: SZ.t
  ensures is_context ctx ** IO.is_channel ch
          ** pts_to buf 'bytes
          ** pure (SZ.v n <= SZ.v remaining)
