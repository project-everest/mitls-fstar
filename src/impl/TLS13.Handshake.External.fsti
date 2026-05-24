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
  exists* p. BDE.is_context ctx p

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

fn store_client_hello
  (ctx: handshake_context)
  (hello: array U8.t)
  (hello_len: SZ.t)
  requires is_context ctx **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_len /\
                 SZ.v hello_len == 130)
  returns ok: bool
  ensures is_context ctx **
          pts_to hello 'hello_bytes

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

fn build_client_finished_record
  (ctx: handshake_context)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_context ctx **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 58)
  returns ok: bool
  ensures exists* out_bytes.
          is_context ctx **
          pts_to out out_bytes **
          pure (B.length out_bytes == 58)

fn process_server_hello_record
  (ctx: handshake_context)
  (header: array U8.t)
  (header_len: SZ.t)
  (fragment: array U8.t)
  (fragment_len: SZ.t)
  (key_share: array U8.t)
  (key_share_len: SZ.t)
  requires is_context ctx **
           pts_to header 'header_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to key_share 'key_share_bytes **
           pure (B.length 'header_bytes == SZ.v header_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'key_share_bytes == SZ.v key_share_len /\
                 SZ.v header_len == 5 /\
                 0 < SZ.v fragment_len /\
                 SZ.v fragment_len <= 4096 /\
                 SZ.v key_share_len == 32)
  returns ok: bool
  ensures is_context ctx **
          pts_to header 'header_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to key_share 'key_share_bytes

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
