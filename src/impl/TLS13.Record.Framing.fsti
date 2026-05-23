module TLS13.Record.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val inner_plaintext_no_padding_result:
  plain:B.bytes ->
  old:B.bytes ->
  plain_len:nat ->
  out_len:nat ->
  content_type:U8.t ->
  GTot B.bytes

fn encode_inner_plaintext_no_padding
  (plain: array U8.t)
  (plain_len: SZ.t)
  (content_type: U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to plain 'plain_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == SZ.v plain_len + 1)
  ensures pts_to plain 'plain_bytes **
          pts_to out (inner_plaintext_no_padding_result
                        (Ghost.reveal 'plain_bytes)
                        (Ghost.reveal 'old_bytes)
                        (SZ.v plain_len)
                        (SZ.v out_len)
                        content_type)
