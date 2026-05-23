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

fn decode_inner_plaintext_no_padding
  (inner: array U8.t)
  (inner_len: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  requires pts_to inner 'inner_bytes **
           pts_to content_type_out 'old_content_type **
           pure (B.length 'inner_bytes == SZ.v inner_len /\
                 B.length 'old_content_type == SZ.v content_type_out_len /\
                 SZ.v inner_len > 0 /\
                 SZ.v content_type_out_len == 1)
  returns payload_len: (p:SZ.t{SZ.v p + 1 == SZ.v inner_len})
  ensures exists* content_type_bytes.
          pts_to inner 'inner_bytes **
          pts_to content_type_out content_type_bytes **
          pure (B.length content_type_bytes == 1)
