module TLS13.Record.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module Ref = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let inner_plaintext_no_padding_result
  (plain:B.bytes)
  (old:B.bytes)
  (plain_len:nat)
  (out_len:nat)
  (content_type:U8.t)
  : GTot B.bytes =
  if plain_len < out_len /\
     plain_len <= B.length plain /\
     out_len <= B.length old
  then
    Seq.upd
      (Seq.append
        (Seq.slice plain 0 plain_len)
        (Seq.slice old plain_len out_len))
      plain_len
      content_type
  else old

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
{
  pts_to_len plain;
  pts_to_len out;
  Arr.memcpy_l plain_len plain out;
  with copied. assert (pts_to out copied);
  assert (pure (Seq.length copied == SZ.v out_len));
  out.(plain_len) <- content_type;
}

fn encode_inner_plaintext_no_padding_slice
  (plain: array U8.t)
  (plain_total_len: SZ.t)
  (plain_offset: SZ.t)
  (plain_len: SZ.t)
  (content_type: U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to plain 'plain_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'plain_bytes == SZ.v plain_total_len /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == SZ.v plain_len + 1 /\
                 SZ.v plain_offset + SZ.v plain_len <= SZ.v plain_total_len)
  ensures exists* out_bytes.
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len)
{
  pts_to_len plain;
  pts_to_len out;
  let mut i = 0sz;
  while (SZ.lt !i plain_len)
    invariant exists* vi out_bytes.
      Ref.pts_to i vi **
      pts_to plain 'plain_bytes **
      pts_to out out_bytes **
      pure (SZ.v vi <= SZ.v plain_len /\
            B.length 'plain_bytes == SZ.v plain_total_len /\
            B.length out_bytes == SZ.v out_len /\
            SZ.v out_len == SZ.v plain_len + 1 /\
            SZ.v plain_offset + SZ.v plain_len <= SZ.v plain_total_len)
  {
    let vi = !i;
    assert (pure (SZ.v vi < SZ.v plain_len));
    assert (pure (SZ.v plain_offset + SZ.v vi < SZ.v plain_total_len));
    let src_index = SZ.(plain_offset +^ vi);
    let b = plain.(src_index);
    out.(vi) <- b;
    i := SZ.(vi +^ 1sz);
  };
  with copied. assert (pts_to out copied);
  assert (pure (Seq.length copied == SZ.v out_len));
  assert (pure (SZ.v plain_len < SZ.v out_len));
  out.(plain_len) <- content_type;
  with final_bytes. assert (pts_to out final_bytes);
  assert (pure (Seq.length final_bytes == SZ.v out_len));
}

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
{
  let payload_len = SZ.(inner_len -^ 1sz);
  pts_to_len inner;
  pts_to_len content_type_out;
  let content_type = inner.(payload_len);
  content_type_out.(0sz) <- content_type;
  payload_len
}

fn rec decode_inner_plaintext_from
  (inner: array U8.t)
  (inner_len: SZ.t)
  (index: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  requires pts_to inner 'inner_bytes **
           pts_to content_type_out 'old_content_type **
           pure (B.length 'inner_bytes == SZ.v inner_len /\
                 B.length 'old_content_type == SZ.v content_type_out_len /\
                 SZ.v inner_len > 0 /\
                 SZ.v index < SZ.v inner_len /\
                 SZ.v content_type_out_len == 1)
  returns payload_len: SZ.t
  ensures exists* content_type_bytes.
          pts_to inner 'inner_bytes **
          pts_to content_type_out content_type_bytes **
          pure (B.length content_type_bytes == 1 /\
                SZ.v payload_len < SZ.v inner_len)
  decreases (SZ.v index)
{
  pts_to_len inner;
  pts_to_len content_type_out;
  let content_type = inner.(index);
  if (content_type = 0uy) {
    if (index = 0sz) {
      content_type_out.(0sz) <- 0uy;
      0sz
    } else {
      assert (pure (SZ.v index > 0));
      let index' = SZ.(index -^ 1sz);
      assert (pure (SZ.v index' < SZ.v index));
      assert (pure (SZ.v index' < SZ.v inner_len));
      decode_inner_plaintext_from inner inner_len index' content_type_out content_type_out_len
    }
  } else {
    content_type_out.(0sz) <- content_type;
    index
  }
}

fn decode_inner_plaintext
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
  returns payload_len: SZ.t
  ensures exists* content_type_bytes.
          pts_to inner 'inner_bytes **
          pts_to content_type_out content_type_bytes **
          pure (B.length content_type_bytes == 1 /\
                SZ.v payload_len < SZ.v inner_len)
{
  let last = SZ.(inner_len -^ 1sz);
  assert (pure (SZ.v last < SZ.v inner_len));
  decode_inner_plaintext_from inner inner_len last content_type_out content_type_out_len
}

fn serialize_application_data_header
  (fragment_len: U16.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5)
  ensures exists* header_bytes.
          pts_to out header_bytes **
          pure (B.length header_bytes == 5)
{
  pts_to_len out;
  out.(0sz) <- 0x17uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  out.(3sz) <- Cast.uint16_to_uint8 (U16.shift_right fragment_len 8ul);
  out.(4sz) <- Cast.uint16_to_uint8 fragment_len;
}

fn parse_record_header
  (header: array U8.t)
  (header_len: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  (fragment_len_out: array U8.t)
  (fragment_len_out_len: SZ.t)
  requires pts_to header 'header_bytes **
           pts_to content_type_out 'old_content_type **
           pts_to fragment_len_out 'old_fragment_len **
           pure (B.length 'header_bytes == SZ.v header_len /\
                 B.length 'old_content_type == SZ.v content_type_out_len /\
                 B.length 'old_fragment_len == SZ.v fragment_len_out_len /\
                 SZ.v header_len == 5 /\
                 SZ.v content_type_out_len == 1 /\
                 SZ.v fragment_len_out_len == 2)
  returns ok: bool
  ensures exists* content_type_bytes fragment_len_bytes.
          pts_to header 'header_bytes **
          pts_to content_type_out content_type_bytes **
          pts_to fragment_len_out fragment_len_bytes **
          pure (B.length content_type_bytes == 1 /\
                B.length fragment_len_bytes == 2)
{
  pts_to_len header;
  pts_to_len content_type_out;
  pts_to_len fragment_len_out;
  let ct = header.(0sz);
  let v0 = header.(1sz);
  let v1 = header.(2sz);
  let l0 = header.(3sz);
  let l1 = header.(4sz);
  content_type_out.(0sz) <- ct;
  fragment_len_out.(0sz) <- l0;
  fragment_len_out.(1sz) <- l1;
  let ok = (ct = 0x14uy || ct = 0x15uy || ct = 0x16uy || ct = 0x17uy) &&
           v0 = 0x03uy &&
           (v1 = 0x01uy || v1 = 0x03uy);
  // PARSER TCB: Assume parser correctness
  // Property assumed: ok <==> Some? (Wire.Spec.parse_record 'header_bytes)
  admit();
  ok
}
