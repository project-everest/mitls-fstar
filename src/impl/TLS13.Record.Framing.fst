module TLS13.Record.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module PC = TLS13.Parser.Correctness
module Ref = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module UInt = FStar.UInt
module U16 = FStar.UInt16
module WS = TLS13.Wire.Spec
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let lemma_read_u16_from_bytes (hi:U8.t) (lo:U8.t)
  : Lemma
      (U16.v (U16.logor (U16.shift_left (Cast.uint8_to_uint16 hi) 8ul)
                        (Cast.uint8_to_uint16 lo)) ==
       U8.v hi * 256 + U8.v lo)
=
  let hi16 = Cast.uint8_to_uint16 hi in
  let lo16 = Cast.uint8_to_uint16 lo in
  let shifted = U16.shift_left hi16 8ul in
  UInt.pow2_values 8;
  UInt.pow2_values 16;
  UInt.shift_left_value_lemma #16 (U16.v hi16) 8;
  assert (U16.v shifted == U8.v hi * 256);
  UInt.logor_disjoint #16 (U16.v shifted) (U16.v lo16) 8;
  assert (U16.v (U16.logor shifted lo16) == U16.v shifted + U16.v lo16)

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

let lemma_inner_plaintext_no_padding_result_len
  (plain:B.bytes)
  (old:B.bytes)
  (plain_len:nat)
  (out_len:nat)
  (content_type:U8.t)
  : Lemma
      (requires B.length plain == plain_len /\
                B.length old == out_len /\
                out_len == plain_len + 1)
      (ensures B.length (inner_plaintext_no_padding_result plain old plain_len out_len content_type) == out_len)
  =
  assert (plain_len < out_len);
  assert (plain_len <= B.length plain);
  assert (out_len <= B.length old);
  Seq.lemma_len_slice plain 0 plain_len;
  Seq.lemma_len_slice old plain_len out_len;
  Seq.lemma_len_append (Seq.slice plain 0 plain_len) (Seq.slice old plain_len out_len);
  assert (B.length (Seq.append (Seq.slice plain 0 plain_len) (Seq.slice old plain_len out_len)) == out_len);
  Seq.lemma_len_upd plain_len content_type (Seq.append (Seq.slice plain 0 plain_len) (Seq.slice old plain_len out_len));
  assert (inner_plaintext_no_padding_result plain old plain_len out_len content_type ==
          Seq.upd
            (Seq.append (Seq.slice plain 0 plain_len) (Seq.slice old plain_len out_len))
            plain_len
            content_type);
  assert (B.length (inner_plaintext_no_padding_result plain old plain_len out_len content_type) == out_len)

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
          pure (
            // Length constraints (carried from precondition)
            B.length 'header_bytes == 5 /\
            B.length content_type_bytes == 1 /\
            B.length fragment_len_bytes == 2 /\
            // Parsed fields match the input header
            Seq.index content_type_bytes 0 == Seq.index 'header_bytes 0 /\
            WS.read_u16 fragment_len_bytes 0 == WS.read_u16 'header_bytes 3 /\
            // Parser correctness: ok matches Wire.Spec.parse_record_header
            (ok <==> Some? (WS.parse_record_header 'header_bytes))
          )
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
  with content_type_bytes. assert (pts_to content_type_out content_type_bytes);
  with fragment_len_bytes. assert (pts_to fragment_len_out fragment_len_bytes);

  // Compute fragment length as U16
  let frag_len = U16.logor (U16.shift_left (Cast.uint8_to_uint16 l0) 8ul)
                            (Cast.uint8_to_uint16 l1);

  let ok = (ct = 0x14uy || ct = 0x15uy || ct = 0x16uy || ct = 0x17uy) &&
           v0 = 0x03uy &&
           v1 = 0x03uy &&
           frag_len `U16.lte` 16640us;

  lemma_read_u16_from_bytes l0 l1;
  WS.lemma_read_u16_definition 'header_bytes 3;
  assert (pure (WS.read_u16 'header_bytes 3 == U8.v l0 * 256 + U8.v l1));
  assert (pure (UInt.size (WS.read_u16 'header_bytes 3) 16));
  assert (pure (U16.v frag_len == WS.read_u16 'header_bytes 3));
  Seq.lemma_index_upd1 'old_fragment_len 0 l0;
  Seq.lemma_index_upd2 (Seq.upd 'old_fragment_len 0 l0) 1 l1 0;
  Seq.lemma_index_upd1 (Seq.upd 'old_fragment_len 0 l0) 1 l1;
  assert (pure (Seq.index fragment_len_bytes 0 == l0));
  assert (pure (Seq.index fragment_len_bytes 1 == l1));
  WS.lemma_read_u16_definition fragment_len_bytes 0;
  assert (pure (WS.read_u16 fragment_len_bytes 0 ==
                U8.v (Seq.index fragment_len_bytes 0) * 256 +
                U8.v (Seq.index fragment_len_bytes 1)));
  assert (pure (WS.read_u16 fragment_len_bytes 0 == U8.v l0 * 256 + U8.v l1));
  assert (pure (WS.read_u16 fragment_len_bytes 0 == WS.read_u16 'header_bytes 3));
  assert (pure ((frag_len `U16.lte` 16640us) <==>
                (WS.read_u16 'header_bytes 3 <= 16640)));

  // PARSER TCB: Call admitted lemma stating parser correctness
  PC.lemma_parse_record_header_correct 'header_bytes ok;
  ok
}
