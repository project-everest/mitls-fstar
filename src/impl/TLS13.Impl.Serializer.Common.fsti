module TLS13.Impl.Serializer.Common

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val byte : n:nat -> B.byte

val lemma_byte_reveal :
  n:nat ->
  Lemma (byte n == U8.uint_to_t (n % 256))

inline_for_extraction
val u8_of_sizet :
  n:SZ.t ->
  Tot (b:U8.t { U8.v b == SZ.v n % 256 })

val u8_of_sizet_v_byte :
  n:SZ.t ->
  Lemma (u8_of_sizet n == byte (SZ.v n))
    [SMTPat (u8_of_sizet n)]

val u8_of_sizet_div2_byte :
  n:SZ.t ->
  Lemma (u8_of_sizet (SZ.div (SZ.div n 256sz) 256sz) == byte (SZ.v n / 65536))

val write_u16_bytes : n:nat -> GTot B.bytes

val write_u24_bytes : n:nat -> GTot B.bytes

val lemma_write_u16_bytes_reveal :
  n:nat ->
  Lemma (Seq.equal (write_u16_bytes n) (B.of_list [byte (n / 256); byte n]))

val lemma_write_u24_bytes_reveal :
  n:nat ->
  Lemma (Seq.equal (write_u24_bytes n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))

val lemma_raw_slice_all :
  bytes:B.bytes ->
  Lemma (ensures Seq.equal (CL.raw_slice bytes 0 (B.length bytes)) bytes)

val lemma_slice_all :
  bytes:B.bytes ->
  Lemma (ensures Seq.equal (Seq.slice bytes 0 (B.length bytes)) bytes)

val lemma_raw_slice_empty :
  bytes:B.bytes ->
  i:nat{i <= B.length bytes} ->
  Lemma (ensures Seq.equal (CL.raw_slice bytes i i) B.empty)

val lemma_raw_slice_index :
  bytes:B.bytes ->
  lo:nat ->
  hi:nat ->
  i:nat ->
  Lemma
    (requires lo <= hi /\ hi <= B.length bytes /\ i < hi - lo)
    (ensures Seq.index (CL.raw_slice bytes lo hi) i ==
             Seq.index bytes (lo + i))

val lemma_copy_expr_preserves_prefix_slice :
  old:B.bytes ->
  src_part:B.bytes ->
  dst_off:nat ->
  copy_len:nat ->
  old_len:nat ->
  lo:nat ->
  hi:nat ->
  Lemma
    (requires B.length src_part == copy_len /\
              old_len == B.length old /\
              lo <= hi /\ hi <= dst_off /\
              dst_off + copy_len <= old_len)
    (ensures Seq.equal
      (CL.raw_slice
        (B.append
          (CL.raw_slice old 0 dst_off)
          (B.append
            src_part
            (CL.raw_slice old (dst_off + copy_len) old_len)))
        lo hi)
      (CL.raw_slice old lo hi))

val lemma_copy_expr_copied_slice :
  old:B.bytes ->
  src_part:B.bytes ->
  dst_off:nat ->
  copy_len:nat ->
  old_len:nat ->
  Lemma
    (requires B.length src_part == copy_len /\
              old_len == B.length old /\
              dst_off + copy_len <= old_len)
    (ensures Seq.equal
      (CL.raw_slice
        (B.append
          (CL.raw_slice old 0 dst_off)
          (B.append
            src_part
            (CL.raw_slice old (dst_off + copy_len) old_len)))
        dst_off (dst_off + copy_len))
      src_part)

val lemma_copy_expr_preserves_suffix_slice :
  old:B.bytes ->
  src_part:B.bytes ->
  dst_off:nat ->
  copy_len:nat ->
  old_len:nat ->
  lo:nat ->
  hi:nat ->
  Lemma
    (requires B.length src_part == copy_len /\
                   old_len == B.length old /\
                   dst_off + copy_len <= lo /\
                   lo <= hi /\ hi <= old_len)
    (ensures Seq.equal
      (CL.raw_slice
             (B.append
               (CL.raw_slice old 0 dst_off)
               (B.append
                 src_part
                 (CL.raw_slice old (dst_off + copy_len) old_len)))
             lo hi)
      (CL.raw_slice old lo hi))

fn write_u16 (out:array U8.t) (off:SZ.t) (n:SZ.t)
  requires pts_to out 'old **
           pure (B.length 'old == length out /\
                 SZ.v off + 2 <= B.length 'old)
  ensures exists* (out_bytes:B.bytes{B.length out_bytes == B.length 'old /\
                                     SZ.v off + 2 <= B.length out_bytes}).
          pts_to out out_bytes **
          pure (Seq.equal
                  (Seq.slice out_bytes (SZ.v off) (SZ.v off + 2))
                  (write_u16_bytes (SZ.v n)))

fn write_u24 (out:array U8.t) (off:SZ.t) (n:SZ.t)
  requires pts_to out 'old **
           pure (B.length 'old == length out /\
                 SZ.v off + 3 <= B.length 'old)
  ensures exists* (out_bytes:B.bytes{B.length out_bytes == B.length 'old /\
                                     SZ.v off + 3 <= B.length out_bytes}).
          pts_to out out_bytes **
          pure (Seq.equal
                  (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3))
                  (write_u24_bytes (SZ.v n)))

fn copy_array_slice_to_array
  (src:array U8.t)
  (src_total_len:SZ.t)
  (src_offset:SZ.t)
  (copy_len:SZ.t)
  (dst:array U8.t)
  (dst_len:SZ.t)
  (dst_offset:SZ.t)
  requires pts_to src 'src_bytes **
           pts_to dst 'dst_bytes **
           pure (B.length 'src_bytes == SZ.v src_total_len /\
                 B.length 'dst_bytes == SZ.v dst_len /\
                 SZ.v src_offset + SZ.v copy_len <= SZ.v src_total_len /\
                 SZ.v dst_offset + SZ.v copy_len <= SZ.v dst_len)
  ensures pts_to src 'src_bytes **
          pts_to dst
            (Seq.append
              (CL.raw_slice (Ghost.reveal 'dst_bytes) 0 (SZ.v dst_offset))
              (Seq.append
                (CL.raw_slice (Ghost.reveal 'src_bytes) (SZ.v src_offset) (SZ.v src_offset + SZ.v copy_len))
                (CL.raw_slice
                  (Ghost.reveal 'dst_bytes)
                  (SZ.v dst_offset + SZ.v copy_len)
                  (SZ.v dst_len))))
