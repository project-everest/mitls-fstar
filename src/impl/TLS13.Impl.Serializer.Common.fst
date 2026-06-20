module TLS13.Impl.Serializer.Common

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast

noextract
let byte (n:nat) : B.byte =
  U8.uint_to_t (n % 256)

let lemma_byte_reveal (n:nat)
  : Lemma (byte n == U8.uint_to_t (n % 256))
=
  ()

inline_for_extraction
let u8_of_sizet (n:SZ.t) : Tot (b:U8.t { U8.v b == SZ.v n % 256 }) =
  let r = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 n) in
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 8 * pow2 24 == pow2 32);
  FStar.Math.Lemmas.modulo_modulo_lemma (SZ.v n) (pow2 8) (pow2 24);
  r

let u8_of_sizet_v_byte (n:SZ.t)
  : Lemma (u8_of_sizet n == byte (SZ.v n))
          [SMTPat (u8_of_sizet n)]
  = ()

let u8_of_sizet_div2_byte (n:SZ.t)
  : Lemma (u8_of_sizet (SZ.div (SZ.div n 256sz) 256sz) == byte (SZ.v n / 65536))
  = FStar.Math.Lemmas.division_multiplication_lemma (SZ.v n) 256 256

let write_u16_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 256); byte n]

let write_u24_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 65536); byte (n / 256); byte n]

let lemma_write_u16_bytes_reveal (n:nat)
  : Lemma (Seq.equal (write_u16_bytes n) (B.of_list [byte (n / 256); byte n]))
=
  ()

let lemma_write_u24_bytes_reveal (n:nat)
  : Lemma (Seq.equal (write_u24_bytes n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))
=
  ()

let lemma_raw_slice_all (bytes:B.bytes)
  : Lemma (ensures Seq.equal (CL.raw_slice bytes 0 (B.length bytes)) bytes)
=
  Seq.lemma_len_slice bytes 0 (B.length bytes);
  assert (forall (i:nat{i < B.length bytes}).
    Seq.index (CL.raw_slice bytes 0 (B.length bytes)) i == Seq.index bytes i);
  Seq.lemma_eq_intro (CL.raw_slice bytes 0 (B.length bytes)) bytes

let lemma_slice_all (bytes:B.bytes)
  : Lemma (ensures Seq.equal (Seq.slice bytes 0 (B.length bytes)) bytes)
=
  Seq.lemma_len_slice bytes 0 (B.length bytes);
  assert (forall (i:nat{i < B.length bytes}).
    Seq.index (Seq.slice bytes 0 (B.length bytes)) i == Seq.index bytes i);
  Seq.lemma_eq_intro (Seq.slice bytes 0 (B.length bytes)) bytes

let lemma_raw_slice_empty (bytes:B.bytes) (i:nat{i <= B.length bytes})
  : Lemma (ensures Seq.equal (CL.raw_slice bytes i i) B.empty)
=
  Seq.lemma_len_slice bytes i i;
  Seq.lemma_eq_intro (CL.raw_slice bytes i i) B.empty

let lemma_raw_slice_index
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat)
  (i:nat)
  : Lemma
      (requires lo <= hi /\ hi <= B.length bytes /\ i < hi - lo)
      (ensures Seq.index (CL.raw_slice bytes lo hi) i ==
               Seq.index bytes (lo + i))
=
  assert (CL.raw_slice bytes lo hi == Seq.slice bytes lo hi);
  Seq.lemma_len_slice bytes lo hi;
  assert (Seq.index (Seq.slice bytes lo hi) i == Seq.index bytes (lo + i))

let lemma_copy_expr_preserves_suffix_index
  (old:B.bytes)
  (src_part:B.bytes)
  (dst_off:nat)
  (copy_len:nat)
  (old_len:nat)
  (k:nat)
  : Lemma
      (requires B.length src_part == copy_len /\
                old_len == B.length old /\
                dst_off + copy_len <= k /\
                k < old_len)
      (ensures
        Seq.index
          (B.append
            (CL.raw_slice old 0 dst_off)
            (B.append
              src_part
              (CL.raw_slice old (dst_off + copy_len) old_len)))
          k ==
        Seq.index old k)
=
  let prefix = CL.raw_slice old 0 dst_off in
  let suffix = CL.raw_slice old (dst_off + copy_len) old_len in
  let tail = B.append src_part suffix in
  let full = B.append prefix tail in
  assert (prefix == Seq.slice old 0 dst_off);
  Seq.lemma_len_slice old 0 dst_off;
  assert (B.length prefix == dst_off);
  assert (suffix == Seq.slice old (dst_off + copy_len) old_len);
  Seq.lemma_len_slice old (dst_off + copy_len) old_len;
  assert (B.length suffix == old_len - (dst_off + copy_len));
  Seq.lemma_len_append src_part suffix;
  assert (B.length tail == copy_len + B.length suffix);
  Seq.lemma_len_append prefix tail;
  assert (B.length full == old_len);
  assert (B.length prefix <= k);
  Seq.lemma_index_app2 prefix tail k;
  let k_tail = k - B.length prefix in
  assert (k_tail == k - dst_off);
  assert (B.length src_part <= k_tail);
  assert (k_tail < B.length tail);
  Seq.lemma_index_app2 src_part suffix k_tail;
  let k_suffix = k_tail - B.length src_part in
  assert (k_suffix == k - (dst_off + copy_len));
  assert (k_suffix < B.length suffix);
  assert (Seq.index suffix k_suffix == Seq.index old k)

let lemma_copy_expr_preserves_prefix_index
  (old:B.bytes)
  (src_part:B.bytes)
  (dst_off:nat)
  (copy_len:nat)
  (old_len:nat)
  (k:nat)
  : Lemma
      (requires B.length src_part == copy_len /\
                old_len == B.length old /\
                k < dst_off /\
                dst_off + copy_len <= old_len)
      (ensures
        Seq.index
          (B.append
            (CL.raw_slice old 0 dst_off)
            (B.append
              src_part
              (CL.raw_slice old (dst_off + copy_len) old_len)))
          k ==
        Seq.index old k)
=
  let prefix = CL.raw_slice old 0 dst_off in
  let suffix = CL.raw_slice old (dst_off + copy_len) old_len in
  let tail = B.append src_part suffix in
  assert (prefix == Seq.slice old 0 dst_off);
  Seq.lemma_len_slice old 0 dst_off;
  assert (B.length prefix == dst_off);
  assert (suffix == Seq.slice old (dst_off + copy_len) old_len);
  Seq.lemma_len_slice old (dst_off + copy_len) old_len;
  Seq.lemma_len_append src_part suffix;
  Seq.lemma_len_append prefix tail;
  Seq.lemma_index_app1 prefix tail k;
  assert (Seq.index prefix k == Seq.index old k)

let lemma_copy_expr_preserves_prefix_slice
  (old:B.bytes)
  (src_part:B.bytes)
  (dst_off:nat)
  (copy_len:nat)
  (old_len:nat)
  (lo:nat)
  (hi:nat)
  : Lemma
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
=
  let copied =
    B.append
      (CL.raw_slice old 0 dst_off)
      (B.append src_part (CL.raw_slice old (dst_off + copy_len) old_len)) in
  Seq.lemma_len_slice old 0 dst_off;
  Seq.lemma_len_slice old (dst_off + copy_len) old_len;
  Seq.lemma_len_append src_part (CL.raw_slice old (dst_off + copy_len) old_len);
  Seq.lemma_len_append (CL.raw_slice old 0 dst_off)
    (B.append src_part (CL.raw_slice old (dst_off + copy_len) old_len));
  assert (B.length copied == old_len);
  Seq.lemma_len_slice copied lo hi;
  Seq.lemma_len_slice old lo hi;
  introduce forall (i:nat).
    i < hi - lo ==>
    Seq.index (CL.raw_slice copied lo hi) i ==
    Seq.index (CL.raw_slice old lo hi) i
  with introduce _ ==> _
  with _. (
    lemma_raw_slice_index copied lo hi i;
    lemma_raw_slice_index old lo hi i;
    lemma_copy_expr_preserves_prefix_index old src_part dst_off copy_len old_len (lo + i)
  );
  Seq.lemma_eq_intro (CL.raw_slice copied lo hi) (CL.raw_slice old lo hi)

let lemma_copy_expr_copied_slice
  (old:B.bytes)
  (src_part:B.bytes)
  (dst_off:nat)
  (copy_len:nat)
  (old_len:nat)
  : Lemma
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
=
  let copied =
    B.append
      (CL.raw_slice old 0 dst_off)
      (B.append src_part (CL.raw_slice old (dst_off + copy_len) old_len)) in
  let suffix = CL.raw_slice old (dst_off + copy_len) old_len in
  let tail = B.append src_part suffix in
  Seq.lemma_len_slice old 0 dst_off;
  Seq.lemma_len_slice old (dst_off + copy_len) old_len;
  Seq.lemma_len_append src_part suffix;
  Seq.lemma_len_append (CL.raw_slice old 0 dst_off) tail;
  assert (B.length copied == old_len);
  Seq.lemma_len_slice copied dst_off (dst_off + copy_len);
  introduce forall (i:nat).
    i < copy_len ==>
    Seq.index (CL.raw_slice copied dst_off (dst_off + copy_len)) i ==
    Seq.index src_part i
  with introduce _ ==> _
  with _. (
    lemma_raw_slice_index copied dst_off (dst_off + copy_len) i;
    Seq.lemma_index_app2 (CL.raw_slice old 0 dst_off) tail (dst_off + i);
    assert ((dst_off + i) - B.length (CL.raw_slice old 0 dst_off) == i);
    Seq.lemma_index_app1 src_part suffix i
  );
  Seq.lemma_eq_intro (CL.raw_slice copied dst_off (dst_off + copy_len)) src_part

let lemma_copy_expr_preserves_suffix_slice
  (old:B.bytes)
  (src_part:B.bytes)
  (dst_off:nat)
  (copy_len:nat)
  (old_len:nat)
  (lo:nat)
  (hi:nat)
  : Lemma
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
=
  let copied =
    B.append
      (CL.raw_slice old 0 dst_off)
      (B.append src_part (CL.raw_slice old (dst_off + copy_len) old_len)) in
  Seq.lemma_len_slice old 0 dst_off;
  Seq.lemma_len_slice old (dst_off + copy_len) old_len;
  Seq.lemma_len_append src_part (CL.raw_slice old (dst_off + copy_len) old_len);
  Seq.lemma_len_append (CL.raw_slice old 0 dst_off)
    (B.append src_part (CL.raw_slice old (dst_off + copy_len) old_len));
  assert (B.length copied == old_len);
  Seq.lemma_len_slice copied lo hi;
  Seq.lemma_len_slice old lo hi;
  introduce forall (i:nat).
    i < hi - lo ==>
    Seq.index (CL.raw_slice copied lo hi) i ==
    Seq.index (CL.raw_slice old lo hi) i
  with introduce _ ==> _
  with _. (
    lemma_raw_slice_index copied lo hi i;
    lemma_raw_slice_index old lo hi i;
    lemma_copy_expr_preserves_suffix_index old src_part dst_off copy_len old_len (lo + i)
  );
  Seq.lemma_eq_intro (CL.raw_slice copied lo hi) (CL.raw_slice old lo hi)

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
{
  out.(off) <- u8_of_sizet (SZ.div n 256sz);
  let off1 = SZ.add off 1sz;
  out.(off1) <- u8_of_sizet n;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == B.length 'old));
  assert (pure (Seq.length (write_u16_bytes (SZ.v n)) == 2));
  assert_norm (Seq.index (write_u16_bytes (SZ.v n)) 0 == byte (SZ.v n / 256));
  assert_norm (Seq.index (write_u16_bytes (SZ.v n)) 1 == byte (SZ.v n));
  assert (pure (Seq.length (Seq.slice out_bytes (SZ.v off) (SZ.v off + 2)) == 2));
  assert (pure (Seq.index (Seq.slice out_bytes (SZ.v off) (SZ.v off + 2)) 0 == byte (SZ.v n / 256)));
  assert (pure (Seq.index (Seq.slice out_bytes (SZ.v off) (SZ.v off + 2)) 1 == byte (SZ.v n)));
  Seq.lemma_eq_intro
    (Seq.slice out_bytes (SZ.v off) (SZ.v off + 2))
    (write_u16_bytes (SZ.v n));
}

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
{
  u8_of_sizet_div2_byte n;
  out.(off) <- u8_of_sizet (SZ.div (SZ.div n 256sz) 256sz);
  let off1 = SZ.add off 1sz;
  out.(off1) <- u8_of_sizet (SZ.div n 256sz);
  let off2 = SZ.add off 2sz;
  out.(off2) <- u8_of_sizet n;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == B.length 'old));
  assert (pure (Seq.length (write_u24_bytes (SZ.v n)) == 3));
  assert_norm (Seq.index (write_u24_bytes (SZ.v n)) 0 == byte (SZ.v n / 65536));
  assert_norm (Seq.index (write_u24_bytes (SZ.v n)) 1 == byte (SZ.v n / 256));
  assert_norm (Seq.index (write_u24_bytes (SZ.v n)) 2 == byte (SZ.v n));
  assert (pure (Seq.length (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3)) == 3));
  assert (pure (Seq.index (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3)) 0 == byte (SZ.v n / 65536)));
  assert (pure (Seq.index (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3)) 1 == byte (SZ.v n / 256)));
  assert (pure (Seq.index (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3)) 2 == byte (SZ.v n)));
  Seq.lemma_eq_intro
    (Seq.slice out_bytes (SZ.v off) (SZ.v off + 3))
    (write_u24_bytes (SZ.v n));
}

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
{
  pts_to_len src;
  pts_to_len dst;
  let src_slice = Slice.from_array src src_total_len;
  let dst_slice = Slice.from_array dst dst_len;
  let src_split = Slice.split src_slice src_offset;
  let src_copy_split = Slice.split (snd src_split) copy_len;
  let dst_split = Slice.split dst_slice dst_offset;
  let dst_copy_split = Slice.split (snd dst_split) copy_len;
  Slice.pts_to_len (fst src_copy_split);
  Slice.pts_to_len (fst dst_copy_split);
  assert (pure (Slice.len (fst src_copy_split) == copy_len));
  assert (pure (Slice.len (fst dst_copy_split) == copy_len));
  Slice.copy (fst dst_copy_split) (fst src_copy_split);
  Slice.join (fst src_copy_split) (snd src_copy_split) (snd src_split);
  Slice.join (fst src_split) (snd src_split) src_slice;
  SeqP.lemma_split (Ghost.reveal 'src_bytes) (SZ.v src_offset);
  SeqP.lemma_split
    (Seq.slice (Ghost.reveal 'src_bytes) (SZ.v src_offset) (B.length (Ghost.reveal 'src_bytes)))
    (SZ.v copy_len);
  Slice.to_array src_slice;
  Slice.join (fst dst_copy_split) (snd dst_copy_split) (snd dst_split);
  Slice.join (fst dst_split) (snd dst_split) dst_slice;
  Slice.to_array dst_slice
}
