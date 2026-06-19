module TLS13.Impl.Serializer

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Classical = FStar.Classical
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ref = Pulse.Lib.Reference
module SerCV = TLS13.Impl.Serializer.CertificateVerify
module SerCert = TLS13.Impl.Serializer.Certificate
module SerEE = TLS13.Impl.Serializer.EncryptedExtensions
module SerFin = TLS13.Impl.Serializer.Finished
module SerPR = TLS13.Impl.Serializer.ProtectedRecord
module SerSH = TLS13.Impl.Serializer.ServerHello
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal
module WSRD = TLS13.Wire.Spec.RevealDecode

let byte (n:nat) : B.byte =
  U8.uint_to_t (n % 256)

(* Machine-native low byte of a [SZ.t]: extract [n mod 256] entirely in machine
   integers (sizet -> uint32 -> uint8), with no detour through the mathematical
   [SZ.v n] view.  This keeps the extracted C free of [FStar_SizeT_v] /
   [Prims_op_Division] / [Prims_op_Modulus] at the wire-length byte-split sites:
   it lowers to a couple of [size_t]->[uint32_t]->[uint8_t] casts. *)
inline_for_extraction
let u8_of_sizet (n:SZ.t) : Tot (b:U8.t { U8.v b == SZ.v n % 256 }) =
  let r = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 n) in
  // U8.v r == (SZ.v n % pow2 32) % pow2 8
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 8 * pow2 24 == pow2 32);
  FStar.Math.Lemmas.modulo_modulo_lemma (SZ.v n) (pow2 8) (pow2 24);
  r

(* [u8_of_sizet] of [SZ.div n d] equals the spec byte [byte (SZ.v n / d)]:
   both have [U8.v == (SZ.v n / d) % 256], so they are equal by [v]-injectivity.
   Stated as an SMTPat on [u8_of_sizet _] so the wire-length byte-split proofs
   (which describe the stored value as [byte (SZ.v len / d)]) stay automatic once
   the executable store writes [u8_of_sizet (SZ.div len dsz)] instead. *)
let u8_of_sizet_v_byte (n:SZ.t)
  : Lemma (u8_of_sizet n == byte (SZ.v n))
          [SMTPat (u8_of_sizet n)]
  = ()

(* High byte of a u24 via two divisions by 256 (the [65536sz] literal exceeds
   SizeT's portable 16-bit minimum range, so we cannot write it directly):
   [(n / 256) / 256 == n / 65536]. *)
let u8_of_sizet_div2_byte (n:SZ.t)
  : Lemma (u8_of_sizet (SZ.div (SZ.div n 256sz) 256sz) == byte (SZ.v n / 65536))
  = FStar.Math.Lemmas.division_multiplication_lemma (SZ.v n) 256 256

let lemma_client_hello_byte_eq (n:nat)
  : Lemma (byte n == WSR.client_hello_byte n)
=
  WSR.lemma_client_hello_byte_v n;
  assert_norm (U8.v (byte n) == n % 256);
  U8.v_inj (byte n) (WSR.client_hello_byte n)

let write_u16_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 256); byte n]

let write_u24_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 65536); byte (n / 256); byte n]

let application_data_header_bytes (n:nat) : GTot (b:B.bytes{B.length b == 5}) =
  B.of_list [0x17uy; 0x03uy; 0x03uy; byte (n / 256); byte n]

let handshake_record_header_bytes (n:nat) : GTot (b:B.bytes{B.length b == 5}) =
  B.of_list [0x16uy; 0x03uy; 0x03uy; byte (n / 256); byte n]

let lemma_handshake_record_header_bytes (n:nat)
  : Lemma (ensures Seq.equal
      (handshake_record_header_bytes n)
      (WSR.serialize_record_header T.Handshake n))
=
  WSR.lemma_serialize_handshake_record_header_reveal n;
  WSR.lemma_byte_value (n / 256);
  WSR.lemma_byte_value n;
  assert_norm (handshake_record_header_bytes n == B.of_list [0x16uy; 0x03uy; 0x03uy; byte (n / 256); byte n]);
  assert_norm (U8.v (byte (n / 256)) == (n / 256) % 256);
  assert_norm (U8.v (byte n) == n % 256);
  U8.v_inj (WSR.byte (n / 256)) (byte (n / 256));
  U8.v_inj (WSR.byte n) (byte n);
  assert (WSR.byte (n / 256) == byte (n / 256));
  assert (WSR.byte n == byte n);
  assert_norm (B.of_list [
      0x16uy; 0x03uy; 0x03uy;
      U8.uint_to_t ((n / 256) % 256);
      U8.uint_to_t (n % 256)
    ] == B.of_list [0x16uy; 0x03uy; 0x03uy; byte (n / 256); byte n]);
  Seq.lemma_eq_elim
    (B.of_list [0x16uy; 0x03uy; 0x03uy; WSR.byte (n / 256); WSR.byte n])
    (handshake_record_header_bytes n)

let lemma_eq_handshake_record_header_from_indices (s:B.bytes) (n:nat)
  : Lemma
      (requires B.length s == 5 /\
                Seq.index s 0 == Seq.index (handshake_record_header_bytes n) 0 /\
                Seq.index s 1 == Seq.index (handshake_record_header_bytes n) 1 /\
                Seq.index s 2 == Seq.index (handshake_record_header_bytes n) 2 /\
                Seq.index s 3 == Seq.index (handshake_record_header_bytes n) 3 /\
                Seq.index s 4 == Seq.index (handshake_record_header_bytes n) 4)
      (ensures Seq.equal s (handshake_record_header_bytes n))
=
  let h = handshake_record_header_bytes n in
  assert (B.length h == 5);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index h i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else assert False
  );
  Seq.lemma_eq_intro s h

let lemma_handshake_record_header_indices (n:nat)
  : Lemma
      (ensures Seq.index (handshake_record_header_bytes n) 0 == 22uy /\
               Seq.index (handshake_record_header_bytes n) 1 == 0x03uy /\
               Seq.index (handshake_record_header_bytes n) 2 == 0x03uy /\
               Seq.index (handshake_record_header_bytes n) 3 == byte (n / 256) /\
               Seq.index (handshake_record_header_bytes n) 4 == byte n)
=
  assert_norm (Seq.index (handshake_record_header_bytes n) 0 == 22uy);
  assert_norm (Seq.index (handshake_record_header_bytes n) 1 == 0x03uy);
  assert_norm (Seq.index (handshake_record_header_bytes n) 2 == 0x03uy);
  assert_norm (Seq.index (handshake_record_header_bytes n) 3 == byte (n / 256));
  assert_norm (Seq.index (handshake_record_header_bytes n) 4 == byte n)

let lemma_application_data_header_bytes (n:nat)
  : Lemma (ensures Seq.equal
      (application_data_header_bytes n)
      (WSR.application_data_record_header_bytes n))
=
  WSR.lemma_application_data_record_header_bytes_reveal n;
  WSR.lemma_byte_value (n / 256);
  WSR.lemma_byte_value n;
  assert_norm (U8.v (byte (n / 256)) == (n / 256) % 256);
  assert_norm (U8.v (byte n) == n % 256);
  U8.v_inj (WSR.byte (n / 256)) (byte (n / 256));
  U8.v_inj (WSR.byte n) (byte n);
  assert (WSR.byte (n / 256) == byte (n / 256));
  assert (WSR.byte n == byte n);
  Seq.lemma_eq_elim
    (WSR.application_data_record_header_bytes n)
    (B.of_list [0x17uy; 0x03uy; 0x03uy; byte (n / 256); byte n]);
  assert_norm (application_data_header_bytes n == B.of_list [0x17uy; 0x03uy; 0x03uy; byte (n / 256); byte n]);
  Seq.lemma_eq_refl (application_data_header_bytes n) (WSR.application_data_record_header_bytes n)

let lemma_slice_create (#a:eqtype) (n:nat) (lo:nat) (hi:nat) (x:a)
  : Lemma (requires lo <= hi /\ hi <= n)
          (ensures Seq.equal
            (Seq.slice (Seq.create n x) lo hi)
            (Seq.create (hi - lo) x))
=
  Seq.lemma_create_len n x;
  Seq.lemma_len_slice (Seq.create n x) lo hi;
  Seq.lemma_create_len (hi - lo) x;
  assert (forall (i:nat{i < hi - lo}).
    Seq.index (Seq.slice (Seq.create n x) lo hi) i ==
    Seq.index (Seq.create (hi - lo) x) i);
  Seq.lemma_eq_intro (Seq.slice (Seq.create n x) lo hi) (Seq.create (hi - lo) x)

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
  let full = B.append prefix tail in
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

let lemma_equal_prefix_raw_slice
  (a:B.bytes)
  (b:B.bytes)
  (prefix_len:nat)
  (lo:nat)
  (hi:nat)
  : Lemma
      (requires lo <= hi /\
                hi <= prefix_len /\
                prefix_len <= B.length a /\
                prefix_len <= B.length b /\
                Seq.equal (CL.raw_slice a 0 prefix_len) (CL.raw_slice b 0 prefix_len))
      (ensures Seq.equal (CL.raw_slice a lo hi) (CL.raw_slice b lo hi))
=
  Seq.lemma_len_slice a lo hi;
  Seq.lemma_len_slice b lo hi;
  Seq.lemma_eq_elim (CL.raw_slice a 0 prefix_len) (CL.raw_slice b 0 prefix_len);
  introduce forall (i:nat).
    i < hi - lo ==>
    Seq.index (CL.raw_slice a lo hi) i ==
    Seq.index (CL.raw_slice b lo hi) i
  with introduce _ ==> _
  with _. (
    let k = lo + i in
    lemma_raw_slice_index a lo hi i;
    lemma_raw_slice_index b lo hi i;
    lemma_raw_slice_index a 0 prefix_len k;
    lemma_raw_slice_index b 0 prefix_len k
  );
  Seq.lemma_eq_intro (CL.raw_slice a lo hi) (CL.raw_slice b lo hi)

#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 20"
let lemma_eq_supported_groups_bytes (s:B.bytes)
  : Lemma
      (requires B.length s == 8 /\
                Seq.index s 0 == 0uy /\
                Seq.index s 1 == 0x0auy /\
                Seq.index s 2 == 0uy /\
                Seq.index s 3 == 4uy /\
                Seq.index s 4 == 0uy /\
                Seq.index s 5 == 2uy /\
                Seq.index s 6 == 0uy /\
                Seq.index s 7 == 0x1duy)
      (ensures Seq.equal s
        (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]))
=
  let bs = SeqP.createL [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy] in
  assert (bs == B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  assert (B.length bs == 8);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index bs i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else if i = 5 then ()
    else if i = 6 then ()
    else if i = 7 then ()
    else assert False
  );
  Seq.lemma_eq_intro s bs;
  Seq.lemma_eq_elim bs (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])

let lemma_eq_signature_algorithms_bytes (s:B.bytes)
  : Lemma
      (requires B.length s == 8 /\
                Seq.index s 0 == 0uy /\
                Seq.index s 1 == 0x0duy /\
                Seq.index s 2 == 0uy /\
                Seq.index s 3 == 4uy /\
                Seq.index s 4 == 0uy /\
                Seq.index s 5 == 2uy /\
                Seq.index s 6 == 0x08uy /\
                Seq.index s 7 == 0x04uy)
      (ensures Seq.equal s
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]))
=
  let bs = SeqP.createL [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy] in
  assert (bs == B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  assert (B.length bs == 8);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index bs i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else if i = 5 then ()
    else if i = 6 then ()
    else if i = 7 then ()
    else assert False
  );
  Seq.lemma_eq_intro s bs;
  Seq.lemma_eq_elim bs (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])

let lemma_eq_key_share_header_bytes (s:B.bytes)
  : Lemma
      (requires B.length s == 10 /\
                Seq.index s 0 == 0uy /\
                Seq.index s 1 == 0x33uy /\
                Seq.index s 2 == 0uy /\
                Seq.index s 3 == 38uy /\
                Seq.index s 4 == 0uy /\
                Seq.index s 5 == 36uy /\
                Seq.index s 6 == 0uy /\
                Seq.index s 7 == 0x1duy /\
                Seq.index s 8 == 0uy /\
                Seq.index s 9 == 32uy)
      (ensures Seq.equal s
        (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]))
=
  let header = SeqP.createL [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  assert (header == B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (B.length header == 10);
  assert (Seq.index header 0 == 0uy);
  assert (Seq.index header 1 == 0x33uy);
  assert (Seq.index header 2 == 0uy);
  assert (Seq.index header 3 == 38uy);
  assert (Seq.index header 4 == 0uy);
  assert (Seq.index header 5 == 36uy);
  assert (Seq.index header 6 == 0uy);
  assert (Seq.index header 7 == 0x1duy);
  assert (Seq.index header 8 == 0uy);
  assert (Seq.index header 9 == 32uy);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index header i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else if i = 5 then ()
    else if i = 6 then ()
    else if i = 7 then ()
    else if i = 8 then ()
    else if i = 9 then ()
    else assert False
  );
  Seq.lemma_eq_intro s header;
  Seq.lemma_eq_elim header (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])

let lemma_eq_supported_versions_bytes (s:B.bytes)
  : Lemma
      (requires B.length s == 7 /\
                Seq.index s 0 == 0uy /\
                Seq.index s 1 == 0x2buy /\
                Seq.index s 2 == 0uy /\
                Seq.index s 3 == 3uy /\
                Seq.index s 4 == 2uy /\
                Seq.index s 5 == 0x03uy /\
                Seq.index s 6 == 0x04uy)
      (ensures Seq.equal s
        (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))
=
  let versions = SeqP.createL [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy] in
  assert (versions == B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  assert (B.length versions == 7);
  assert (Seq.index versions 0 == 0uy);
  assert (Seq.index versions 1 == 0x2buy);
  assert (Seq.index versions 2 == 0uy);
  assert (Seq.index versions 3 == 3uy);
  assert (Seq.index versions 4 == 2uy);
  assert (Seq.index versions 5 == 0x03uy);
  assert (Seq.index versions 6 == 0x04uy);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index versions i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else if i = 5 then ()
    else if i = 6 then ()
    else assert False
  );
  Seq.lemma_eq_intro s versions;
  Seq.lemma_eq_elim versions (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])
#pop-options

let lemma_append_assoc (#a:eqtype) (x:Seq.seq a) (y:Seq.seq a) (z:Seq.seq a)
  : Lemma (ensures Seq.equal
      (Seq.append (Seq.append x y) z)
      (Seq.append x (Seq.append y z)))
=
  Seq.lemma_len_append x y;
  Seq.lemma_len_append (Seq.append x y) z;
  Seq.lemma_len_append y z;
  Seq.lemma_len_append x (Seq.append y z);
  assert (forall (i:nat{i < Seq.length (Seq.append (Seq.append x y) z)}).
    Seq.index (Seq.append (Seq.append x y) z) i ==
    Seq.index (Seq.append x (Seq.append y z)) i);
  Seq.lemma_eq_intro (Seq.append (Seq.append x y) z) (Seq.append x (Seq.append y z))

let cv_context_with_zero : b:B.bytes{B.length b == 34} =
  WSR.certificate_verify_context_with_zero

let cv_context_index (i:nat{i < 34}) : U8.t =
  Seq.index cv_context_with_zero i

let cv_out_after_context (spaces:B.bytes) (context:B.bytes) : B.bytes =
  B.append
    (CL.raw_slice spaces 0 64)
    (B.append (CL.raw_slice context 0 34) (CL.raw_slice spaces 98 130))

let cv_out_after_hash (hash:B.bytes) (spaces:B.bytes) (context:B.bytes) : B.bytes =
  let after_context = cv_out_after_context spaces context in
  B.append
    (CL.raw_slice after_context 0 98)
    (B.append (CL.raw_slice hash 0 32) (CL.raw_slice after_context 130 130))

inline_for_extraction
let cv_context_byte (i:SZ.t) : U8.t =
  if i `SZ.lt` 8sz then
    if i = 0sz then 0x54uy
    else if i = 1sz then 0x4cuy
    else if i = 2sz then 0x53uy
    else if i = 3sz then 0x20uy
    else if i = 4sz then 0x31uy
    else if i = 5sz then 0x2euy
    else if i = 6sz then 0x33uy
    else 0x2cuy
  else if i `SZ.lt` 16sz then
    if i = 8sz then 0x20uy
    else if i = 9sz then 0x73uy
    else if i = 10sz then 0x65uy
    else if i = 11sz then 0x72uy
    else if i = 12sz then 0x76uy
    else if i = 13sz then 0x65uy
    else if i = 14sz then 0x72uy
    else 0x20uy
  else if i `SZ.lt` 24sz then
    if i = 16sz then 0x43uy
    else if i = 17sz then 0x65uy
    else if i = 18sz then 0x72uy
    else if i = 19sz then 0x74uy
    else if i = 20sz then 0x69uy
    else if i = 21sz then 0x66uy
    else if i = 22sz then 0x69uy
    else 0x63uy
  else if i `SZ.lt` 32sz then
    if i = 24sz then 0x61uy
    else if i = 25sz then 0x74uy
    else if i = 26sz then 0x65uy
    else if i = 27sz then 0x56uy
    else if i = 28sz then 0x65uy
    else if i = 29sz then 0x72uy
    else if i = 30sz then 0x69uy
    else 0x66uy
  else if i = 32sz then 0x79uy
  else 0uy

let lemma_sizet_eq_of_v (x:SZ.t) (y:SZ.t)
  : Lemma (requires SZ.v x == SZ.v y)
          (ensures x == y)
=
  SZ.size_v_inj x;
  SZ.size_v_inj y

// Proof strategy for lemma_cv_context_byte_reveal:
// cv_context_byte uses a SizeT if-chain (transparent, normalizable).
// cv_context_index k = Seq.index WSR.certificate_verify_context_with_zero k.
// WSR.lemma_certificate_verify_context_index_* reveals each concrete context byte.
// assert_norm handles the SizeT if-chain for cv_context_byte ksz.
let lemma_cv_context_byte_reveal (i:SZ.t)
  : Lemma (requires SZ.v i < 34)
          (ensures cv_context_byte i ==
                   cv_context_index (SZ.v i))
=
  let iv : n:nat{n < 34} = SZ.v i in
  match iv with
  | 0  -> WSR.lemma_certificate_verify_context_index_0 (); lemma_sizet_eq_of_v i  0sz; assert_norm (cv_context_byte  0sz == 0x54uy)
  | 1  -> WSR.lemma_certificate_verify_context_index_1 (); lemma_sizet_eq_of_v i  1sz; assert_norm (cv_context_byte  1sz == 0x4cuy)
  | 2  -> WSR.lemma_certificate_verify_context_index_2 (); lemma_sizet_eq_of_v i  2sz; assert_norm (cv_context_byte  2sz == 0x53uy)
  | 3  -> WSR.lemma_certificate_verify_context_index_3 (); lemma_sizet_eq_of_v i  3sz; assert_norm (cv_context_byte  3sz == 0x20uy)
  | 4  -> WSR.lemma_certificate_verify_context_index_4 (); lemma_sizet_eq_of_v i  4sz; assert_norm (cv_context_byte  4sz == 0x31uy)
  | 5  -> WSR.lemma_certificate_verify_context_index_5 (); lemma_sizet_eq_of_v i  5sz; assert_norm (cv_context_byte  5sz == 0x2euy)
  | 6  -> WSR.lemma_certificate_verify_context_index_6 (); lemma_sizet_eq_of_v i  6sz; assert_norm (cv_context_byte  6sz == 0x33uy)
  | 7  -> WSR.lemma_certificate_verify_context_index_7 (); lemma_sizet_eq_of_v i  7sz; assert_norm (cv_context_byte  7sz == 0x2cuy)
  | 8  -> WSR.lemma_certificate_verify_context_index_8 (); lemma_sizet_eq_of_v i  8sz; assert_norm (cv_context_byte  8sz == 0x20uy)
  | 9  -> WSR.lemma_certificate_verify_context_index_9 (); lemma_sizet_eq_of_v i  9sz; assert_norm (cv_context_byte  9sz == 0x73uy)
  | 10 -> WSR.lemma_certificate_verify_context_index_10 (); lemma_sizet_eq_of_v i 10sz; assert_norm (cv_context_byte 10sz == 0x65uy)
  | 11 -> WSR.lemma_certificate_verify_context_index_11 (); lemma_sizet_eq_of_v i 11sz; assert_norm (cv_context_byte 11sz == 0x72uy)
  | 12 -> WSR.lemma_certificate_verify_context_index_12 (); lemma_sizet_eq_of_v i 12sz; assert_norm (cv_context_byte 12sz == 0x76uy)
  | 13 -> WSR.lemma_certificate_verify_context_index_13 (); lemma_sizet_eq_of_v i 13sz; assert_norm (cv_context_byte 13sz == 0x65uy)
  | 14 -> WSR.lemma_certificate_verify_context_index_14 (); lemma_sizet_eq_of_v i 14sz; assert_norm (cv_context_byte 14sz == 0x72uy)
  | 15 -> WSR.lemma_certificate_verify_context_index_15 (); lemma_sizet_eq_of_v i 15sz; assert_norm (cv_context_byte 15sz == 0x20uy)
  | 16 -> WSR.lemma_certificate_verify_context_index_16 (); lemma_sizet_eq_of_v i 16sz; assert_norm (cv_context_byte 16sz == 0x43uy)
  | 17 -> WSR.lemma_certificate_verify_context_index_17 (); lemma_sizet_eq_of_v i 17sz; assert_norm (cv_context_byte 17sz == 0x65uy)
  | 18 -> WSR.lemma_certificate_verify_context_index_18 (); lemma_sizet_eq_of_v i 18sz; assert_norm (cv_context_byte 18sz == 0x72uy)
  | 19 -> WSR.lemma_certificate_verify_context_index_19 (); lemma_sizet_eq_of_v i 19sz; assert_norm (cv_context_byte 19sz == 0x74uy)
  | 20 -> WSR.lemma_certificate_verify_context_index_20 (); lemma_sizet_eq_of_v i 20sz; assert_norm (cv_context_byte 20sz == 0x69uy)
  | 21 -> WSR.lemma_certificate_verify_context_index_21 (); lemma_sizet_eq_of_v i 21sz; assert_norm (cv_context_byte 21sz == 0x66uy)
  | 22 -> WSR.lemma_certificate_verify_context_index_22 (); lemma_sizet_eq_of_v i 22sz; assert_norm (cv_context_byte 22sz == 0x69uy)
  | 23 -> WSR.lemma_certificate_verify_context_index_23 (); lemma_sizet_eq_of_v i 23sz; assert_norm (cv_context_byte 23sz == 0x63uy)
  | 24 -> WSR.lemma_certificate_verify_context_index_24 (); lemma_sizet_eq_of_v i 24sz; assert_norm (cv_context_byte 24sz == 0x61uy)
  | 25 -> WSR.lemma_certificate_verify_context_index_25 (); lemma_sizet_eq_of_v i 25sz; assert_norm (cv_context_byte 25sz == 0x74uy)
  | 26 -> WSR.lemma_certificate_verify_context_index_26 (); lemma_sizet_eq_of_v i 26sz; assert_norm (cv_context_byte 26sz == 0x65uy)
  | 27 -> WSR.lemma_certificate_verify_context_index_27 (); lemma_sizet_eq_of_v i 27sz; assert_norm (cv_context_byte 27sz == 0x56uy)
  | 28 -> WSR.lemma_certificate_verify_context_index_28 (); lemma_sizet_eq_of_v i 28sz; assert_norm (cv_context_byte 28sz == 0x65uy)
  | 29 -> WSR.lemma_certificate_verify_context_index_29 (); lemma_sizet_eq_of_v i 29sz; assert_norm (cv_context_byte 29sz == 0x72uy)
  | 30 -> WSR.lemma_certificate_verify_context_index_30 (); lemma_sizet_eq_of_v i 30sz; assert_norm (cv_context_byte 30sz == 0x69uy)
  | 31 -> WSR.lemma_certificate_verify_context_index_31 (); lemma_sizet_eq_of_v i 31sz; assert_norm (cv_context_byte 31sz == 0x66uy)
  | 32 -> WSR.lemma_certificate_verify_context_index_32 (); lemma_sizet_eq_of_v i 32sz; assert_norm (cv_context_byte 32sz == 0x79uy)
  | _  -> WSR.lemma_certificate_verify_context_index_33 (); lemma_sizet_eq_of_v i 33sz; assert_norm (cv_context_byte 33sz == 0uy)


let lemma_cv_out_after_hash_reveal
  (hash:B.bytes)
  (spaces:B.bytes)
  (context:B.bytes)
  : Lemma (requires B.length hash == 32 /\
                    B.length spaces == 130 /\
                    Seq.equal spaces (Seq.create 130 0x20uy) /\
                    B.length context == 34 /\
                    Seq.equal context cv_context_with_zero)
          (ensures Seq.equal
            (cv_out_after_hash hash spaces context)
            (WS.serialize_server_certificate_verify_input hash))
=
  let spaces64 = Seq.create 64 0x20uy in
  let spaces32 = Seq.create 32 0x20uy in
  let context0 = cv_context_with_zero in
  let after_context = cv_out_after_context spaces context in
  let after_context_expected = B.append spaces64 (B.append context0 spaces32) in

  Seq.lemma_eq_elim spaces (Seq.create 130 0x20uy);
  lemma_slice_create 130 0 64 0x20uy;
  lemma_slice_create 130 98 130 0x20uy;
  lemma_raw_slice_all context;
  Seq.lemma_eq_elim context context0;
  assert (Seq.equal after_context after_context_expected);

  Seq.lemma_create_len 64 0x20uy;
  Seq.lemma_create_len 32 0x20uy;
  assert (B.length context0 == 34);
  Seq.lemma_len_append context0 spaces32;
  Seq.lemma_len_append spaces64 (B.append context0 spaces32);
  assert (B.length after_context_expected == 130);
  Seq.lemma_eq_elim after_context after_context_expected;

  SeqP.append_slices spaces64 (B.append context0 spaces32);
  SeqP.append_slices context0 spaces32;
  assert (Seq.equal (CL.raw_slice after_context 0 98) (B.append spaces64 context0));
  lemma_raw_slice_all hash;
  lemma_raw_slice_empty after_context 130;
  assert (Seq.equal
    (cv_out_after_hash hash spaces context)
    (B.append (B.append spaces64 context0) hash));

  lemma_append_assoc spaces64 context0 hash;
  WSR.lemma_serialize_server_certificate_verify_input_bytes hash;
  Seq.lemma_eq_elim
    (WS.serialize_server_certificate_verify_input hash)
    (B.append (B.append spaces64 context0) hash);
  Seq.lemma_eq_refl
    (cv_out_after_hash hash spaces context)
    (WS.serialize_server_certificate_verify_input hash)

#push-options "--split_queries always"
let lemma_content_type_matches_byte (wire:U8.t) (ct:T.content_type)
  : Lemma (requires L.content_type_matches wire ct)
          (ensures wire == WSR.content_type_byte ct)
=
  match ct with
  | T.ChangeCipherSpec ->
      assert (ct == T.ChangeCipherSpec);
      assert (U8.v wire == 0x14);
      WSR.lemma_content_type_byte_value T.ChangeCipherSpec;
      assert (U8.v (WSR.content_type_byte T.ChangeCipherSpec) == 0x14);
      U8.v_inj wire (WSR.content_type_byte T.ChangeCipherSpec);
      assert (wire == WSR.content_type_byte T.ChangeCipherSpec);
      assert (wire == WSR.content_type_byte ct)
  | T.Alert ->
      assert (ct == T.Alert);
      assert (U8.v wire == 0x15);
      WSR.lemma_content_type_byte_value T.Alert;
      assert (U8.v (WSR.content_type_byte T.Alert) == 0x15);
      U8.v_inj wire (WSR.content_type_byte T.Alert);
      assert (wire == WSR.content_type_byte T.Alert);
      assert (wire == WSR.content_type_byte ct)
  | T.Handshake ->
      assert (ct == T.Handshake);
      assert (U8.v wire == 0x16);
      WSR.lemma_content_type_byte_value T.Handshake;
      assert (U8.v (WSR.content_type_byte T.Handshake) == 0x16);
      U8.v_inj wire (WSR.content_type_byte T.Handshake);
      assert (wire == WSR.content_type_byte T.Handshake);
      assert (wire == WSR.content_type_byte ct)
  | T.ApplicationData ->
      assert (ct == T.ApplicationData);
      assert (U8.v wire == 0x17);
      WSR.lemma_content_type_byte_value T.ApplicationData;
      assert (U8.v (WSR.content_type_byte T.ApplicationData) == 0x17);
      U8.v_inj wire (WSR.content_type_byte T.ApplicationData);
      assert (wire == WSR.content_type_byte T.ApplicationData);
      assert (wire == WSR.content_type_byte ct)
#pop-options

let inner_plaintext_post_prop (wire:U8.t) (fragment:B.bytes) (out_bytes:B.bytes) (ct:T.content_type) : prop =
  Seq.equal out_bytes
    (WS.serialize_plaintext { M.content_type = ct; M.fragment = fragment }) /\
  WS.parse_plaintext out_bytes ==
    Some { M.content_type = ct; M.fragment = fragment }

let lemma_inner_plaintext_for_ct
  (wire:U8.t)
  (ct:T.content_type)
  (fragment:B.bytes)
  (out_bytes:B.bytes)
  : Lemma (requires L.content_type_matches wire ct /\
                    Seq.equal out_bytes (B.append fragment (B.singleton wire)))
          (ensures inner_plaintext_post_prop wire fragment out_bytes ct)
=
  lemma_content_type_matches_byte wire ct;
  assert (wire == WSR.content_type_byte ct);
  assert (Seq.equal (B.singleton wire) (B.singleton (WSR.content_type_byte ct)));
  Seq.lemma_eq_elim (B.singleton wire) (B.singleton (WSR.content_type_byte ct));
  assert (Seq.equal out_bytes (B.append fragment (B.singleton (WSR.content_type_byte ct))));
  Seq.lemma_eq_elim out_bytes (B.append fragment (B.singleton (WSR.content_type_byte ct)));
  WSR.lemma_plaintext_roundtrip_reveal ct fragment

let lemma_inner_plaintext_post
  (wire:U8.t)
  (fragment:B.bytes)
  (out_bytes:B.bytes)
  : Lemma (requires Seq.equal out_bytes (B.append fragment (B.singleton wire)))
          (ensures forall ct.
            L.content_type_matches wire ct ==>
            inner_plaintext_post_prop wire fragment out_bytes ct)
=
  introduce forall (ct:T.content_type).
    L.content_type_matches wire ct ==>
    inner_plaintext_post_prop wire fragment out_bytes ct
  with introduce _ ==> _
  with _. (
    lemma_inner_plaintext_for_ct wire ct fragment out_bytes
  )

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

fn copy_vec_to_vec_u8
  (src:V.vec U8.t)
  (dst:V.vec U8.t)
  (len:SZ.t)
  requires V.pts_to src 'src_bytes **
           V.pts_to dst 'dst_bytes **
           pure (V.is_full_vec src /\
                 V.is_full_vec dst /\
                 V.length src == SZ.v len /\
                 V.length dst == SZ.v len /\
                 B.length 'src_bytes == SZ.v len /\
                 B.length 'dst_bytes == SZ.v len)
  ensures V.pts_to src 'src_bytes **
          V.pts_to dst 'src_bytes **
          pure (V.is_full_vec src /\
                V.is_full_vec dst /\
                V.length src == SZ.v len /\
                V.length dst == SZ.v len)
{
  V.to_array_pts_to src;
  V.to_array_pts_to dst;
  Arr.memcpy len (V.vec_to_array src) (V.vec_to_array dst);
  V.to_vec_pts_to src;
  V.to_vec_pts_to dst
}

fn copy_vec_to_vec_u16
  (src:V.vec U16.t)
  (dst:V.vec U16.t)
  (len:SZ.t)
  requires V.pts_to src 'src_items **
           V.pts_to dst 'dst_items **
           pure (V.is_full_vec src /\
                 V.is_full_vec dst /\
                 V.length src == SZ.v len /\
                 V.length dst == SZ.v len /\
                 Seq.length 'src_items == SZ.v len /\
                 Seq.length 'dst_items == SZ.v len)
  ensures V.pts_to src 'src_items **
          V.pts_to dst 'src_items **
          pure (V.is_full_vec src /\
                V.is_full_vec dst /\
                V.length src == SZ.v len /\
                V.length dst == SZ.v len)
{
  V.to_array_pts_to src;
  V.to_array_pts_to dst;
  Arr.memcpy len (V.vec_to_array src) (V.vec_to_array dst);
  V.to_vec_pts_to src;
  V.to_vec_pts_to dst
}

fn build_server_certificate_verify_input
  (transcript_hash: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to transcript_hash 'hash_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'hash_bytes == 32 /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 130)
  ensures exists* out_bytes.
          pts_to transcript_hash 'hash_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130 /\
                B.length 'hash_bytes == 32 /\
                Seq.equal
                  (Ghost.reveal out_bytes)
                  (WS.serialize_server_certificate_verify_input (Ghost.reveal 'hash_bytes)))
{
  pts_to_len out;
  Arr.fill 130sz out 0x20uy;
  with spaces_bytes. assert (pts_to out spaces_bytes);
  assert (pure (Seq.equal (Ghost.reveal spaces_bytes) (Seq.create 130 0x20uy)));
  let mut context = [| 0uy; 34sz |];
  let mut i = 0sz;
  while ((Ref.read i) `SZ.lt` 34sz)
    invariant live i
    invariant exists* context_loop.
      pts_to context context_loop **
      pure (B.length context_loop == 34 /\
            SZ.v (Ref.read i) <= 34 /\
            (forall (k:nat). k < SZ.v (Ref.read i) ==>
              Seq.index context_loop k ==
              cv_context_index k) /\
            (forall (k:nat). SZ.v (Ref.read i) <= k /\ k < 34 ==>
              Seq.index context_loop k == 0uy))
  {
    let vi = Ref.read i;
    assert (pure (SZ.v vi < 34));
    let b = cv_context_byte vi;
    lemma_cv_context_byte_reveal vi;
    context.(vi) <- b;
    with context_after_write.
      assert (pts_to context context_after_write);
    assert (pure (B.length context_after_write == 34));
    assert (pure (forall (k:nat). k < SZ.v vi + 1 ==>
      Seq.index context_after_write k ==
      cv_context_index k));
    assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < 34 ==>
      Seq.index context_after_write k == 0uy));
    assert (pure (SZ.v vi + 1 <= 34));
    SZ.fits_lte (SZ.v vi + 1) 34;
    let next_i = vi `SZ.add` 1sz;
    Ref.write i next_i;
  };
  with context_bytes. assert (pts_to context context_bytes);
  assert (pure (B.length (Ghost.reveal context_bytes) == 34));
  assert (pure (forall (k:nat). k < 34 ==>
    Seq.index (Ghost.reveal context_bytes) k ==
    cv_context_index k));
  assert (pure (forall (k:nat). k < 34 ==>
    cv_context_index k == Seq.index cv_context_with_zero k));
  Seq.lemma_eq_intro
    (Ghost.reveal context_bytes)
    cv_context_with_zero;
  assert (pure (Seq.equal
    (Ghost.reveal context_bytes)
    cv_context_with_zero));
  copy_array_slice_to_array context 34sz 0sz 34sz out 130sz 64sz;
  copy_array_slice_to_array transcript_hash 32sz 0sz 32sz out 130sz 98sz;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == 130));
  WS.lemma_serialize_server_certificate_verify_input_len32 (Ghost.reveal 'hash_bytes);
  assert (pure (B.length (Ghost.reveal 'hash_bytes) == 32));
  assert (pure (B.length (Ghost.reveal spaces_bytes) == 130));
  assert (pure (Seq.equal (Ghost.reveal spaces_bytes) (Seq.create 130 0x20uy)));
  assert (pure (B.length (Ghost.reveal context_bytes) == 34));
  assert (pure (Seq.equal
    (Ghost.reveal context_bytes)
    cv_context_with_zero));
  lemma_cv_out_after_hash_reveal
    (Ghost.reveal 'hash_bytes)
    (Ghost.reveal spaces_bytes)
    (Ghost.reveal context_bytes);
  assert (pure (Seq.equal
    out_bytes
    (cv_out_after_hash
      (Ghost.reveal 'hash_bytes)
      (Ghost.reveal spaces_bytes)
      (Ghost.reveal context_bytes))));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_server_certificate_verify_input (Ghost.reveal 'hash_bytes))));
}

fn serialize_finished_handshake
  (#fin: erased M.finished)
  (lfin: L.finished)
  (handshake_out: array U8.t)
  (handshake_out_len: SZ.t)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           pts_to handshake_out 'old_handshake **
           pure (B.length 'old_handshake == SZ.v handshake_out_len /\
                 SZ.v handshake_out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v handshake_out_len})
  ensures exists* handshake_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          pts_to handshake_out handshake_bytes **
          pure (B.length handshake_bytes == 36 /\
                SZ.v written == 36 /\
                Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                WS.parse_tls_message T.Handshake handshake_bytes ==
                  Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  unfold (L.is_valid_finished lfin (Ghost.reveal fin));
  with verify_data. assert (V.pts_to lfin.L.finished_verify_data verify_data);
  handshake_out.(0sz) <- 20uy;
  handshake_out.(1sz) <- 0uy;
  handshake_out.(2sz) <- 0uy;
  handshake_out.(3sz) <- 32uy;
  V.to_array_pts_to lfin.L.finished_verify_data;
  copy_array_slice_to_array
    (V.vec_to_array lfin.L.finished_verify_data)
    32sz
    0sz
    32sz
    handshake_out
    36sz
    4sz;
  V.to_vec_pts_to lfin.L.finished_verify_data;
  with handshake_bytes. assert (pts_to handshake_out handshake_bytes);
  assert (pure (B.length handshake_bytes == 36));
  assert (pure (B.length verify_data == 32));
  WS.lemma_serialize_finished_len (Ghost.reveal fin);
  WSR.lemma_serialize_finished_reveal (Ghost.reveal fin);
  assert (pure (Seq.equal verify_data (Ghost.reveal fin).M.verify_data));
  assert (pure (Seq.equal
    handshake_bytes
    (WS.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  WSR.lemma_parse_finished_handshake (Ghost.reveal fin);
  fold (L.is_valid_finished lfin (Ghost.reveal fin));
  36sz
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
                 0 <= SZ.v plain_offset /\
                 0 <= SZ.v plain_len /\
                 SZ.v out_len == SZ.v plain_len + 1 /\
                 SZ.v plain_offset + SZ.v plain_len <= SZ.v plain_total_len)
  ensures exists* out_bytes.
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               0 <= SZ.v plain_offset /\
               0 <= SZ.v plain_len /\
               SZ.v plain_len <= Seq.length (Ghost.reveal out_bytes) /\
               SZ.v plain_offset <= SZ.v plain_offset + SZ.v plain_len /\
               SZ.v plain_offset + SZ.v plain_len <= Seq.length (Ghost.reveal 'plain_bytes) /\
               Seq.equal
                 (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v plain_len))
                 (Seq.slice
                    (Ghost.reveal 'plain_bytes)
                    (SZ.v plain_offset)
                    (SZ.v plain_offset + SZ.v plain_len)) /\
                Seq.equal
                  (Seq.slice
                    (Ghost.reveal out_bytes)
                    (SZ.v plain_len)
                    (Seq.length (Ghost.reveal out_bytes)))
                  (B.singleton content_type) /\
                (forall ct.
                  L.content_type_matches content_type ct ==>
                  Seq.equal
                    (Ghost.reveal out_bytes)
                    (WS.serialize_plaintext {
                      M.content_type = ct;
                      M.fragment =
                        Seq.slice
                          (Ghost.reveal 'plain_bytes)
                          (SZ.v plain_offset)
                          (SZ.v plain_offset + SZ.v plain_len);
                   }) /\
                  WS.parse_plaintext (Ghost.reveal out_bytes) ==
                    Some {
                      M.content_type = ct;
                      M.fragment =
                        Seq.slice
                          (Ghost.reveal 'plain_bytes)
                          (SZ.v plain_offset)
                          (SZ.v plain_offset + SZ.v plain_len);
                    }))
{
  copy_array_slice_to_array plain plain_total_len plain_offset plain_len out out_len 0sz;
  out.(plain_len) <- content_type;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v out_len == SZ.v plain_len + 1));
  assert (pure (Seq.length out_bytes == SZ.v plain_len + 1));
  assert (pure (Seq.equal
    (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v plain_len))
    (Seq.slice
       (Ghost.reveal 'plain_bytes)
       (SZ.v plain_offset)
       (SZ.v plain_offset + SZ.v plain_len))));
  assert (pure (Seq.length
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v plain_len)
      (Seq.length (Ghost.reveal out_bytes))) == 1));
  assert (pure (Seq.index
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v plain_len)
      (Seq.length (Ghost.reveal out_bytes)))
    0 == content_type));
  Seq.lemma_eq_intro
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v plain_len)
      (Seq.length (Ghost.reveal out_bytes)))
    (B.singleton content_type);
  let fragment = Ghost.hide (
    Seq.slice
      (Ghost.reveal 'plain_bytes)
      (SZ.v plain_offset)
      (SZ.v plain_offset + SZ.v plain_len));
  SeqP.lemma_split (Ghost.reveal out_bytes) (SZ.v plain_len);
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (B.append
      (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v plain_len))
      (Seq.slice
        (Ghost.reveal out_bytes)
        (SZ.v plain_len)
        (Seq.length (Ghost.reveal out_bytes))))));
  Seq.lemma_eq_elim
    (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v plain_len))
    (Ghost.reveal fragment);
  Seq.lemma_eq_elim
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v plain_len)
      (Seq.length (Ghost.reveal out_bytes)))
    (B.singleton content_type);
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (B.append (Ghost.reveal fragment) (B.singleton content_type))));
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (B.append
      (Seq.slice
        (Ghost.reveal 'plain_bytes)
        (SZ.v plain_offset)
        (SZ.v plain_offset + SZ.v plain_len))
      (B.singleton content_type))));
  lemma_inner_plaintext_post
    content_type
    (Seq.slice
      (Ghost.reveal 'plain_bytes)
      (SZ.v plain_offset)
      (SZ.v plain_offset + SZ.v plain_len))
    (Ghost.reveal out_bytes);
  assert (pure (forall (ct:T.content_type).
    L.content_type_matches content_type ct ==>
    Seq.equal
      (Ghost.reveal out_bytes)
      (WS.serialize_plaintext {
        M.content_type = ct;
        M.fragment =
          Seq.slice
            (Ghost.reveal 'plain_bytes)
            (SZ.v plain_offset)
            (SZ.v plain_offset + SZ.v plain_len);
      }) /\
    WS.parse_plaintext (Ghost.reveal out_bytes) ==
      Some {
        M.content_type = ct;
        M.fragment =
          Seq.slice
            (Ghost.reveal 'plain_bytes)
            (SZ.v plain_offset)
            (SZ.v plain_offset + SZ.v plain_len);
      }));
}

fn serialize_application_data_header
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5 /\
                 SZ.v fragment_len <= 16640)
  ensures exists* header_bytes.
          pts_to out header_bytes **
          pure (B.length header_bytes == 5 /\
                Seq.equal
                  (Ghost.reveal header_bytes)
                  (CS.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record_header (Ghost.reveal header_bytes) ==
                  Some (T.ApplicationData, SZ.v fragment_len))
{
  out.(0sz) <- 23uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  with header_prefix. assert (pts_to out header_prefix);
  pts_to_len out;
  assert (pure (B.length header_prefix == 5));
  assert (pure (B.length header_prefix == length out));
  out.(3sz) <- u8_of_sizet (SZ.div fragment_len 256sz);
  out.(4sz) <- u8_of_sizet fragment_len;
  with header_bytes. assert (pts_to out header_bytes);
  assert (pure (B.length header_bytes == 5));
  WSR.lemma_application_data_record_header_bytes (SZ.v fragment_len);
  lemma_application_data_header_bytes (SZ.v fragment_len);
  assert (pure (Seq.length (application_data_header_bytes (SZ.v fragment_len)) == 5));
  assert (pure (Seq.index header_bytes 0 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 0));
  assert (pure (Seq.index header_bytes 1 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 1));
  assert (pure (Seq.index header_bytes 2 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 2));
  assert (pure (Seq.index header_bytes 3 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 3));
  assert (pure (Seq.index header_bytes 4 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 4));
  Seq.lemma_eq_intro header_bytes (application_data_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    header_bytes
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CS.application_data_record_header (SZ.v fragment_len))
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  WSR.lemma_parse_application_data_record_header_bytes (SZ.v fragment_len);
  assert (pure (Seq.equal
    header_bytes
    (CS.application_data_record_header (SZ.v fragment_len))));
  assert (pure (WS.parse_record_header header_bytes ==
    Some (T.ApplicationData, SZ.v fragment_len)));
}

fn serialize_raw_application_data_record
  (fragment: array U8.t)
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to fragment 'fragment_bytes **
          pts_to out 'old_out **
          pure (B.length 'old_out == SZ.v out_len /\
                B.length 'fragment_bytes == SZ.v fragment_len /\
                SZ.v fragment_len <= 16640 /\
                SZ.v fragment_len + 5 <= SZ.v out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v fragment_len + 5 /\
               (let raw_prefix =
                  Seq.slice out_bytes 0 (SZ.v written) in
                Seq.equal raw_prefix (WS.serialize_record T.ApplicationData (Ghost.reveal 'fragment_bytes)) /\
                Seq.equal
                  (CS.record_header_aad raw_prefix)
                  (CS.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record raw_prefix ==
                  Some (T.ApplicationData, (Ghost.reveal 'fragment_bytes), SZ.v written) /\
                CS.raw_records_exactly raw_prefix T.ApplicationData 1))
{
  out.(0sz) <- 23uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  with header_prefix. assert (pts_to out header_prefix);
  pts_to_len out;
  assert (pure (B.length header_prefix == SZ.v out_len));
  assert (pure (B.length header_prefix == length out));
  out.(3sz) <- u8_of_sizet (SZ.div fragment_len 256sz);
  out.(4sz) <- u8_of_sizet fragment_len;
  with header_written. assert (pts_to out header_written);
  assert (pure (B.length header_written == SZ.v out_len));
  WSR.lemma_application_data_record_header_bytes (SZ.v fragment_len);
  lemma_application_data_header_bytes (SZ.v fragment_len);
  Seq.lemma_len_slice header_written 0 5;
  assert (pure (Seq.length (CL.raw_slice header_written 0 5) == 5));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 0 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 0));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 1 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 1));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 2 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 2));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 3 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 3));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 4 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 4));
  Seq.lemma_eq_intro (CL.raw_slice header_written 0 5) (application_data_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CL.raw_slice header_written 0 5)
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CS.application_data_record_header (SZ.v fragment_len))
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  copy_array_slice_to_array fragment fragment_len 0sz fragment_len out out_len 5sz;
  let written = SZ.add fragment_len 5sz;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v written == SZ.v fragment_len + 5));
  assert (pure (SZ.v written <= SZ.v out_len));
  lemma_raw_slice_all (Ghost.reveal 'fragment_bytes);
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes);
  SeqP.append_slices
    (CL.raw_slice header_written 0 5)
    (B.append
      (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
      (CL.raw_slice header_written (5 + SZ.v fragment_len) (SZ.v out_len)));
  SeqP.append_slices
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (CL.raw_slice header_written (5 + SZ.v fragment_len) (SZ.v out_len));
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (B.append
      (CL.raw_slice header_written 0 5)
      (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len)))));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (B.append (CS.application_data_record_header (SZ.v fragment_len)) (Ghost.reveal 'fragment_bytes))));
  WSR.lemma_serialize_application_data_record_reveal (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (WS.serialize_record T.ApplicationData (Ghost.reveal 'fragment_bytes))));
  Seq.lemma_eq_elim
    (Seq.slice out_bytes 0 (SZ.v written))
    (WS.serialize_record T.ApplicationData (Ghost.reveal 'fragment_bytes));
  WS.lemma_parse_record_serialize_record
    T.ApplicationData
    (Ghost.reveal 'fragment_bytes);
  assert (pure (B.length (Seq.slice out_bytes 0 (SZ.v written)) == SZ.v written));
  assert (pure (WS.parse_record (Seq.slice out_bytes 0 (SZ.v written)) ==
    Some (T.ApplicationData, (Ghost.reveal 'fragment_bytes), SZ.v written)));
  WSR.lemma_application_data_record_aad (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (CS.record_header_aad (Seq.slice out_bytes 0 (SZ.v written)))
    (CS.application_data_record_header (SZ.v fragment_len))));
  assert (pure (CS.raw_records_exactly (Seq.slice out_bytes 0 (SZ.v written)) T.ApplicationData 1));
  written
}

fn serialize_protected_handshake_record
  (#msg: erased M.handshake_msg)
  (write_state: Rec.record_state)
  (handshake: array U8.t)
  (handshake_len: SZ.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  (#record_write: erased R.direction_state)
  (#handshake_bytes: erased B.bytes)
  (#old_network: erased B.bytes)
  requires Rec.is_record_state write_state (Ghost.reveal record_write) **
           pts_to handshake (Ghost.reveal handshake_bytes) **
           pts_to network_out (Ghost.reveal old_network) **
           pure (B.length (Ghost.reveal handshake_bytes) == SZ.v handshake_len /\
                 Seq.equal
                   (Ghost.reveal handshake_bytes)
                   (WS.serialize_handshake (Ghost.reveal msg)) /\
                 B.length (Ghost.reveal old_network) == SZ.v network_out_len /\
                 SZ.v handshake_len + 17 <= 16640 /\
                 SZ.v handshake_len + 22 <= SZ.v network_out_len /\
                 Some? (R.seal
                   (Ghost.reveal record_write)
                   (CS.application_data_record_header (SZ.v handshake_len + 17))
                   {
                     R.content_type = T.ApplicationData;
                     R.fragment =
                       CS.sent_tls_inner_plaintext_fragment
                         (M.TlsHandshake (Ghost.reveal msg));
                   }))
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* network_bytes.
          Rec.is_record_state write_state (Ghost.reveal record_write) **
          pts_to handshake (Ghost.reveal handshake_bytes) **
          pts_to network_out network_bytes **
          pure (B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == SZ.v handshake_len + 22 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.ApplicationData 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.ApplicationData, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.ApplicationData outer_fragment) /\
                   Seq.equal
                     (CS.record_header_aad raw_prefix)
                     (CS.application_data_record_header (SZ.v handshake_len + 17)) /\
                   R.seal
                     (Ghost.reveal record_write)
                     (CS.record_header_aad raw_prefix)
                     {
                       R.content_type = T.ApplicationData;
                       R.fragment =
                         CS.sent_tls_inner_plaintext_fragment
                           (M.TlsHandshake (Ghost.reveal msg));
                     } ==
                     Some (outer_fragment, R.next_seq (Ghost.reveal record_write)))))
{
  SerPR.serialize_protected_handshake_record
    #msg
    write_state
    handshake
    handshake_len
    network_out
    network_out_len
    #record_write
    #handshake_bytes
    #old_network
}

fn serialize_client_finished_outputs
  (write_state: Rec.record_state)
  (lfin: L.finished)
  (handshake_out: array U8.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  requires Rec.is_record_state write_state 'record_write **
           (exists* fin. L.is_valid_finished lfin fin **
             pure (Some? (R.seal
               'record_write
               (CS.application_data_record_header 53)
               {
                 R.content_type = T.ApplicationData;
                 R.fragment =
                   CS.sent_tls_inner_plaintext_fragment
                     (M.TlsHandshake (M.Finished fin));
               }))) **
           pts_to handshake_out 'old_handshake **
           pts_to network_out 'old_network **
           pure (B.length 'old_handshake == 36 /\
                B.length 'old_network == SZ.v network_out_len /\
                58 <= SZ.v network_out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* fin handshake_bytes network_bytes.
          Rec.is_record_state write_state 'record_write **
          L.is_valid_finished lfin fin **
          pts_to handshake_out handshake_bytes **
          pts_to network_out network_bytes **
          pure (B.length handshake_bytes == 36 /\
                Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished fin)) /\
                WS.parse_tls_message T.Handshake handshake_bytes ==
                  Some (M.TlsHandshake (M.Finished fin)) /\
                B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == 58 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.ApplicationData 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.ApplicationData, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.ApplicationData outer_fragment) /\
                   Seq.equal
                     (CS.record_header_aad raw_prefix)
                     (CS.application_data_record_header 53) /\
                   R.seal
                     'record_write
                     (CS.record_header_aad raw_prefix)
                     {
                       R.content_type = T.ApplicationData;
                       R.fragment =
                         CS.sent_tls_inner_plaintext_fragment
                           (M.TlsHandshake (M.Finished fin));
                     } ==
                     Some (outer_fragment, R.next_seq 'record_write))))
{
  with fin. assert (L.is_valid_finished lfin fin);
  assert (pure (Some? (R.seal
    'record_write
    (CS.application_data_record_header 53)
    {
      R.content_type = T.ApplicationData;
      R.fragment =
        CS.sent_tls_inner_plaintext_fragment
          (M.TlsHandshake (M.Finished fin));
    })));
  let erased_fin = Ghost.hide fin;
  let handshake_written =
    serialize_finished_handshake #erased_fin lfin handshake_out 36sz;
  with handshake_bytes. assert (pts_to handshake_out handshake_bytes);
  assert (pure (SZ.v handshake_written == 36));
  assert (pure (Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished fin))));

  let mut inner_plaintext = [| 0uy; 37sz |];
  encode_inner_plaintext_no_padding_slice
    handshake_out
    36sz
    0sz
    36sz
    22uy
    inner_plaintext
    37sz;
  with inner_plaintext_bytes. assert (pts_to inner_plaintext inner_plaintext_bytes);
  assert (pure (B.length inner_plaintext_bytes == 37));
  assert (pure (L.content_type_matches 22uy T.Handshake));
  lemma_slice_all handshake_bytes;
  Seq.lemma_eq_elim (Seq.slice handshake_bytes 0 36) handshake_bytes;
  assert (pure (Seq.equal
    (Seq.slice handshake_bytes 0 36)
    (WS.serialize_handshake (M.Finished fin))));
  assert (pure (Seq.equal
    inner_plaintext_bytes
    (WS.serialize_plaintext {
      M.content_type = T.Handshake;
      M.fragment = Seq.slice handshake_bytes 0 36;
    })));
  Seq.lemma_eq_elim
    (Seq.slice handshake_bytes 0 36)
    (WS.serialize_handshake (M.Finished fin));
  assert (pure (Seq.equal
    inner_plaintext_bytes
    (WS.serialize_plaintext {
      M.content_type = T.Handshake;
      M.fragment = WS.serialize_handshake (M.Finished fin);
    })));
  WSRD.lemma_serialize_tls_message_handshake (M.Finished fin);
  assert (pure (Seq.equal
    inner_plaintext_bytes
    (CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (M.Finished fin)))));

  let mut aad = [| 0uy; 5sz |];
  serialize_application_data_header 53sz aad 5sz;
  with aad_bytes. assert (pts_to aad aad_bytes);
  assert (pure (Seq.equal aad_bytes (CS.application_data_record_header 53)));

  let mut ciphertext = [| 0uy; 53sz |];
  let sealed =
    Rec.seal_application_no_update
      write_state
      aad
      5sz
      inner_plaintext
      37sz
      ciphertext;
  with ciphertext_bytes. _;
  if sealed {
    assert (pure (R.seal
      'record_write
      aad_bytes
      { R.content_type = T.ApplicationData; R.fragment = inner_plaintext_bytes } ==
      Some (ciphertext_bytes, R.next_seq 'record_write)));
    let written =
      serialize_raw_application_data_record ciphertext 53sz network_out network_out_len;
    with network_bytes. assert (pts_to network_out network_bytes);
    assert (pure (SZ.v written == 58));
    assert (pure (B.length network_bytes == SZ.v network_out_len));
    assert (pure (CS.raw_records_exactly (Seq.slice network_bytes 0 58) T.ApplicationData 1));
    assert (pure (Seq.equal
      (CS.record_header_aad (Seq.slice network_bytes 0 58))
      (CS.application_data_record_header 53)));
    written
  } else {
    assert (pure False);
    0sz
  }
}

fn serialize_server_hello_from_selection
  (#sh: erased M.server_hello)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                B.length (Ghost.reveal sh).M.body == 0 /\
                SZ.v out_len == 90)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 90 /\
               SZ.v written == 90 /\
               Seq.equal out_bytes
                (WS.serialize_server_hello_from_selection (Ghost.reveal sh)) /\
               Seq.equal out_bytes
                (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  let written = SerSH.serialize_server_hello_from_selection #sh lsh out out_len #old_bytes;
  with out_bytes. assert (pts_to out out_bytes);
  WS.lemma_fixed_server_handshake_serializers
    (Ghost.reveal sh)
    { M.chain = []; M.body = B.empty }
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty; M.body = B.empty }
    { M.verify_data = Seq.create 32 0uy };
  Seq.lemma_eq_elim
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))));
  written
}

fn serialize_server_hello_record_from_selection
  (#sh: erased M.server_hello)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                B.length (Ghost.reveal sh).M.body == 0 /\
                SZ.v out_len == 95)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 95 /\
               SZ.v written == 95 /\
               Seq.equal out_bytes
                 (WS.serialize_record
                   T.Handshake
                   (WS.serialize_server_hello_from_selection (Ghost.reveal sh))) /\
               Seq.equal out_bytes
                (CS.serialized_cleartext_tls_message
                  (M.TlsHandshake (M.ServerHello (Ghost.reveal sh)))) /\
               WS.parse_record out_bytes ==
                 Some
                   (T.Handshake,
                    WS.serialize_server_hello_from_selection (Ghost.reveal sh),
                    95) /\
               CS.raw_records_exactly out_bytes T.Handshake 1)
{
  let written = SerSH.serialize_server_hello_record_from_selection #sh lsh out out_len #old_bytes;
  with out_bytes. assert (pts_to out out_bytes);
  WS.lemma_fixed_server_handshake_serializers
    (Ghost.reveal sh)
    { M.chain = []; M.body = B.empty }
    { M.scheme = T.RsaPssRsaeSha256; M.signature = B.empty; M.body = B.empty }
    { M.verify_data = Seq.create 32 0uy };
  Seq.lemma_eq_elim
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  WSR.lemma_serialize_record_reveal
    T.Handshake
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  WSRD.lemma_serialize_tls_message_handshake (M.ServerHello (Ghost.reveal sh));
  assert (pure (Seq.equal
    out_bytes
    (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ServerHello (Ghost.reveal sh))))));
  written
}

fn serialize_empty_encrypted_extensions
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v out_len == 6)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to out out_bytes **
          pure (B.length out_bytes == 6 /\
               SZ.v written == 6 /\
               Seq.equal out_bytes (WS.serialize_empty_encrypted_extensions ()))
{
  SerEE.serialize_empty_encrypted_extensions out out_len #old_bytes
}

fn serialize_certificate_from_credential
  (#cert: erased M.certificate_msg)
  (lcert: L.certificate_msg)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 lcert.L.certificate_msg_cert_count == 1sz /\
                 (exists (certificate:B.bytes).
                   (Ghost.reveal cert).M.chain == [certificate]) /\
                 SZ.v out_len == B.length (WS.serialize_certificate_from_credential (Ghost.reveal cert)))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                 (WS.serialize_certificate_from_credential (Ghost.reveal cert)))
{
  SerCert.serialize_certificate_from_credential #cert lcert out out_len #old_bytes
}

fn serialize_certificate_verify_from_signature
  (#cv: erased M.certificate_verify)
  (lcv: L.certificate_verify)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v out_len == B.length (WS.serialize_certificate_verify_from_signature (Ghost.reveal cv)))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                 (WS.serialize_certificate_verify_from_signature (Ghost.reveal cv)))
{
  SerCV.serialize_certificate_verify_from_signature #cv lcv out out_len #old_bytes
}

fn serialize_server_finished
  (#fin: erased M.finished)
  (lfin: L.finished)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 36 /\
               SZ.v written == 36 /\
               Seq.equal out_bytes
                 (WS.serialize_server_finished (Ghost.reveal fin)) /\
               WS.parse_tls_message T.Handshake out_bytes ==
                 Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  SerFin.serialize_server_finished #fin lfin out out_len #old_bytes
}

#push-options "--z3rlimit 100"
fn write_client_hello_common_extensions
  (key_share_src: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (off: SZ.t)
  requires pts_to key_share_src 'key_share **
           pts_to out 'old_out **
           pure (B.length 'key_share == 32 /\
                 B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 512 /\
                 SZ.v off + 65 <= SZ.v out_len)
  ensures exists* out_bytes.
          pts_to key_share_src 'key_share **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                Seq.equal
                  (CL.raw_slice out_bytes 0 (SZ.v off))
                  (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off)) /\
                Seq.equal
                  (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 65))
                  (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share)))
{
  assert (pure (SZ.v off + 65 <= 512));
  SZ.fits_lte (SZ.v off + 65) 512;
  pts_to_len out;
  (out).(off) <- 0uy;

  SZ.fits_lte (SZ.v off + 1) (SZ.v off + 65);
  let off_1 = off `SZ.add` 1sz;
  (out).(off_1) <- 0x0auy;
  SZ.fits_lte (SZ.v off + 2) (SZ.v off + 65);
  let off_2 = off `SZ.add` 2sz;
  (out).(off_2) <- 0uy;
  SZ.fits_lte (SZ.v off + 3) (SZ.v off + 65);
  let off_3 = off `SZ.add` 3sz;
  (out).(off_3) <- 4uy;
  SZ.fits_lte (SZ.v off + 4) (SZ.v off + 65);
  let off_4 = off `SZ.add` 4sz;
  (out).(off_4) <- 0uy;
  SZ.fits_lte (SZ.v off + 5) (SZ.v off + 65);
  let off_5 = off `SZ.add` 5sz;
  (out).(off_5) <- 2uy;
  SZ.fits_lte (SZ.v off + 6) (SZ.v off + 65);
  let off_6 = off `SZ.add` 6sz;
  (out).(off_6) <- 0uy;
  SZ.fits_lte (SZ.v off + 7) (SZ.v off + 65);
  let off_7 = off `SZ.add` 7sz;
  (out).(off_7) <- 0x1duy;
  with out_after_supported_groups. assert (pts_to out out_after_supported_groups);
  assert (pure (Seq.equal
    (CL.raw_slice out_after_supported_groups 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_supported_groups (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));

  SZ.fits_lte (SZ.v off + 8) (SZ.v off + 65);
  let off_8 = off `SZ.add` 8sz;
  (out).(off_8) <- 0uy;
  SZ.fits_lte (SZ.v off + 9) (SZ.v off + 65);
  let off_9 = off `SZ.add` 9sz;
  (out).(off_9) <- 0x0duy;
  SZ.fits_lte (SZ.v off + 10) (SZ.v off + 65);
  let off_10 = off `SZ.add` 10sz;
  (out).(off_10) <- 0uy;
  SZ.fits_lte (SZ.v off + 11) (SZ.v off + 65);
  let off_11 = off `SZ.add` 11sz;
  (out).(off_11) <- 4uy;
  SZ.fits_lte (SZ.v off + 12) (SZ.v off + 65);
  let off_12 = off `SZ.add` 12sz;
  (out).(off_12) <- 0uy;
  SZ.fits_lte (SZ.v off + 13) (SZ.v off + 65);
  let off_13 = off `SZ.add` 13sz;
  (out).(off_13) <- 2uy;
  SZ.fits_lte (SZ.v off + 14) (SZ.v off + 65);
  let off_14 = off `SZ.add` 14sz;
  (out).(off_14) <- 0x08uy;
  SZ.fits_lte (SZ.v off + 15) (SZ.v off + 65);
  let off_15 = off `SZ.add` 15sz;
  (out).(off_15) <- 0x04uy;
  with out_after_signature_algorithms. assert (pts_to out out_after_signature_algorithms);
  assert (pure (Seq.equal
    (CL.raw_slice out_after_signature_algorithms 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_signature_algorithms (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_signature_algorithms (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])));

  SZ.fits_lte (SZ.v off + 16) (SZ.v off + 65);
  let off_16 = off `SZ.add` 16sz;
  (out).(off_16) <- 0uy;
  SZ.fits_lte (SZ.v off + 17) (SZ.v off + 65);
  let off_17 = off `SZ.add` 17sz;
  (out).(off_17) <- 0x33uy;
  SZ.fits_lte (SZ.v off + 18) (SZ.v off + 65);
  let off_18 = off `SZ.add` 18sz;
  (out).(off_18) <- 0uy;
  SZ.fits_lte (SZ.v off + 19) (SZ.v off + 65);
  let off_19 = off `SZ.add` 19sz;
  pts_to_len out;
  (out).(off_19) <- 38uy;
  SZ.fits_lte (SZ.v off + 20) (SZ.v off + 65);
  let off_20 = off `SZ.add` 20sz;
  (out).(off_20) <- 0uy;
  SZ.fits_lte (SZ.v off + 21) (SZ.v off + 65);
  let off_21 = off `SZ.add` 21sz;
  (out).(off_21) <- 36uy;
  SZ.fits_lte (SZ.v off + 22) (SZ.v off + 65);
  let off_22 = off `SZ.add` 22sz;
  (out).(off_22) <- 0uy;
  SZ.fits_lte (SZ.v off + 23) (SZ.v off + 65);
  let off_23 = off `SZ.add` 23sz;
  (out).(off_23) <- 0x1duy;
  SZ.fits_lte (SZ.v off + 24) (SZ.v off + 65);
  let off_24 = off `SZ.add` 24sz;
  (out).(off_24) <- 0uy;
  SZ.fits_lte (SZ.v off + 25) (SZ.v off + 65);
  let off_25 = off `SZ.add` 25sz;
  (out).(off_25) <- 32uy;
  with out_after_key_share_header. assert (pts_to out out_after_key_share_header);
  assert (pure (Seq.equal
    (CL.raw_slice out_after_key_share_header 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_key_share_header (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_key_share_header (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_after_key_share_header (SZ.v off + 16) (SZ.v off + 26))
    (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])));
  SZ.fits_lte (SZ.v off + 26) (SZ.v off + 65);
  let key_share_off = off `SZ.add` 26sz;

  SZ.fits_lte (SZ.v off + 58) (SZ.v off + 65);
  let off_58 = off `SZ.add` 58sz;
  (out).(off_58) <- 0uy;
  SZ.fits_lte (SZ.v off + 59) (SZ.v off + 65);
  let off_59 = off `SZ.add` 59sz;
  (out).(off_59) <- 0x2buy;
  SZ.fits_lte (SZ.v off + 60) (SZ.v off + 65);
  let off_60 = off `SZ.add` 60sz;
  (out).(off_60) <- 0uy;
  SZ.fits_lte (SZ.v off + 61) (SZ.v off + 65);
  let off_61 = off `SZ.add` 61sz;
  (out).(off_61) <- 3uy;
  SZ.fits_lte (SZ.v off + 62) (SZ.v off + 65);
  let off_62 = off `SZ.add` 62sz;
  (out).(off_62) <- 2uy;
  SZ.fits_lte (SZ.v off + 63) (SZ.v off + 65);
  let off_63 = off `SZ.add` 63sz;
  (out).(off_63) <- 0x03uy;
  SZ.fits_lte (SZ.v off + 64) (SZ.v off + 65);
  let off_64 = off `SZ.add` 64sz;
  assert (pure (SZ.v off_64 < SZ.v out_len));
  (out).(off_64) <- 0x04uy;
  assert (pure (SZ.v off_64 == SZ.v off + 64));
  with out_before_key_share_copy. assert (pts_to out out_before_key_share_copy);
  pts_to_len out;
  assert (pure (B.length out_before_key_share_copy == SZ.v out_len));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_16) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_17) == 0x33uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_18) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_19) == 38uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_20) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_21) == 36uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_22) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_23) == 0x1duy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_24) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_25) == 32uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_58) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_59) == 0x2buy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_60) == 0uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_61) == 3uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_62) == 2uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_63) == 0x03uy));
  assert (pure (Seq.index out_before_key_share_copy (SZ.v off_64) == 0x04uy));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_key_share_copy (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_key_share_copy (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_key_share_copy (SZ.v off + 16) (SZ.v off + 26))
    (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_key_share_copy 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  let frozen_out_before_key_share_copy = Ghost.hide out_before_key_share_copy;
  assert (pure (B.length (Ghost.reveal frozen_out_before_key_share_copy) == SZ.v out_len));
  copy_array_slice_to_array
    key_share_src
    32sz
    0sz
    32sz
    out
    out_len
    key_share_off;
  with out_bytes. assert (pts_to out out_bytes);
  pts_to_len out;
  WSR.lemma_client_hello_common_extensions_len (Ghost.reveal 'key_share);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'key_share) 0 32) == 32));
  assert (pure (B.length (Ghost.reveal frozen_out_before_key_share_copy) == SZ.v out_len));
  lemma_copy_expr_preserves_prefix_slice
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    0
    (SZ.v off);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) 0 (SZ.v off));
  assert (pure (Seq.equal
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 0 (SZ.v off))
    (CL.raw_slice (Ghost.reveal 'old_out) 0 (SZ.v off))));
  lemma_copy_expr_preserves_prefix_slice
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off)
    (SZ.v off + 8);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 8))
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off) (SZ.v off + 8));
  assert (pure (Seq.equal
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])));
  lemma_copy_expr_preserves_prefix_slice
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off + 8)
    (SZ.v off + 16);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 16))
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 8) (SZ.v off + 16));
  assert (pure (Seq.equal
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])));
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'key_share) 0 32) == 32));
  assert (pure (B.length (Ghost.reveal frozen_out_before_key_share_copy) == SZ.v out_len));
  lemma_copy_expr_preserves_prefix_slice
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off + 16)
    (SZ.v off + 26);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 26))
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_16) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_17) == 0x33uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_18) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_19) == 38uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_20) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_21) == 36uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_22) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_23) == 0x1duy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_24) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_25) == 32uy));
  assert (pure (Seq.length (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26)) == 10));
  assert (pure (SZ.v off_16 == SZ.v off + 16));
  assert (pure (SZ.v off_17 == (SZ.v off + 16) + 1));
  assert (pure (SZ.v off_18 == (SZ.v off + 16) + 2));
  assert (pure (SZ.v off_19 == (SZ.v off + 16) + 3));
  assert (pure (SZ.v off_20 == (SZ.v off + 16) + 4));
  assert (pure (SZ.v off_21 == (SZ.v off + 16) + 5));
  assert (pure (SZ.v off_22 == (SZ.v off + 16) + 6));
  assert (pure (SZ.v off_23 == (SZ.v off + 16) + 7));
  assert (pure (SZ.v off_24 == (SZ.v off + 16) + 8));
  assert (pure (SZ.v off_25 == (SZ.v off + 16) + 9));
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 0;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 1;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 2;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 3;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 4;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 5;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 6;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 7;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 8;
  lemma_raw_slice_index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26) 9;
  lemma_eq_key_share_header_bytes
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off + 16) (SZ.v off + 26))
    (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 26))
    (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])));
  assert (pure (SZ.v key_share_off == SZ.v off + 26));
  assert (pure (SZ.v key_share_off + 32 == SZ.v off + 58));
  lemma_copy_expr_copied_slice
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 26) (SZ.v off + 58))
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32);
  lemma_raw_slice_all (Ghost.reveal 'key_share);
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (Ghost.reveal 'key_share);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 26) (SZ.v off + 58))
    (Ghost.reveal 'key_share)));
  SeqP.append_slices
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 26))
    (CL.raw_slice out_bytes (SZ.v off + 26) (SZ.v off + 58));
  CL.lemma_raw_slice_split out_bytes (SZ.v off + 16) (SZ.v off + 26) (SZ.v off + 58);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 26))
    (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 26) (SZ.v off + 58))
    (Ghost.reveal 'key_share);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 58))
    (B.append
      (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Ghost.reveal 'key_share))));
  assert (pure (SZ.v off + 65 <= B.length out_bytes));
  assert (pure (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65) ==
                Seq.slice out_bytes (SZ.v off + 58) (SZ.v off + 65)));
  Seq.lemma_len_slice out_bytes (SZ.v off + 58) (SZ.v off + 65);
  assert (pure (Seq.length (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) == 7));
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'key_share) 0 32) == 32));
  assert (pure (B.length (Ghost.reveal frozen_out_before_key_share_copy) == SZ.v out_len));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_58) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_59) == 0x2buy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_60) == 0uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_61) == 3uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_62) == 2uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_63) == 0x03uy));
  assert (pure (Seq.index (Ghost.reveal frozen_out_before_key_share_copy) (SZ.v off_64) == 0x04uy));
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_58);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_59);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_60);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_61);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_62);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_63);
  lemma_copy_expr_preserves_suffix_index
    (Ghost.reveal frozen_out_before_key_share_copy)
    (CL.raw_slice (Ghost.reveal 'key_share) 0 32)
    (SZ.v key_share_off)
    32
    (SZ.v out_len)
    (SZ.v off_64);
  assert (pure (Seq.index out_bytes (SZ.v off_58) == 0uy));
  assert (pure (Seq.index out_bytes (SZ.v off_59) == 0x2buy));
  assert (pure (Seq.index out_bytes (SZ.v off_60) == 0uy));
  assert (pure (Seq.index out_bytes (SZ.v off_61) == 3uy));
  assert (pure (Seq.index out_bytes (SZ.v off_62) == 2uy));
  assert (pure (Seq.index out_bytes (SZ.v off_63) == 0x03uy));
  assert (pure (Seq.index out_bytes (SZ.v off_64) == 0x04uy));
  assert (pure (SZ.v off_58 == SZ.v off + 58));
  assert (pure (SZ.v off_59 == (SZ.v off + 58) + 1));
  assert (pure (SZ.v off_60 == (SZ.v off + 58) + 2));
  assert (pure (SZ.v off_61 == (SZ.v off + 58) + 3));
  assert (pure (SZ.v off_62 == (SZ.v off + 58) + 4));
  assert (pure (SZ.v off_63 == (SZ.v off + 58) + 5));
  assert (pure (SZ.v off_64 == (SZ.v off + 58) + 6));
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 0;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 1;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 2;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 3;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 4;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 5;
  lemma_raw_slice_index out_bytes (SZ.v off + 58) (SZ.v off + 65) 6;
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 0 == 0uy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 1 == 0x2buy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 2 == 0uy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 3 == 3uy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 4 == 2uy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 5 == 0x03uy));
  assert (pure (Seq.index (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65)) 6 == 0x04uy));
  lemma_eq_supported_versions_bytes (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65));
  let versions_bytes = SeqP.createL [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy];
  assert (pure (versions_bytes == B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]));
  assert (pure (B.length versions_bytes == 7));
  assert (pure (Seq.index versions_bytes 0 == 0uy));
  assert (pure (Seq.index versions_bytes 1 == 0x2buy));
  assert (pure (Seq.index versions_bytes 2 == 0uy));
  assert (pure (Seq.index versions_bytes 3 == 3uy));
  assert (pure (Seq.index versions_bytes 4 == 2uy));
  assert (pure (Seq.index versions_bytes 5 == 0x03uy));
  assert (pure (Seq.index versions_bytes 6 == 0x04uy));
  Seq.lemma_eq_elim
    versions_bytes
    (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65))
    (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])));
  SeqP.append_slices
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 58))
    (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65));
  CL.lemma_raw_slice_split out_bytes (SZ.v off + 16) (SZ.v off + 58) (SZ.v off + 65);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 58))
    (B.append
      (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Ghost.reveal 'key_share));
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 58) (SZ.v off + 65))
    (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 65))
    (B.append
      (B.append
        (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Ghost.reveal 'key_share))
      (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))));
  SeqP.append_slices
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 16))
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 65));
  CL.lemma_raw_slice_split out_bytes (SZ.v off + 8) (SZ.v off + 16) (SZ.v off + 65);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 16))
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 16) (SZ.v off + 65))
    (B.append
      (B.append
        (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Ghost.reveal 'key_share))
      (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 65))
    (B.append
      (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
      (B.append
        (B.append
          (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          (Ghost.reveal 'key_share))
        (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])))));
  SeqP.append_slices
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 8))
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 65));
  CL.lemma_raw_slice_split out_bytes (SZ.v off) (SZ.v off + 8) (SZ.v off + 65);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 8))
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v off + 8) (SZ.v off + 65))
    (B.append
      (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
      (B.append
        (B.append
          (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          (Ghost.reveal 'key_share))
        (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])));
  WSR.lemma_client_hello_common_extensions_bytes_reveal (Ghost.reveal 'key_share);
  assert (pure (Seq.equal
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share))
    (B.append
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
      (B.append
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
        (B.append
          (B.append
            (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            (Ghost.reveal 'key_share))
          (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))))));
  Seq.lemma_eq_elim
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share))
    (B.append
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
      (B.append
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
        (B.append
          (B.append
            (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            (Ghost.reveal 'key_share))
          (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))));
  assert (pure (Seq.length (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 65)) == 65));
  assert (pure (forall (i:nat). i < 65 ==>
    Seq.index (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 65)) i ==
    Seq.index (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share)) i));
  Seq.lemma_eq_intro
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 65))
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v off) (SZ.v off + 65))
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share))))
}
#pop-options

fn write_client_hello_sni_and_common_extensions
  (server_name_src: array U8.t)
  (key_share_src: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (hostname_len: SZ.t)
  requires pts_to server_name_src 'server_name **
           pts_to key_share_src 'key_share **
           pts_to out 'old_out **
           pure (B.length 'server_name == 255 /\
                 B.length 'key_share == 32 /\
                 B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 512 /\
                 0 < SZ.v hostname_len /\
                 SZ.v hostname_len <= 255)
  ensures exists* out_bytes.
          pts_to server_name_src 'server_name **
          pts_to key_share_src 'key_share **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                Seq.equal
                  (CL.raw_slice out_bytes 0 47)
                  (CL.raw_slice (Ghost.reveal 'old_out) 0 47) /\
                Seq.equal
                  (CL.raw_slice out_bytes 47 (SZ.v hostname_len + 121))
                  (WSR.client_hello_extensions_bytes
                    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
                    (Ghost.reveal 'key_share)))
{
  assert (pure (SZ.v hostname_len + 5 <= 260));
  SZ.fits_lte (SZ.v hostname_len + 5) 260;
  assert (pure (SZ.v hostname_len + 3 <= 258));
  SZ.fits_lte (SZ.v hostname_len + 3) 258;
  pts_to_len out;
  (out).(47sz) <- 0uy;
  (out).(48sz) <- 0uy;
  let sni_data_len = hostname_len `SZ.add` 5sz;
  (out).(49sz) <- u8_of_sizet (SZ.div sni_data_len 256sz);
  (out).(50sz) <- u8_of_sizet sni_data_len;
  let sni_list_len = hostname_len `SZ.add` 3sz;
  (out).(51sz) <- u8_of_sizet (SZ.div sni_list_len 256sz);
  (out).(52sz) <- u8_of_sizet sni_list_len;
  pts_to_len out;
  (out).(53sz) <- 0uy;
  (out).(54sz) <- u8_of_sizet (SZ.div hostname_len 256sz);
  (out).(55sz) <- u8_of_sizet hostname_len;
  copy_array_slice_to_array
    server_name_src
    255sz
    0sz
    hostname_len
    out
    out_len
    56sz;
  assert (pure (SZ.v hostname_len + 56 <= 311));
  SZ.fits_lte (SZ.v hostname_len + 56) 311;
  let common_extensions_off = hostname_len `SZ.add` 56sz;
  assert (pure (SZ.v common_extensions_off + 65 <= 512));
  assert (pure (SZ.v common_extensions_off == SZ.v hostname_len + 56));
  with out_before_common_extensions. assert (pts_to out out_before_common_extensions);
  assert (pure (B.length out_before_common_extensions == SZ.v out_len));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_common_extensions 0 47)
    (CL.raw_slice (Ghost.reveal 'old_out) 0 47)));
  assert (pure (B.length (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)) ==
    SZ.v hostname_len));
  lemma_client_hello_byte_eq ((5 + SZ.v hostname_len) / 256);
  lemma_client_hello_byte_eq (5 + SZ.v hostname_len);
  lemma_client_hello_byte_eq ((3 + SZ.v hostname_len) / 256);
  lemma_client_hello_byte_eq (3 + SZ.v hostname_len);
  lemma_client_hello_byte_eq (SZ.v hostname_len / 256);
  lemma_client_hello_byte_eq (SZ.v hostname_len);
  WSR.lemma_client_hello_byte_v ((5 + SZ.v hostname_len) / 256);
  WSR.lemma_client_hello_byte_v (5 + SZ.v hostname_len);
  WSR.lemma_client_hello_byte_v ((3 + SZ.v hostname_len) / 256);
  WSR.lemma_client_hello_byte_v (3 + SZ.v hostname_len);
  WSR.lemma_client_hello_byte_v (SZ.v hostname_len / 256);
  WSR.lemma_client_hello_byte_v (SZ.v hostname_len);
  assert (pure (u8_of_sizet (SZ.div sni_data_len 256sz) ==
    WSR.client_hello_byte ((5 + SZ.v hostname_len) / 256)));
  assert (pure (u8_of_sizet sni_data_len ==
    WSR.client_hello_byte (5 + SZ.v hostname_len)));
  assert (pure (u8_of_sizet (SZ.div sni_list_len 256sz) ==
    WSR.client_hello_byte ((3 + SZ.v hostname_len) / 256)));
  assert (pure (u8_of_sizet sni_list_len ==
    WSR.client_hello_byte (3 + SZ.v hostname_len)));
  assert (pure (u8_of_sizet (SZ.div hostname_len 256sz) ==
    WSR.client_hello_byte (SZ.v hostname_len / 256)));
  assert (pure (u8_of_sizet hostname_len ==
    WSR.client_hello_byte (SZ.v hostname_len)));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_common_extensions 47 56)
    (B.of_list [
      0uy; 0uy;
      WSR.client_hello_byte ((5 + SZ.v hostname_len) / 256);
      WSR.client_hello_byte (5 + SZ.v hostname_len);
      WSR.client_hello_byte ((3 + SZ.v hostname_len) / 256);
      WSR.client_hello_byte (3 + SZ.v hostname_len);
      0uy;
      WSR.client_hello_byte (SZ.v hostname_len / 256);
      WSR.client_hello_byte (SZ.v hostname_len)])));
  lemma_copy_expr_copied_slice
    (Ghost.reveal 'old_out)
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
    56
    (SZ.v hostname_len)
    (SZ.v out_len);
  assert (pure (Seq.equal
    (CL.raw_slice out_before_common_extensions 56 (SZ.v common_extensions_off))
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))));
  SeqP.append_slices
    (CL.raw_slice out_before_common_extensions 47 56)
    (CL.raw_slice out_before_common_extensions 56 (SZ.v common_extensions_off));
  CL.lemma_raw_slice_split out_before_common_extensions 47 56 (SZ.v common_extensions_off);
  WSR.lemma_client_hello_server_name_extension_bytes_reveal
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len));
  Seq.lemma_eq_elim
    (CL.raw_slice out_before_common_extensions 47 56)
    (B.of_list [
      0uy; 0uy;
      WSR.client_hello_byte ((5 + SZ.v hostname_len) / 256);
      WSR.client_hello_byte (5 + SZ.v hostname_len);
      WSR.client_hello_byte ((3 + SZ.v hostname_len) / 256);
      WSR.client_hello_byte (3 + SZ.v hostname_len);
      0uy;
      WSR.client_hello_byte (SZ.v hostname_len / 256);
      WSR.client_hello_byte (SZ.v hostname_len)]);
  Seq.lemma_eq_elim
    (CL.raw_slice out_before_common_extensions 56 (SZ.v common_extensions_off))
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len));
  assert (pure (Seq.equal
    (CL.raw_slice out_before_common_extensions 47 (SZ.v common_extensions_off))
    (WSR.client_hello_server_name_extension_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)))));
  write_client_hello_common_extensions
    key_share_src
    out
    out_len
    common_extensions_off;
  with out_bytes. assert (pts_to out out_bytes);
  pts_to_len out;
  WSR.lemma_client_hello_server_name_extension_len
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len));
  WSR.lemma_client_hello_common_extensions_len (Ghost.reveal 'key_share);
  WSR.lemma_client_hello_extensions_len
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
    (Ghost.reveal 'key_share);
  assert (pure (B.length out_bytes == SZ.v out_len));
  lemma_equal_prefix_raw_slice
    out_bytes
    out_before_common_extensions
    (SZ.v common_extensions_off)
    0
    47;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 0 47)
    (CL.raw_slice out_before_common_extensions 0 47);
  Seq.lemma_eq_elim
    (CL.raw_slice out_before_common_extensions 0 47)
    (CL.raw_slice (Ghost.reveal 'old_out) 0 47);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 0 47)
    (CL.raw_slice (Ghost.reveal 'old_out) 0 47)));
  lemma_equal_prefix_raw_slice
    out_bytes
    out_before_common_extensions
    (SZ.v common_extensions_off)
    47
    (SZ.v common_extensions_off);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 47 (SZ.v hostname_len + 56))
    (WSR.client_hello_server_name_extension_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)))));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes (SZ.v hostname_len + 56) (SZ.v hostname_len + 121))
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share))));
  SeqP.append_slices
    (CL.raw_slice out_bytes 47 (SZ.v hostname_len + 56))
    (CL.raw_slice out_bytes (SZ.v hostname_len + 56) (SZ.v hostname_len + 121));
  CL.lemma_raw_slice_split out_bytes 47 (SZ.v hostname_len + 56) (SZ.v hostname_len + 121);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 47 (SZ.v hostname_len + 56))
    (WSR.client_hello_server_name_extension_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)));
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (SZ.v hostname_len + 56) (SZ.v hostname_len + 121))
    (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share));
  WSR.lemma_client_hello_extensions_bytes_shape
    (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
    (Ghost.reveal 'key_share);
  assert (pure (Seq.equal
    (WSR.client_hello_extensions_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
      (Ghost.reveal 'key_share))
    (B.append
      (WSR.client_hello_server_name_extension_bytes
        (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)))
      (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share)))));
  Seq.lemma_eq_elim
    (WSR.client_hello_extensions_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
      (Ghost.reveal 'key_share))
    (B.append
      (WSR.client_hello_server_name_extension_bytes
        (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len)))
      (WSR.client_hello_common_extensions_bytes (Ghost.reveal 'key_share)));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 47 (SZ.v hostname_len + 121))
    (WSR.client_hello_extensions_bytes
      (CL.raw_slice (Ghost.reveal 'server_name) 0 (SZ.v hostname_len))
      (Ghost.reveal 'key_share))))
}

#push-options "--z3rlimit 100"
fn serialize_client_hello_from_start
  (#start: erased CS.handshake_start)
  (#ch: erased M.client_hello)
  (start_random: V.vec U8.t)
  (start_server_name: V.vec U8.t)
  (start_server_name_len: box SZ.t)
  (start_key_share: V.vec U8.t)
  (start_cipher_suites: V.vec U16.t)
  (start_cipher_suites_len: box SZ.t)
  (start_signature_schemes: V.vec U16.t)
  (start_signature_schemes_len: box SZ.t)
  (client_hello_present: box bool)
  (l: L.client_hello)
  (client_hello_bytes: V.vec U8.t)
  (client_hello_bytes_len: box SZ.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  requires exists* random server_name server_name_len key_share
                  cipher_suites cipher_suites_len
                  signature_schemes signature_schemes_len
                  old_present old_l_random old_l_server_name old_l_key_share
                  old_l_cipher_suites old_l_signature_schemes
                  old_client_hello_bytes_len old_client_hello_bytes old_network_out.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present old_present **
          V.pts_to l.L.client_hello_random old_l_random **
          V.pts_to l.L.client_hello_server_name old_l_server_name **
          V.pts_to l.L.client_hello_key_share old_l_key_share **
          V.pts_to l.L.client_hello_cipher_suites old_l_cipher_suites **
          V.pts_to l.L.client_hello_signature_schemes old_l_signature_schemes **
          V.pts_to client_hello_bytes old_client_hello_bytes **
          Box.pts_to client_hello_bytes_len old_client_hello_bytes_len **
          pts_to network_out old_network_out **
          pure (old_present == false /\
                V.is_full_vec start_random /\
                V.is_full_vec start_server_name /\
                V.is_full_vec start_key_share /\
                V.is_full_vec start_cipher_suites /\
                V.is_full_vec start_signature_schemes /\
                V.is_full_vec l.L.client_hello_random /\
                V.is_full_vec l.L.client_hello_server_name /\
                V.is_full_vec l.L.client_hello_key_share /\
                V.is_full_vec l.L.client_hello_cipher_suites /\
                V.is_full_vec l.L.client_hello_signature_schemes /\
                V.is_full_vec client_hello_bytes /\
                V.length start_random == 32 /\
                V.length start_server_name == L.max_server_name_len /\
                V.length start_key_share == 32 /\
                V.length start_cipher_suites == L.max_cipher_suites /\
                V.length start_signature_schemes == L.max_signature_schemes /\
                V.length l.L.client_hello_random == 32 /\
                V.length l.L.client_hello_server_name == L.max_server_name_len /\
                V.length l.L.client_hello_key_share == 32 /\
                V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
                V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
                V.length client_hello_bytes == 512 /\
                B.length random == 32 /\
                B.length server_name == L.max_server_name_len /\
                B.length key_share == 32 /\
                Seq.length cipher_suites == L.max_cipher_suites /\
                Seq.length signature_schemes == L.max_signature_schemes /\
                B.length old_l_random == 32 /\
                B.length old_l_server_name == L.max_server_name_len /\
                B.length old_l_key_share == 32 /\
                Seq.length old_l_cipher_suites == L.max_cipher_suites /\
                Seq.length old_l_signature_schemes == L.max_signature_schemes /\
                B.length old_client_hello_bytes == 512 /\
                B.length old_network_out == SZ.v network_out_len /\
                517 <= SZ.v network_out_len /\
                SZ.v server_name_len <= B.length server_name /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                Seq.equal random (Ghost.reveal start).CS.start_client_random /\
                B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
                Seq.equal (Ghost.reveal start).CS.start_server_name (Seq.slice server_name 0 (SZ.v server_name_len)) /\
                Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
                L.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  (Ghost.reveal start).CS.start_cipher_suites /\
                L.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  (Ghost.reveal start).CS.start_signature_schemes /\
                Ghost.reveal ch == {
                  M.random = (Ghost.reveal start).CS.start_client_random;
                  M.server_name = Some (Ghost.reveal start).CS.start_server_name;
                  M.key_share = (Ghost.reveal start).CS.start_client_key_share_public;
                  M.cipher_suites = (Ghost.reveal start).CS.start_cipher_suites;
                  M.signature_schemes = (Ghost.reveal start).CS.start_signature_schemes;
                })
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* random server_name server_name_len key_share
                 cipher_suites cipher_suites_len
                 signature_schemes signature_schemes_len
                 handshake_bytes network_out_bytes handshake_len.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present true **
          V.pts_to l.L.client_hello_random random **
          V.pts_to l.L.client_hello_server_name server_name **
          V.pts_to l.L.client_hello_key_share key_share **
          V.pts_to l.L.client_hello_cipher_suites cipher_suites **
          V.pts_to l.L.client_hello_signature_schemes signature_schemes **
          V.pts_to client_hello_bytes handshake_bytes **
          Box.pts_to client_hello_bytes_len handshake_len **
          pts_to network_out network_out_bytes **
          pure (V.is_full_vec start_random /\
               V.is_full_vec start_server_name /\
               V.is_full_vec start_key_share /\
               V.is_full_vec start_cipher_suites /\
               V.is_full_vec start_signature_schemes /\
               V.is_full_vec l.L.client_hello_random /\
               V.is_full_vec l.L.client_hello_server_name /\
               V.is_full_vec l.L.client_hello_key_share /\
               V.is_full_vec l.L.client_hello_cipher_suites /\
               V.is_full_vec l.L.client_hello_signature_schemes /\
               V.is_full_vec client_hello_bytes /\
               V.length start_random == 32 /\
               V.length start_server_name == L.max_server_name_len /\
               V.length start_key_share == 32 /\
               V.length start_cipher_suites == L.max_cipher_suites /\
               V.length start_signature_schemes == L.max_signature_schemes /\
               V.length l.L.client_hello_random == 32 /\
               V.length l.L.client_hello_server_name == L.max_server_name_len /\
               V.length l.L.client_hello_key_share == 32 /\
               V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
               V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
               V.length client_hello_bytes == 512 /\
               B.length random == 32 /\
               B.length server_name == L.max_server_name_len /\
               B.length key_share == 32 /\
               Seq.length cipher_suites == L.max_cipher_suites /\
               Seq.length signature_schemes == L.max_signature_schemes /\
               B.length handshake_bytes == 512 /\
               B.length network_out_bytes == SZ.v network_out_len /\
               SZ.v server_name_len <= B.length server_name /\
               SZ.v cipher_suites_len <= Seq.length cipher_suites /\
               SZ.v signature_schemes_len <= Seq.length signature_schemes /\
               Seq.equal random (Ghost.reveal start).CS.start_client_random /\
               B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
               Seq.equal (Ghost.reveal start).CS.start_server_name (CL.raw_slice server_name 0 (SZ.v server_name_len)) /\
               Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Ghost.reveal start).CS.start_cipher_suites /\
               L.signature_schemes_match
                 signature_schemes
                 (SZ.v signature_schemes_len)
                 (Ghost.reveal start).CS.start_signature_schemes /\
               Seq.equal random (Ghost.reveal ch).M.random /\
               L.optional_byte_prefix_matches
                 true
                 server_name
                 server_name_len
                 (Ghost.reveal ch).M.server_name /\
               Seq.equal key_share (Ghost.reveal ch).M.key_share /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Ghost.reveal ch).M.cipher_suites /\
               L.signature_schemes_match
                 signature_schemes
                 (SZ.v signature_schemes_len)
                 (Ghost.reveal ch).M.signature_schemes /\
               SZ.v handshake_len == B.length (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))) /\
               SZ.v handshake_len <= B.length handshake_bytes /\
               Seq.equal
                 (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
                 (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))) /\
               SZ.v written ==
                 B.length (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch)))) /\
               5 <= SZ.v written /\
               SZ.v written <= B.length network_out_bytes /\
               Seq.equal
                 (CL.raw_slice network_out_bytes 0 (SZ.v written))
                 (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch)))) /\
               WS.parse_record (CL.raw_slice network_out_bytes 0 (SZ.v written)) ==
                 Some
                   (T.Handshake,
                    WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)),
                    SZ.v written) /\
               CS.raw_records_exactly
                 (CL.raw_slice network_out_bytes 0 (SZ.v written))
                 T.Handshake
                 1)
{
  with random. assert (V.pts_to start_random random);
  with server_name. assert (V.pts_to start_server_name server_name);
  with server_name_len. assert (Box.pts_to start_server_name_len server_name_len);
  with key_share. assert (V.pts_to start_key_share key_share);
  with cipher_suites. assert (V.pts_to start_cipher_suites cipher_suites);
  with cipher_suites_len. assert (Box.pts_to start_cipher_suites_len cipher_suites_len);
  with signature_schemes. assert (V.pts_to start_signature_schemes signature_schemes);
  with signature_schemes_len. assert (Box.pts_to start_signature_schemes_len signature_schemes_len);
  with old_present. assert (Box.pts_to client_hello_present old_present);
  with old_l_random. assert (V.pts_to l.L.client_hello_random old_l_random);
  with old_l_server_name. assert (V.pts_to l.L.client_hello_server_name old_l_server_name);
  with old_l_key_share. assert (V.pts_to l.L.client_hello_key_share old_l_key_share);
  with old_l_cipher_suites. assert (V.pts_to l.L.client_hello_cipher_suites old_l_cipher_suites);
  with old_l_signature_schemes. assert (V.pts_to l.L.client_hello_signature_schemes old_l_signature_schemes);
  with old_client_hello_bytes_len. assert (Box.pts_to client_hello_bytes_len old_client_hello_bytes_len);
  with old_client_hello_bytes. assert (V.pts_to client_hello_bytes old_client_hello_bytes);
  with old_network_out. assert (pts_to network_out old_network_out);

  let hostname_len = !start_server_name_len;
  let cipher_suites_len_runtime = !start_cipher_suites_len;
  let signature_schemes_len_runtime = !start_signature_schemes_len;
  assert (pure (hostname_len == server_name_len));
  assert (pure (cipher_suites_len_runtime == cipher_suites_len));
  assert (pure (signature_schemes_len_runtime == signature_schemes_len));
  assert (pure (SZ.v hostname_len <= 255));

  assert (pure (SZ.v hostname_len + 9 <= 264));
  SZ.fits_lte (SZ.v hostname_len + 9) 264;
  let sni_extension_len =
    (if hostname_len = 0sz then 0sz else hostname_len `SZ.add` 9sz);
  assert (pure (SZ.v sni_extension_len ==
    (if SZ.v hostname_len == 0 then 0 else 9 + SZ.v hostname_len)));
  assert (pure (SZ.v sni_extension_len <= 264));
  assert (pure (SZ.v sni_extension_len + 65 <= 329));
  SZ.fits_lte (SZ.v sni_extension_len + 65) 329;
  let extensions_len = sni_extension_len `SZ.add` 65sz;
  assert (pure (SZ.v extensions_len == 65 + SZ.v sni_extension_len));
  assert (pure (SZ.v extensions_len <= 329));
  assert (pure (SZ.v extensions_len + 43 <= 372));
  SZ.fits_lte (SZ.v extensions_len + 43) 372;
  let body_len = extensions_len `SZ.add` 43sz;
  assert (pure (SZ.v body_len == 43 + SZ.v extensions_len));
  assert (pure (SZ.v body_len <= 372));
  assert (pure (SZ.v body_len + 4 <= 376));
  SZ.fits_lte (SZ.v body_len + 4) 376;
  let handshake_len = body_len `SZ.add` 4sz;
  assert (pure (SZ.v handshake_len == 4 + SZ.v body_len));
  assert (pure (SZ.v handshake_len <= 376));
  assert (pure (SZ.v handshake_len <= 512));
  assert (pure (SZ.v handshake_len + 5 <= 381));
  SZ.fits_lte (SZ.v handshake_len + 5) 381;
  let record_len = handshake_len `SZ.add` 5sz;
  assert (pure (SZ.v record_len == 5 + SZ.v handshake_len));
  assert (pure (SZ.v record_len <= SZ.v network_out_len));

  copy_vec_to_vec_u8 start_random l.L.client_hello_random 32sz;
  copy_vec_to_vec_u8 start_server_name l.L.client_hello_server_name 255sz;
  copy_vec_to_vec_u8 start_key_share l.L.client_hello_key_share 32sz;
  copy_vec_to_vec_u16 start_cipher_suites l.L.client_hello_cipher_suites 16sz;
  copy_vec_to_vec_u16 start_signature_schemes l.L.client_hello_signature_schemes 16sz;

  V.to_array_pts_to client_hello_bytes;
  V.to_array_pts_to start_random;
  V.to_array_pts_to start_server_name;
  V.to_array_pts_to start_key_share;

  (V.vec_to_array client_hello_bytes).(0sz) <- 1uy;
  u8_of_sizet_div2_byte body_len;
  (V.vec_to_array client_hello_bytes).(1sz) <- u8_of_sizet (SZ.div (SZ.div body_len 256sz) 256sz);
  (V.vec_to_array client_hello_bytes).(2sz) <- u8_of_sizet (SZ.div body_len 256sz);
  (V.vec_to_array client_hello_bytes).(3sz) <- u8_of_sizet body_len;
  (V.vec_to_array client_hello_bytes).(4sz) <- 0x03uy;
  (V.vec_to_array client_hello_bytes).(5sz) <- 0x03uy;
  copy_array_slice_to_array
    (V.vec_to_array start_random)
    32sz
    0sz
    32sz
    (V.vec_to_array client_hello_bytes)
    512sz
    6sz;
  (V.vec_to_array client_hello_bytes).(38sz) <- 0uy;
  (V.vec_to_array client_hello_bytes).(39sz) <- 0uy;
  (V.vec_to_array client_hello_bytes).(40sz) <- 2uy;
  (V.vec_to_array client_hello_bytes).(41sz) <- 0x13uy;
  (V.vec_to_array client_hello_bytes).(42sz) <- 0x03uy;
  (V.vec_to_array client_hello_bytes).(43sz) <- 1uy;
  (V.vec_to_array client_hello_bytes).(44sz) <- 0uy;
  (V.vec_to_array client_hello_bytes).(45sz) <- u8_of_sizet (SZ.div extensions_len 256sz);
  (V.vec_to_array client_hello_bytes).(46sz) <- u8_of_sizet extensions_len;
  with client_hello_prefix. assert (pts_to (V.vec_to_array client_hello_bytes) client_hello_prefix);
  pts_to_len (V.vec_to_array client_hello_bytes);
  assert (pure (B.length client_hello_prefix == 512));
  WSR.lemma_client_hello_prefix_bytes_reveal
    (SZ.v body_len)
    (SZ.v extensions_len)
    random;
  u8_of_sizet_v_byte (SZ.div body_len 256sz);
  u8_of_sizet_v_byte body_len;
  u8_of_sizet_v_byte (SZ.div extensions_len 256sz);
  u8_of_sizet_v_byte extensions_len;
  assert (pure (SZ.v (SZ.div body_len 256sz) == SZ.v body_len / 256));
  assert (pure (SZ.v (SZ.div extensions_len 256sz) == SZ.v extensions_len / 256));
  lemma_client_hello_byte_eq (SZ.v body_len / 65536);
  lemma_client_hello_byte_eq (SZ.v body_len / 256);
  lemma_client_hello_byte_eq (SZ.v body_len);
  lemma_client_hello_byte_eq (SZ.v extensions_len / 256);
  lemma_client_hello_byte_eq (SZ.v extensions_len);
  assert (pure (Seq.equal
    (CL.raw_slice client_hello_prefix 0 47)
    (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)));

  let hostname_is_empty = hostname_len = 0sz;
  if hostname_is_empty {
    write_client_hello_common_extensions
      (V.vec_to_array start_key_share)
      (V.vec_to_array client_hello_bytes)
      512sz
      47sz;
    with out_common. assert (pts_to (V.vec_to_array client_hello_bytes) out_common);
    assert (pure (B.length out_common == 512));
    assert (pure (SZ.v extensions_len == 65));
    assert (pure (SZ.v body_len == 108));
    assert (pure (SZ.v handshake_len == 112));
    WSR.lemma_client_hello_common_extensions_len key_share;
    WSR.lemma_client_hello_extensions_len
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share;
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 47)
      (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 47 (SZ.v handshake_len))
      (WSR.client_hello_common_extensions_bytes key_share)));
    SeqP.append_slices
      (CL.raw_slice out_common 0 47)
      (CL.raw_slice out_common 47 (SZ.v handshake_len));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (B.append
        (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)
        (WSR.client_hello_common_extensions_bytes key_share))));
    assert (pure (B.length (CL.raw_slice server_name 0 (SZ.v server_name_len)) == 0));
    WSR.lemma_client_hello_server_name_extension_bytes_empty
      (CL.raw_slice server_name 0 (SZ.v server_name_len));
    WSR.lemma_client_hello_extensions_bytes_shape
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share;
    Seq.lemma_eq_elim
      (WSR.client_hello_server_name_extension_bytes
        (CL.raw_slice server_name 0 (SZ.v server_name_len)))
      B.empty;
    assert (pure (Seq.equal
      (WSR.client_hello_extensions_bytes
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)
      (WSR.client_hello_common_extensions_bytes key_share)));
    WSR.lemma_client_hello_handshake_bytes_prefix
      random
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share;
    Seq.lemma_eq_elim
      (WSR.client_hello_extensions_bytes
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)
      (WSR.client_hello_common_extensions_bytes key_share);
    assert (pure (B.length (WSR.client_hello_extensions_bytes
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share) == SZ.v extensions_len));
    assert (pure (43 + B.length (WSR.client_hello_extensions_bytes
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share) == SZ.v body_len));
    Seq.lemma_eq_elim
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)
      (B.append
        (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)
        (WSR.client_hello_common_extensions_bytes key_share));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)));

    client_hello_bytes_len := handshake_len;
    network_out.(0sz) <- 22uy;
    network_out.(1sz) <- 0x03uy;
    network_out.(2sz) <- 0x03uy;
    with network_after_record_version. assert (pts_to network_out network_after_record_version);
    assert (pure (Seq.index network_after_record_version 0 == 22uy));
    assert (pure (Seq.index network_after_record_version 1 == 0x03uy));
    assert (pure (Seq.index network_after_record_version 2 == 0x03uy));
    network_out.(3sz) <- u8_of_sizet (SZ.div handshake_len 256sz);
    with network_after_len_hi. assert (pts_to network_out network_after_len_hi);
    Seq.lemma_index_upd1 network_after_record_version 3 (byte (SZ.v handshake_len / 256));
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 0;
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 1;
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 2;
    assert (pure (Seq.index network_after_len_hi 0 == 22uy));
    assert (pure (Seq.index network_after_len_hi 1 == 0x03uy));
    assert (pure (Seq.index network_after_len_hi 2 == 0x03uy));
    assert (pure (Seq.index network_after_len_hi 3 == byte (SZ.v handshake_len / 256)));
    network_out.(4sz) <- u8_of_sizet handshake_len;
    with network_header_bytes. assert (pts_to network_out network_header_bytes);
    Seq.lemma_index_upd1 network_after_len_hi 4 (byte (SZ.v handshake_len));
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 0;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 1;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 2;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 3;
    assert (pure (B.length network_header_bytes == SZ.v network_out_len));
    lemma_handshake_record_header_bytes (SZ.v handshake_len);
    Seq.lemma_len_slice network_header_bytes 0 5;
    assert (pure (Seq.length (CL.raw_slice network_header_bytes 0 5) == 5));
    assert (pure (B.length (handshake_record_header_bytes (SZ.v handshake_len)) == 5));
    lemma_handshake_record_header_indices (SZ.v handshake_len);
    lemma_raw_slice_index network_header_bytes 0 5 0;
    lemma_raw_slice_index network_header_bytes 0 5 1;
    lemma_raw_slice_index network_header_bytes 0 5 2;
    lemma_raw_slice_index network_header_bytes 0 5 3;
    lemma_raw_slice_index network_header_bytes 0 5 4;
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 3 == byte (SZ.v handshake_len / 256)));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 4 == byte (SZ.v handshake_len)));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 0 == 22uy));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 1 == 0x03uy));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 2 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 0 == 22uy));
    assert (pure (Seq.index network_header_bytes 1 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 2 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 3 == byte (SZ.v handshake_len / 256)));
    assert (pure (Seq.index network_header_bytes 4 == byte (SZ.v handshake_len)));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 0 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 0));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 1 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 1));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 2 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 2));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 3 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 3));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 4 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 4));
    lemma_eq_handshake_record_header_from_indices
      (CL.raw_slice network_header_bytes 0 5)
      (SZ.v handshake_len);
    copy_array_slice_to_array
      (V.vec_to_array client_hello_bytes)
      512sz
      0sz
      handshake_len
      network_out
      network_out_len
      5sz;
    client_hello_present := true;

    V.to_vec_pts_to start_random;
    V.to_vec_pts_to start_server_name;
    V.to_vec_pts_to start_key_share;
    V.to_vec_pts_to client_hello_bytes;

    with handshake_bytes. assert (V.pts_to client_hello_bytes handshake_bytes);
    with network_out_bytes. assert (pts_to network_out network_out_bytes);
    V.pts_to_len client_hello_bytes;
    pts_to_len network_out;
    assert (pure (B.length handshake_bytes == 512));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v handshake_len <= B.length handshake_bytes));
    assert (pure (SZ.v record_len == B.length (Seq.slice network_out_bytes 0 (SZ.v record_len))));
    assert (pure (Seq.equal random (Ghost.reveal ch).M.random));
    assert (pure (Seq.equal key_share (Ghost.reveal ch).M.key_share));
    assert (pure (CL.raw_slice server_name 0 (SZ.v server_name_len) ==
      Seq.slice server_name 0 (SZ.v server_name_len)));
    assert (pure (L.optional_byte_prefix_matches
      true
      server_name
      server_name_len
      (Ghost.reveal ch).M.server_name));
    assert (pure (V.is_full_vec start_random));
    assert (pure (V.is_full_vec start_server_name));
    assert (pure (V.is_full_vec start_key_share));
    assert (pure (V.is_full_vec start_cipher_suites));
    assert (pure (V.is_full_vec start_signature_schemes));
    assert (pure (V.is_full_vec l.L.client_hello_random));
    assert (pure (V.is_full_vec l.L.client_hello_server_name));
    assert (pure (V.is_full_vec l.L.client_hello_key_share));
    assert (pure (V.is_full_vec l.L.client_hello_cipher_suites));
    assert (pure (V.is_full_vec l.L.client_hello_signature_schemes));
    assert (pure (V.is_full_vec client_hello_bytes));
    assert (pure (V.length start_random == 32));
    assert (pure (V.length start_server_name == L.max_server_name_len));
    assert (pure (V.length start_key_share == 32));
    assert (pure (V.length start_cipher_suites == L.max_cipher_suites));
    assert (pure (V.length start_signature_schemes == L.max_signature_schemes));
    assert (pure (V.length l.L.client_hello_random == 32));
    assert (pure (V.length l.L.client_hello_server_name == L.max_server_name_len));
    assert (pure (V.length l.L.client_hello_key_share == 32));
    assert (pure (V.length l.L.client_hello_cipher_suites == L.max_cipher_suites));
    assert (pure (V.length l.L.client_hello_signature_schemes == L.max_signature_schemes));
    assert (pure (V.length client_hello_bytes == 512));
    assert (pure (B.length random == 32));
    assert (pure (B.length server_name == L.max_server_name_len));
    assert (pure (B.length key_share == 32));
    assert (pure (Seq.length cipher_suites == L.max_cipher_suites));
    assert (pure (Seq.length signature_schemes == L.max_signature_schemes));
    assert (pure (SZ.v server_name_len <= B.length server_name));
    assert (pure (SZ.v cipher_suites_len <= Seq.length cipher_suites));
    assert (pure (SZ.v signature_schemes_len <= Seq.length signature_schemes));
    assert (pure (Seq.equal random (Ghost.reveal start).CS.start_client_random));
    assert (pure (B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len));
    assert (pure (Seq.equal
      (Ghost.reveal start).CS.start_server_name
      (CL.raw_slice server_name 0 (SZ.v server_name_len))));
    assert (pure (Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public));
    assert (pure (L.cipher_suites_match cipher_suites (SZ.v cipher_suites_len) (Ghost.reveal start).CS.start_cipher_suites));
    assert (pure (L.signature_schemes_match signature_schemes (SZ.v signature_schemes_len) (Ghost.reveal start).CS.start_signature_schemes));
    assert (pure (L.cipher_suites_match cipher_suites (SZ.v cipher_suites_len) (Ghost.reveal ch).M.cipher_suites));
    assert (pure (L.signature_schemes_match signature_schemes (SZ.v signature_schemes_len) (Ghost.reveal ch).M.signature_schemes));
    assert (pure (Seq.equal
      (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)));
    Seq.lemma_eq_elim random (Ghost.reveal ch).M.random;
    Seq.lemma_eq_elim key_share (Ghost.reveal ch).M.key_share;
    Seq.lemma_eq_elim
      (Ghost.reveal start).CS.start_server_name
      (CL.raw_slice server_name 0 (SZ.v server_name_len));
    assert (pure ((Ghost.reveal ch).M.server_name ==
      Some (CL.raw_slice server_name 0 (SZ.v server_name_len))));
    WSR.lemma_client_hello_handshake_bytes_reveal (Ghost.reveal ch);
    WSR.lemma_serialize_client_hello_reveal (Ghost.reveal ch);
    assert (pure (SZ.v handshake_len ==
      B.length (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    assert (pure (Seq.equal
      (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    WSRD.lemma_serialize_tls_message_handshake (M.ClientHello (Ghost.reveal ch));
    WSR.lemma_serialize_record_reveal
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (SZ.v record_len ==
      B.length (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    SeqP.append_slices
      (CL.raw_slice network_header_bytes 0 5)
      (B.append
        (CL.raw_slice out_common 0 (SZ.v handshake_len))
        (CL.raw_slice network_header_bytes (5 + SZ.v handshake_len) (SZ.v network_out_len)));
    SeqP.append_slices
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (CL.raw_slice network_header_bytes (5 + SZ.v handshake_len) (SZ.v network_out_len));
    assert (pure (B.length (CL.raw_slice out_common 0 (SZ.v handshake_len)) == SZ.v handshake_len));
    lemma_copy_expr_preserves_prefix_slice
      network_header_bytes
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      5
      (SZ.v handshake_len)
      (SZ.v network_out_len)
      0
      5;
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 0 5)
      (CL.raw_slice network_header_bytes 0 5);
    lemma_copy_expr_copied_slice
      network_header_bytes
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      5
      (SZ.v handshake_len)
      (SZ.v network_out_len);
    assert (pure (SZ.v record_len == 5 + SZ.v handshake_len));
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 5 (SZ.v record_len))
      (CL.raw_slice out_common 0 (SZ.v handshake_len));
    CL.lemma_raw_slice_split network_out_bytes 0 5 (SZ.v record_len);
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 0 5)
      (CL.raw_slice network_header_bytes 0 5);
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 5 (SZ.v record_len))
      (CL.raw_slice out_common 0 (SZ.v handshake_len));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (B.append
        (CL.raw_slice network_header_bytes 0 5)
        (CL.raw_slice out_common 0 (SZ.v handshake_len)))));
    Seq.lemma_eq_elim
      (CL.raw_slice network_header_bytes 0 5)
      (WSR.serialize_record_header T.Handshake (SZ.v handshake_len));
    Seq.lemma_eq_elim
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (B.append
        (WSR.serialize_record_header T.Handshake (SZ.v handshake_len))
        (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (WS.serialize_record T.Handshake (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    WS.lemma_parse_record_serialize_record
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (WS.parse_record (CL.raw_slice network_out_bytes 0 (SZ.v record_len)) ==
      Some
        (T.Handshake,
         WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)),
         SZ.v record_len)));
    CSL.lemma_parse_record_full_raw_records_exactly
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (CS.raw_records_exactly
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      T.Handshake
      1));
    record_len
  } else {
    assert (pure (0 < SZ.v hostname_len));
    write_client_hello_sni_and_common_extensions
      (V.vec_to_array start_server_name)
      (V.vec_to_array start_key_share)
      (V.vec_to_array client_hello_bytes)
      512sz
      hostname_len;
    with out_common. assert (pts_to (V.vec_to_array client_hello_bytes) out_common);
    assert (pure (B.length out_common == 512));
    assert (pure (SZ.v extensions_len == 74 + SZ.v hostname_len));
    assert (pure (SZ.v body_len == 117 + SZ.v hostname_len));
    assert (pure (SZ.v handshake_len == 121 + SZ.v hostname_len));
    WSR.lemma_client_hello_extensions_len
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share;
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 47)
      (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 47 (SZ.v handshake_len))
      (WSR.client_hello_extensions_bytes
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)));
    SeqP.append_slices
      (CL.raw_slice out_common 0 47)
      (CL.raw_slice out_common 47 (SZ.v handshake_len));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (B.append
        (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)
        (WSR.client_hello_extensions_bytes
          (CL.raw_slice server_name 0 (SZ.v server_name_len))
          key_share))));
    WSR.lemma_client_hello_handshake_bytes_prefix
      random
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share;
    assert (pure (B.length (WSR.client_hello_extensions_bytes
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share) == SZ.v extensions_len));
    assert (pure (43 + B.length (WSR.client_hello_extensions_bytes
      (CL.raw_slice server_name 0 (SZ.v server_name_len))
      key_share) == SZ.v body_len));
    Seq.lemma_eq_elim
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)
      (B.append
        (WSR.client_hello_prefix_bytes (SZ.v body_len) (SZ.v extensions_len) random)
        (WSR.client_hello_extensions_bytes
          (CL.raw_slice server_name 0 (SZ.v server_name_len))
          key_share));
    assert (pure (Seq.equal
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)));

    client_hello_bytes_len := handshake_len;
    network_out.(0sz) <- 22uy;
    network_out.(1sz) <- 0x03uy;
    network_out.(2sz) <- 0x03uy;
    with network_after_record_version. assert (pts_to network_out network_after_record_version);
    assert (pure (Seq.index network_after_record_version 0 == 22uy));
    assert (pure (Seq.index network_after_record_version 1 == 0x03uy));
    assert (pure (Seq.index network_after_record_version 2 == 0x03uy));
    network_out.(3sz) <- u8_of_sizet (SZ.div handshake_len 256sz);
    with network_after_len_hi. assert (pts_to network_out network_after_len_hi);
    Seq.lemma_index_upd1 network_after_record_version 3 (byte (SZ.v handshake_len / 256));
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 0;
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 1;
    Seq.lemma_index_upd2 network_after_record_version 3 (byte (SZ.v handshake_len / 256)) 2;
    assert (pure (Seq.index network_after_len_hi 0 == 22uy));
    assert (pure (Seq.index network_after_len_hi 1 == 0x03uy));
    assert (pure (Seq.index network_after_len_hi 2 == 0x03uy));
    assert (pure (Seq.index network_after_len_hi 3 == byte (SZ.v handshake_len / 256)));
    network_out.(4sz) <- u8_of_sizet handshake_len;
    with network_header_bytes. assert (pts_to network_out network_header_bytes);
    Seq.lemma_index_upd1 network_after_len_hi 4 (byte (SZ.v handshake_len));
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 0;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 1;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 2;
    Seq.lemma_index_upd2 network_after_len_hi 4 (byte (SZ.v handshake_len)) 3;
    assert (pure (B.length network_header_bytes == SZ.v network_out_len));
    lemma_handshake_record_header_bytes (SZ.v handshake_len);
    Seq.lemma_len_slice network_header_bytes 0 5;
    assert (pure (Seq.length (CL.raw_slice network_header_bytes 0 5) == 5));
    assert (pure (B.length (handshake_record_header_bytes (SZ.v handshake_len)) == 5));
    lemma_handshake_record_header_indices (SZ.v handshake_len);
    lemma_raw_slice_index network_header_bytes 0 5 0;
    lemma_raw_slice_index network_header_bytes 0 5 1;
    lemma_raw_slice_index network_header_bytes 0 5 2;
    lemma_raw_slice_index network_header_bytes 0 5 3;
    lemma_raw_slice_index network_header_bytes 0 5 4;
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 3 == byte (SZ.v handshake_len / 256)));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 4 == byte (SZ.v handshake_len)));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 0 == 22uy));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 1 == 0x03uy));
    assert (pure (Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 2 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 0 == 22uy));
    assert (pure (Seq.index network_header_bytes 1 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 2 == 0x03uy));
    assert (pure (Seq.index network_header_bytes 3 == byte (SZ.v handshake_len / 256)));
    assert (pure (Seq.index network_header_bytes 4 == byte (SZ.v handshake_len)));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 0 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 0));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 1 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 1));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 2 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 2));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 3 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 3));
    assert (pure (Seq.index (CL.raw_slice network_header_bytes 0 5) 4 == Seq.index (handshake_record_header_bytes (SZ.v handshake_len)) 4));
    lemma_eq_handshake_record_header_from_indices
      (CL.raw_slice network_header_bytes 0 5)
      (SZ.v handshake_len);
    copy_array_slice_to_array
      (V.vec_to_array client_hello_bytes)
      512sz
      0sz
      handshake_len
      network_out
      network_out_len
      5sz;
    client_hello_present := true;

    V.to_vec_pts_to start_random;
    V.to_vec_pts_to start_server_name;
    V.to_vec_pts_to start_key_share;
    V.to_vec_pts_to client_hello_bytes;

    with handshake_bytes. assert (V.pts_to client_hello_bytes handshake_bytes);
    with network_out_bytes. assert (pts_to network_out network_out_bytes);
    V.pts_to_len client_hello_bytes;
    pts_to_len network_out;
    assert (pure (B.length handshake_bytes == 512));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v handshake_len <= B.length handshake_bytes));
    assert (pure (SZ.v record_len == B.length (Seq.slice network_out_bytes 0 (SZ.v record_len))));
    assert (pure (Seq.equal random (Ghost.reveal ch).M.random));
    assert (pure (Seq.equal key_share (Ghost.reveal ch).M.key_share));
    assert (pure (CL.raw_slice server_name 0 (SZ.v server_name_len) ==
      Seq.slice server_name 0 (SZ.v server_name_len)));
    assert (pure (L.optional_byte_prefix_matches
      true
      server_name
      server_name_len
      (Ghost.reveal ch).M.server_name));
    assert (pure (V.is_full_vec start_random));
    assert (pure (V.is_full_vec start_server_name));
    assert (pure (V.is_full_vec start_key_share));
    assert (pure (V.is_full_vec start_cipher_suites));
    assert (pure (V.is_full_vec start_signature_schemes));
    assert (pure (V.is_full_vec l.L.client_hello_random));
    assert (pure (V.is_full_vec l.L.client_hello_server_name));
    assert (pure (V.is_full_vec l.L.client_hello_key_share));
    assert (pure (V.is_full_vec l.L.client_hello_cipher_suites));
    assert (pure (V.is_full_vec l.L.client_hello_signature_schemes));
    assert (pure (V.is_full_vec client_hello_bytes));
    assert (pure (V.length start_random == 32));
    assert (pure (V.length start_server_name == L.max_server_name_len));
    assert (pure (V.length start_key_share == 32));
    assert (pure (V.length start_cipher_suites == L.max_cipher_suites));
    assert (pure (V.length start_signature_schemes == L.max_signature_schemes));
    assert (pure (V.length l.L.client_hello_random == 32));
    assert (pure (V.length l.L.client_hello_server_name == L.max_server_name_len));
    assert (pure (V.length l.L.client_hello_key_share == 32));
    assert (pure (V.length l.L.client_hello_cipher_suites == L.max_cipher_suites));
    assert (pure (V.length l.L.client_hello_signature_schemes == L.max_signature_schemes));
    assert (pure (V.length client_hello_bytes == 512));
    assert (pure (B.length random == 32));
    assert (pure (B.length server_name == L.max_server_name_len));
    assert (pure (B.length key_share == 32));
    assert (pure (Seq.length cipher_suites == L.max_cipher_suites));
    assert (pure (Seq.length signature_schemes == L.max_signature_schemes));
    assert (pure (SZ.v server_name_len <= B.length server_name));
    assert (pure (SZ.v cipher_suites_len <= Seq.length cipher_suites));
    assert (pure (SZ.v signature_schemes_len <= Seq.length signature_schemes));
    assert (pure (Seq.equal random (Ghost.reveal start).CS.start_client_random));
    assert (pure (B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len));
    assert (pure (Seq.equal
      (Ghost.reveal start).CS.start_server_name
      (CL.raw_slice server_name 0 (SZ.v server_name_len))));
    assert (pure (Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public));
    assert (pure (L.cipher_suites_match cipher_suites (SZ.v cipher_suites_len) (Ghost.reveal start).CS.start_cipher_suites));
    assert (pure (L.signature_schemes_match signature_schemes (SZ.v signature_schemes_len) (Ghost.reveal start).CS.start_signature_schemes));
    assert (pure (L.cipher_suites_match cipher_suites (SZ.v cipher_suites_len) (Ghost.reveal ch).M.cipher_suites));
    assert (pure (L.signature_schemes_match signature_schemes (SZ.v signature_schemes_len) (Ghost.reveal ch).M.signature_schemes));
    assert (pure (Seq.equal
      (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
      (WSR.client_hello_handshake_bytes
        random
        (CL.raw_slice server_name 0 (SZ.v server_name_len))
        key_share)));
    Seq.lemma_eq_elim random (Ghost.reveal ch).M.random;
    Seq.lemma_eq_elim key_share (Ghost.reveal ch).M.key_share;
    Seq.lemma_eq_elim
      (Ghost.reveal start).CS.start_server_name
      (CL.raw_slice server_name 0 (SZ.v server_name_len));
    assert (pure ((Ghost.reveal ch).M.server_name ==
      Some (CL.raw_slice server_name 0 (SZ.v server_name_len))));
    WSR.lemma_client_hello_handshake_bytes_reveal (Ghost.reveal ch);
    WSR.lemma_serialize_client_hello_reveal (Ghost.reveal ch);
    assert (pure (SZ.v handshake_len ==
      B.length (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    assert (pure (Seq.equal
      (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
    WSRD.lemma_serialize_tls_message_handshake (M.ClientHello (Ghost.reveal ch));
    WSR.lemma_serialize_record_reveal
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (SZ.v record_len ==
      B.length (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    SeqP.append_slices
      (CL.raw_slice network_header_bytes 0 5)
      (B.append
        (CL.raw_slice out_common 0 (SZ.v handshake_len))
        (CL.raw_slice network_header_bytes (5 + SZ.v handshake_len) (SZ.v network_out_len)));
    SeqP.append_slices
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (CL.raw_slice network_header_bytes (5 + SZ.v handshake_len) (SZ.v network_out_len));
    assert (pure (B.length (CL.raw_slice out_common 0 (SZ.v handshake_len)) == SZ.v handshake_len));
    lemma_copy_expr_preserves_prefix_slice
      network_header_bytes
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      5
      (SZ.v handshake_len)
      (SZ.v network_out_len)
      0
      5;
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 0 5)
      (CL.raw_slice network_header_bytes 0 5);
    lemma_copy_expr_copied_slice
      network_header_bytes
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      5
      (SZ.v handshake_len)
      (SZ.v network_out_len);
    assert (pure (SZ.v record_len == 5 + SZ.v handshake_len));
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 5 (SZ.v record_len))
      (CL.raw_slice out_common 0 (SZ.v handshake_len));
    CL.lemma_raw_slice_split network_out_bytes 0 5 (SZ.v record_len);
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 0 5)
      (CL.raw_slice network_header_bytes 0 5);
    Seq.lemma_eq_elim
      (CL.raw_slice network_out_bytes 5 (SZ.v record_len))
      (CL.raw_slice out_common 0 (SZ.v handshake_len));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (B.append
        (CL.raw_slice network_header_bytes 0 5)
        (CL.raw_slice out_common 0 (SZ.v handshake_len)))));
    Seq.lemma_eq_elim
      (CL.raw_slice network_header_bytes 0 5)
      (WSR.serialize_record_header T.Handshake (SZ.v handshake_len));
    Seq.lemma_eq_elim
      (CL.raw_slice out_common 0 (SZ.v handshake_len))
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (B.append
        (WSR.serialize_record_header T.Handshake (SZ.v handshake_len))
        (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (WS.serialize_record T.Handshake (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))))));
    assert (pure (Seq.equal
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));
    WS.lemma_parse_record_serialize_record
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (WS.parse_record (CL.raw_slice network_out_bytes 0 (SZ.v record_len)) ==
      Some
        (T.Handshake,
         WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)),
         SZ.v record_len)));
    CSL.lemma_parse_record_full_raw_records_exactly
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      T.Handshake
      (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));
    assert (pure (CS.raw_records_exactly
      (CL.raw_slice network_out_bytes 0 (SZ.v record_len))
      T.Handshake
      1));
    record_len
  }
}
#pop-options
