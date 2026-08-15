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
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ref = Pulse.Lib.Reference
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
module Rev = TLS13.Wire.Spec.Reveal.Handshake
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GCS = TLS13.Wire.Generated.CipherSuite
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module GHS = TLS13.Wire.Generated.Handshake
module SerH = TLS13.Impl.Serializer.Handshake

noextract
let byte (n:nat) : B.byte =
  U8.uint_to_t (n % 256)

(* Machine-native low byte of a [SZ.t]: extract [n mod 256] entirely in machine
   integers (sizet -> uint32 -> uint8), with no detour through mathematical
   integer runtime helpers at the wire-length byte-split sites. *)
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

let write_u16_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 256); byte n]

let write_u24_bytes (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 65536); byte (n / 256); byte n]

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
  with (
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
  with (
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
  with (
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
  with (
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
  with (
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
  with (
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
  with (
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
  with (
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
  | T.Invalid ->
      assert (U8.v wire == 0x00);
      WSR.lemma_content_type_byte_value T.Invalid;
      assert (U8.v (WSR.content_type_byte T.Invalid) == 0x00);
      U8.v_inj wire (WSR.content_type_byte T.Invalid);
      assert (wire == WSR.content_type_byte ct)
  | T.Change_cipher_spec ->
      assert (ct == T.Change_cipher_spec);
      assert (U8.v wire == 0x14);
      WSR.lemma_content_type_byte_value T.Change_cipher_spec;
      assert (U8.v (WSR.content_type_byte T.Change_cipher_spec) == 0x14);
      U8.v_inj wire (WSR.content_type_byte T.Change_cipher_spec);
      assert (wire == WSR.content_type_byte T.Change_cipher_spec);
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
  | T.Application_data ->
      assert (ct == T.Application_data);
      assert (U8.v wire == 0x17);
      WSR.lemma_content_type_byte_value T.Application_data;
      assert (U8.v (WSR.content_type_byte T.Application_data) == 0x17);
      U8.v_inj wire (WSR.content_type_byte T.Application_data);
      assert (wire == WSR.content_type_byte T.Application_data);
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
  with (
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
    decreases (34 - SZ.v (Ref.read i))
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
  (#fin: erased GFin.finished)
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
  SerFin.serialize_server_finished #fin lfin handshake_out handshake_out_len
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
                  (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record_header (Ghost.reveal header_bytes) ==
                  Some (T.Application_data, SZ.v fragment_len))
{
  SerPR.serialize_application_data_header fragment_len out out_len
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
                Seq.equal raw_prefix (WS.serialize_record T.Application_data (Ghost.reveal 'fragment_bytes)) /\
                Seq.equal
                  (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                  (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record raw_prefix ==
                  Some (T.Application_data, (Ghost.reveal 'fragment_bytes), SZ.v written) /\
                CS.raw_records_exactly raw_prefix T.Application_data 1))
{
  SerPR.serialize_raw_application_data_record
    fragment fragment_len out out_len
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
                   (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v handshake_len + 17))
                   {
                     R.content_type = T.Application_data;
                     R.fragment =
                       TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
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
                CS.raw_records_exactly raw_prefix T.Application_data 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.Application_data, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.Application_data outer_fragment) /\
                   Seq.equal
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v handshake_len + 17)) /\
                   R.seal
                     (Ghost.reveal record_write)
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     {
                       R.content_type = T.Application_data;
                       R.fragment =
                         TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
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
               (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)
               {
                 R.content_type = T.Application_data;
                 R.fragment =
                   TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
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
                CS.raw_records_exactly raw_prefix T.Application_data 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.Application_data, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.Application_data outer_fragment) /\
                   Seq.equal
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53) /\
                   R.seal
                     'record_write
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     {
                       R.content_type = T.Application_data;
                       R.fragment =
                         TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
                           (M.TlsHandshake (M.Finished fin));
                     } ==
                     Some (outer_fragment, R.next_seq 'record_write))))
{
  with fin. assert (L.is_valid_finished lfin fin);
  assert (pure (Some? (R.seal
    'record_write
    (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)
    {
      R.content_type = T.Application_data;
      R.fragment =
        TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
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
  WS.lemma_serialize_tls_message_handshake (M.Finished fin);
  assert (pure (Seq.equal
    inner_plaintext_bytes
    (TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment (M.TlsHandshake (M.Finished fin)))));

  let mut aad = [| 0uy; 5sz |];
  serialize_application_data_header 53sz aad 5sz;
  with aad_bytes. assert (pts_to aad aad_bytes);
  assert (pure (Seq.equal aad_bytes (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)));

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
      { R.content_type = T.Application_data; R.fragment = inner_plaintext_bytes } ==
      Some (ciphertext_bytes, R.next_seq 'record_write)));
    let written =
      serialize_raw_application_data_record ciphertext 53sz network_out network_out_len;
    with network_bytes. assert (pts_to network_out network_bytes);
    assert (pure (SZ.v written == 58));
    assert (pure (B.length network_bytes == SZ.v network_out_len));
    assert (pure (CS.raw_records_exactly (Seq.slice network_bytes 0 58) T.Application_data 1));
    assert (pure (Seq.equal
      (TLS13.Spec.StateMachine.Canonical.record_header_aad (Seq.slice network_bytes 0 58))
      (TLS13.Spec.StateMachine.Canonical.application_data_record_header 53)));
    written
  } else {
    assert (pure False);
    0sz
  }
}

fn serialize_server_hello_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#sid: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v out_len == 90 + Seq.length (Ghost.reveal sid) /\
                Seq.length (Ghost.reveal rnd) == 32 /\
                (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                Seq.length (Ghost.reveal ks) == 32 /\
                Seq.length (Ghost.reveal sid) <= 32 /\
                Ghost.reveal sh ==
                  SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal sid) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  SerSH.serialize_server_hello_from_selection #sh #rnd #ks #sid #cs lsh out out_len #old_bytes
}

fn serialize_server_hello_record_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#sid: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (sid_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v sid_len == Seq.length (Ghost.reveal sid) /\
                SZ.v out_len == 95 + Seq.length (Ghost.reveal sid) /\
                Seq.length (Ghost.reveal rnd) == 32 /\
                (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                Seq.length (Ghost.reveal ks) == 32 /\
                Seq.length (Ghost.reveal sid) <= 32 /\
                Ghost.reveal sh ==
                  SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal sid) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                 (WS.serialize_record
                   T.Handshake
                   (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))) /\
               Seq.equal out_bytes
                (CS.serialized_cleartext_tls_message
                  (M.TlsHandshake (M.ServerHello (Ghost.reveal sh)))) /\
               WS.parse_record out_bytes ==
                 Some
                   (T.Handshake,
                    WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)),
                    SZ.v out_len) /\
               CS.raw_records_exactly out_bytes T.Handshake 1)
{
  let written =
    SerSH.serialize_server_hello_record_from_selection #sh #rnd #ks #sid #cs
      lsh sid_len out out_len #old_bytes;
  with out_bytes. assert (pts_to out out_bytes);
  WS.lemma_serialize_tls_message_handshake (M.ServerHello (Ghost.reveal sh));
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
               Seq.equal out_bytes
                 (WS.serialize_handshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions))))
{
  SerEE.serialize_empty_encrypted_extensions out out_len #old_bytes
}

fn serialize_certificate_from_credential
  (#cert: erased GCert.certificate)
  (#chain: erased B.bytes)
  (lcert: L.certificate_msg)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 1 <= Seq.length (Ghost.reveal chain) /\
                 Seq.length (Ghost.reveal chain) <= 32768 /\
                 Ghost.reveal cert == SerH.poc_canonical_cert (Ghost.reveal chain) /\
                 SZ.v out_len == B.length (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                 (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
{
  SerCert.serialize_certificate_from_credential #cert #chain lcert out out_len #old_bytes
}

fn serialize_certificate_verify_from_signature
  (#cv: erased GCV.certificateVerify)
  (lcv: L.certificate_verify)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                SZ.v out_len == B.length (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v out_len /\
               Seq.equal out_bytes
                 (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
{
  SerH.serialize_certificate_verify_handshake_poc #cv lcv out out_len #old_bytes
}

fn serialize_server_finished
  (#fin: erased GFin.finished)
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
                 (WS.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
               WS.parse_tls_message T.Handshake out_bytes ==
                 Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  SerFin.serialize_server_finished #fin lfin out out_len #old_bytes
}

#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let rec lemma_cipher_suites_match_length
  (wire:Seq.seq U16.t) (len:nat) (suites:list T.cipher_suite)
  : Lemma (requires L.cipher_suites_match wire len suites)
          (ensures FStar.List.Tot.length suites == len)
          (decreases len)
  = if len = 0 then ()
    else match suites with
         | [] -> ()
         | _ :: rest -> lemma_cipher_suites_match_length (Seq.slice wire 1 (Seq.length wire)) (len - 1) rest

let rec lemma_signature_schemes_match_length
  (wire:Seq.seq U16.t) (len:nat) (schemes:list T.signature_scheme)
  : Lemma (requires L.signature_schemes_match wire len schemes)
          (ensures FStar.List.Tot.length schemes == len)
          (decreases len)
  = if len = 0 then ()
    else match schemes with
         | [] -> ()
         | _ :: rest -> lemma_signature_schemes_match_length (Seq.slice wire 1 (Seq.length wire)) (len - 1) rest

let lemma_ch_handshake_len (rnd sni ks pks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length pks == 65 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    FStar.List.Tot.length cs <= 16 /\ FStar.List.Tot.length sa <= 16)
          (ensures B.length (WS.serialize_handshake (M.ClientHello (SerH.poc_canonical_ch rnd sni ks pks sid cs sa)))
                   == 220 + Seq.length sni
                          + 2 * FStar.List.Tot.length cs
                          + 2 * FStar.List.Tot.length sa)
  = let ch = SerH.poc_canonical_ch rnd sni ks pks sid cs sa in
    let exts = [ SerH.ch_sn_high sni; SerH.ch_sg_high; SerH.ch_sa_high sa; SerH.ch_ks_high ks pks; SerH.ch_sv_high ] in
    assert (ch.GCH.extensions == exts);
    Rev.lemma_serialize_handshake_client_hello ch;
    GHS.handshake_bytesize_eq (GHS.Body_client_hello (ch <: GHS.handshake_body_client_hello));
    GCH.clientHello_extensions_list_bytesize_nil;
    GCH.clientHello_extensions_list_bytesize_cons SerH.ch_sv_high [];
    GCH.clientHello_extensions_list_bytesize_cons (SerH.ch_ks_high ks pks) [SerH.ch_sv_high];
    GCH.clientHello_extensions_list_bytesize_cons (SerH.ch_sa_high sa) [SerH.ch_ks_high ks pks; SerH.ch_sv_high];
    GCH.clientHello_extensions_list_bytesize_cons SerH.ch_sg_high [SerH.ch_sa_high sa; SerH.ch_ks_high ks pks; SerH.ch_sv_high];
    GCH.clientHello_extensions_list_bytesize_cons (SerH.ch_sn_high sni) [SerH.ch_sg_high; SerH.ch_sa_high sa; SerH.ch_ks_high ks pks; SerH.ch_sv_high];
    ()
#pop-options

#push-options "--z3rlimit 100"
fn serialize_client_hello_from_start
  (#start: erased CS.handshake_start)
  (#ch: erased GCH.clientHello)
  (#rnd: erased B.bytes)
  (#sni: erased B.bytes)
  (#ks: erased B.bytes)
  (#pks: erased B.bytes)
  (#cs: erased GCH.clientHello_cipher_suites)
  (#sa: erased GECH.extensionClientHello_extension_data_signature_algorithms)
  (start_random: V.vec U8.t)
  (start_server_name: V.vec U8.t)
  (start_server_name_len: box SZ.t)
  (start_key_share: V.vec U8.t)
  (start_p256_key_share: V.vec U8.t)
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
                  old_present old_l_random old_l_session_id old_l_server_name old_l_key_share
                  old_l_cipher_suites old_l_signature_schemes
                  old_client_hello_bytes_len old_client_hello_bytes old_network_out.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_p256_key_share (Ghost.reveal pks) **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present old_present **
          V.pts_to l.L.client_hello_random old_l_random **
          V.pts_to l.L.client_hello_session_id old_l_session_id **
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
                V.is_full_vec start_p256_key_share /\
                V.is_full_vec start_cipher_suites /\
                V.is_full_vec start_signature_schemes /\
                V.is_full_vec l.L.client_hello_random /\
                V.is_full_vec l.L.client_hello_session_id /\
                V.is_full_vec l.L.client_hello_server_name /\
                V.is_full_vec l.L.client_hello_key_share /\
                V.is_full_vec l.L.client_hello_cipher_suites /\
                V.is_full_vec l.L.client_hello_signature_schemes /\
                V.is_full_vec client_hello_bytes /\
                V.length start_random == 32 /\
                V.length start_server_name == L.max_server_name_len /\
                V.length start_key_share == 32 /\
                V.length start_p256_key_share == 65 /\
                                V.length start_cipher_suites == L.max_cipher_suites /\
                V.length start_signature_schemes == L.max_signature_schemes /\
                V.length l.L.client_hello_random == 32 /\
                V.length l.L.client_hello_session_id == 32 /\
                V.length l.L.client_hello_server_name == L.max_server_name_len /\
                V.length l.L.client_hello_key_share == 32 /\
                V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
                V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
                V.length client_hello_bytes == 8192 /\
                B.length random == 32 /\
                B.length server_name == L.max_server_name_len /\
                B.length key_share == 32 /\
                Seq.length cipher_suites == L.max_cipher_suites /\
                Seq.length signature_schemes == L.max_signature_schemes /\
                B.length old_l_random == 32 /\
                B.length old_l_session_id == 32 /\
                B.length old_l_server_name == L.max_server_name_len /\
                B.length old_l_key_share == 32 /\
                Seq.length old_l_cipher_suites == L.max_cipher_suites /\
                Seq.length old_l_signature_schemes == L.max_signature_schemes /\
                B.length old_client_hello_bytes == 8192 /\
                B.length old_network_out == SZ.v network_out_len /\
                544 <= SZ.v network_out_len /\
                SZ.v server_name_len <= B.length server_name /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                Seq.equal random (Ghost.reveal start).CS.start_client_random /\
                B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
                Seq.equal (Ghost.reveal start).CS.start_server_name (Seq.slice server_name 0 (SZ.v server_name_len)) /\
                Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
                Seq.equal (Ghost.reveal pks) (Ghost.reveal start).CS.start_client_p256_public /\
                L.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  (Ghost.reveal start).CS.start_cipher_suites /\
                L.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  (Ghost.reveal start).CS.start_signature_schemes /\
                CS.client_hello_matches_start (Ghost.reveal start) (Ghost.reveal ch) /\
                Seq.length (Ghost.reveal rnd) == 32 /\
                Seq.length (Ghost.reveal ks) == 32 /\
                Seq.length (Ghost.reveal pks) == 65 /\
                1 <= Seq.length (Ghost.reveal sni) /\
                Seq.length (Ghost.reveal sni) <= 255 /\
                FStar.List.Tot.length (Ghost.reveal cs) <= 16 /\
                FStar.List.Tot.length (Ghost.reveal sa) <= 16 /\
                Ghost.reveal ch ==
                  SerH.poc_canonical_ch (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks)
                    (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa))
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* random server_name server_name_len key_share
                 cipher_suites cipher_suites_len
                 signature_schemes signature_schemes_len
                 handshake_bytes network_out_bytes handshake_len.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_p256_key_share (Ghost.reveal pks) **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present true **
          V.pts_to l.L.client_hello_random random **
          V.pts_to l.L.client_hello_session_id random **
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
               V.is_full_vec start_p256_key_share /\
               V.is_full_vec start_cipher_suites /\
               V.is_full_vec start_signature_schemes /\
               V.is_full_vec l.L.client_hello_random /\
               V.is_full_vec l.L.client_hello_session_id /\
               V.is_full_vec l.L.client_hello_server_name /\
               V.is_full_vec l.L.client_hello_key_share /\
               V.is_full_vec l.L.client_hello_cipher_suites /\
               V.is_full_vec l.L.client_hello_signature_schemes /\
               V.is_full_vec client_hello_bytes /\
               V.length start_random == 32 /\
               V.length start_server_name == L.max_server_name_len /\
               V.length start_key_share == 32 /\
               V.length start_p256_key_share == 65 /\
                              V.length start_cipher_suites == L.max_cipher_suites /\
               V.length start_signature_schemes == L.max_signature_schemes /\
               V.length l.L.client_hello_random == 32 /\
               V.length l.L.client_hello_session_id == 32 /\
               V.length l.L.client_hello_server_name == L.max_server_name_len /\
               V.length l.L.client_hello_key_share == 32 /\
               V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
               V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
               V.length client_hello_bytes == 8192 /\
               B.length random == 32 /\
               B.length server_name == L.max_server_name_len /\
               B.length key_share == 32 /\
               Seq.length cipher_suites == L.max_cipher_suites /\
               Seq.length signature_schemes == L.max_signature_schemes /\
               B.length handshake_bytes == 8192 /\
               B.length network_out_bytes == SZ.v network_out_len /\
               SZ.v server_name_len <= B.length server_name /\
               SZ.v cipher_suites_len <= Seq.length cipher_suites /\
               SZ.v signature_schemes_len <= Seq.length signature_schemes /\
               Seq.equal random (Ghost.reveal start).CS.start_client_random /\
               B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
               Seq.equal (Ghost.reveal start).CS.start_server_name (CL.raw_slice server_name 0 (SZ.v server_name_len)) /\
               Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
               Seq.equal (Ghost.reveal pks) (Ghost.reveal start).CS.start_client_p256_public /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Ghost.reveal start).CS.start_cipher_suites /\
               L.signature_schemes_match
                 signature_schemes
                 (SZ.v signature_schemes_len)
                 (Ghost.reveal start).CS.start_signature_schemes /\
               Seq.equal random (Sem.clientHello_random (Ghost.reveal ch)) /\
               L.optional_byte_prefix_matches
                 true
                 server_name
                 server_name_len
                 (Sem.clientHello_server_name (Ghost.reveal ch)) /\
               (match Sem.clientHello_key_share_x25519 (Ghost.reveal ch) with
                | Some k -> B.length k == 32 /\ Seq.equal key_share k
                | None -> False) /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Sem.clientHello_cipher_suites (Ghost.reveal ch)) /\
               (match Sem.clientHello_sig_algs (Ghost.reveal ch) with
                | Some sas ->
                  L.signature_schemes_match
                    signature_schemes
                    (SZ.v signature_schemes_len)
                    sas
                | None -> False) /\
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
  with old_l_random. assert (V.pts_to l.L.client_hello_random old_l_random);
  with old_l_session_id. assert (V.pts_to l.L.client_hello_session_id old_l_session_id);
  with old_l_server_name. assert (V.pts_to l.L.client_hello_server_name old_l_server_name);
  with old_l_key_share. assert (V.pts_to l.L.client_hello_key_share old_l_key_share);
  with old_l_cipher_suites. assert (V.pts_to l.L.client_hello_cipher_suites old_l_cipher_suites);
  with old_l_signature_schemes. assert (V.pts_to l.L.client_hello_signature_schemes old_l_signature_schemes);
  with old_client_hello_bytes. assert (V.pts_to client_hello_bytes old_client_hello_bytes);

  (* establish ch-semantic facts and the SNI length bound (<= 255) *)
  SerH.lemma_ch_random (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);
  SerH.lemma_ch_server_name (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);
  SerH.lemma_ch_key_share (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);
  assert (pure (Ghost.reveal sni == (Ghost.reveal start).CS.start_server_name));
  assert (pure (Seq.length (Ghost.reveal sni) == SZ.v server_name_len));
  assert (pure (Seq.length (Ghost.reveal sni) <= 255));
  lemma_ch_handshake_len (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);

  let hostname_len = !start_server_name_len;
  let cipher_suites_len_runtime = !start_cipher_suites_len;
  let signature_schemes_len_runtime = !start_signature_schemes_len;
  assert (pure (hostname_len == server_name_len));
  assert (pure (cipher_suites_len_runtime == cipher_suites_len));
  assert (pure (signature_schemes_len_runtime == signature_schemes_len));
  assert (pure (1 <= SZ.v hostname_len /\ SZ.v hostname_len <= 255));

  (* relate the runtime cipher_suites/signature_schemes lengths to the
     high-level list lengths in cs/sa: matches_start ties ch's semantics to
     start's lists, lemma_ch_cipher_suites/sig_algs tie them to cs/sa, and the
     *_match_length lemmas give the list-length == runtime-len equalities *)
  SerH.lemma_ch_cipher_suites (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);
  SerH.lemma_ch_sig_algs (Ghost.reveal rnd) (Ghost.reveal sni) (Ghost.reveal ks) (Ghost.reveal pks) (Ghost.reveal rnd) (Ghost.reveal cs) (Ghost.reveal sa);
  assert (pure (Ghost.reveal cs == (Ghost.reveal start).CS.start_cipher_suites));
  assert (pure (Ghost.reveal sa == (Ghost.reveal start).CS.start_signature_schemes));
  lemma_cipher_suites_match_length cipher_suites (SZ.v cipher_suites_len) (Ghost.reveal start).CS.start_cipher_suites;
  lemma_signature_schemes_match_length signature_schemes (SZ.v signature_schemes_len) (Ghost.reveal start).CS.start_signature_schemes;
  assert (pure (FStar.List.Tot.length (Ghost.reveal cs) == SZ.v cipher_suites_len_runtime));
  assert (pure (FStar.List.Tot.length (Ghost.reveal sa) == SZ.v signature_schemes_len_runtime));
  assert (pure (SZ.v cipher_suites_len_runtime <= 16));
  assert (pure (SZ.v signature_schemes_len_runtime <= 16));

  (* handshake_len = 220 + sni + 2*len_cs + 2*len_sa  (max 220+255+32+32 = 539).
     The constant is 220 rather than 149 because the ClientHello now offers two
     key-exchange groups: an extra NamedGroup in supported_groups (2 bytes) and
     an extra KeyShareEntry carrying the 65-byte uncompressed secp256r1 point
     (2 group + 2 length + 65 share = 69 bytes). *)
  SZ.fits_lte (220 + SZ.v hostname_len) 475;
  let hl1 = 220sz `SZ.add` hostname_len;
  SZ.fits_lte (SZ.v hl1 + SZ.v cipher_suites_len_runtime) 491;
  let hl2 = hl1 `SZ.add` cipher_suites_len_runtime;
  SZ.fits_lte (SZ.v hl2 + SZ.v cipher_suites_len_runtime) 507;
  let hl3 = hl2 `SZ.add` cipher_suites_len_runtime;
  SZ.fits_lte (SZ.v hl3 + SZ.v signature_schemes_len_runtime) 523;
  let hl4 = hl3 `SZ.add` signature_schemes_len_runtime;
  SZ.fits_lte (SZ.v hl4 + SZ.v signature_schemes_len_runtime) 539;
  let handshake_len = hl4 `SZ.add` signature_schemes_len_runtime;
  assert (pure (SZ.v handshake_len ==
    220 + SZ.v hostname_len + 2 * SZ.v cipher_suites_len_runtime + 2 * SZ.v signature_schemes_len_runtime));
  assert (pure (SZ.v handshake_len <= 539));
  assert (pure (SZ.v handshake_len ==
    B.length (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
  assert (pure (SZ.v handshake_len + 5 <= 544));
  SZ.fits_lte (SZ.v handshake_len + 5) 544;
  let record_len = handshake_len `SZ.add` 5sz;
  assert (pure (SZ.v record_len == 5 + SZ.v handshake_len));
  assert (pure (SZ.v record_len <= SZ.v network_out_len));

  (* first copy: start vecs -> l vecs, so l's content matches ch's semantics *)
  copy_vec_to_vec_u8 start_random l.L.client_hello_random 32sz;
  (* The client's legacy_session_id is a 32-byte value (RFC 8446 4.1.2 / D.4
     middlebox compatibility).  We reuse the ClientHello random, which is a
     fresh 32-byte random already carried in [handshake_start] and travels in
     the same cleartext message; this keeps the session id RFC-compliant
     without adding a second random to the model state. *)
  copy_vec_to_vec_u8 start_random l.L.client_hello_session_id 32sz;
  copy_vec_to_vec_u8 start_server_name l.L.client_hello_server_name 255sz;
  copy_vec_to_vec_u8 start_key_share l.L.client_hello_key_share 32sz;
  copy_vec_to_vec_u16 start_cipher_suites l.L.client_hello_cipher_suites 64sz;
  copy_vec_to_vec_u16 start_signature_schemes l.L.client_hello_signature_schemes 32sz;

  (* [l]'s caller does not own a secp256r1 slot -- the client's own P-256 share
     travels separately as [start_p256_key_share] -- so the canonical structure
     gets a scratch one, freed once ownership is recovered below.  It is never
     read: [client_hello_has_p256_key_share = false] makes the slot's clause
     vacuous. *)
  let l_poc_p256_key_share = V.alloc 0uy 65sz;
  (* build canonical-pinned structure sharing l's vecs (only scalars differ) *)
  let l_poc : L.client_hello = {
    L.client_hello_random = l.L.client_hello_random;
    L.client_hello_session_id = l.L.client_hello_session_id;
    L.client_hello_session_id_len = 32sz;
    L.client_hello_server_name = l.L.client_hello_server_name;
    L.client_hello_server_name_len = hostname_len;
    L.client_hello_has_server_name = true;
    L.client_hello_key_share = l.L.client_hello_key_share;
    L.client_hello_p256_key_share = l_poc_p256_key_share;
    L.client_hello_has_p256_key_share = false;
    L.client_hello_cipher_suites = l.L.client_hello_cipher_suites;
    L.client_hello_cipher_suites_len = cipher_suites_len_runtime;
    L.client_hello_signature_schemes = l.L.client_hello_signature_schemes;
    L.client_hello_signature_schemes_len = signature_schemes_len_runtime;
  };
  assert (pure (Seq.equal random (Sem.clientHello_random (Ghost.reveal ch))));
  assert (pure (L.optional_byte_prefix_matches
    true server_name hostname_len (Sem.clientHello_server_name (Ghost.reveal ch))));
  assert (pure (L.cipher_suites_match
    cipher_suites (SZ.v cipher_suites_len_runtime) (Sem.clientHello_cipher_suites (Ghost.reveal ch))));
  rewrite (V.pts_to l.L.client_hello_random random)
       as (V.pts_to l_poc.L.client_hello_random random);
  with session_id. assert (V.pts_to l.L.client_hello_session_id session_id);
  rewrite (V.pts_to l.L.client_hello_session_id session_id)
       as (V.pts_to l_poc.L.client_hello_session_id session_id);
  rewrite (V.pts_to l.L.client_hello_server_name server_name)
       as (V.pts_to l_poc.L.client_hello_server_name server_name);
  rewrite (V.pts_to l.L.client_hello_key_share key_share)
       as (V.pts_to l_poc.L.client_hello_key_share key_share);
  rewrite (V.pts_to l_poc_p256_key_share (Seq.create 65 0uy))
       as (V.pts_to l_poc.L.client_hello_p256_key_share (Seq.create 65 0uy));
  rewrite (V.pts_to l.L.client_hello_cipher_suites cipher_suites)
       as (V.pts_to l_poc.L.client_hello_cipher_suites cipher_suites);
  rewrite (V.pts_to l.L.client_hello_signature_schemes signature_schemes)
       as (V.pts_to l_poc.L.client_hello_signature_schemes signature_schemes);
  fold (L.is_valid_client_hello l_poc (Ghost.reveal ch));

  (* allocate an exact-length scratch buffer, run the verified POC serializer *)
  let tmp = V.alloc 0uy handshake_len;
  V.to_array_pts_to tmp;
  let written_poc = SerH.serialize_client_hello_handshake_poc
    #ch #rnd #sni #ks #pks #rnd #cs #sa l_poc start_p256_key_share (V.vec_to_array tmp) handshake_len;
  with ob. assert (pts_to (V.vec_to_array tmp) ob);
  assert (pure (Seq.equal ob (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
  Seq.lemma_eq_elim
    ob
    (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)));

  let written =
    SerPR.serialize_raw_record
      T.Handshake
      (V.vec_to_array tmp)
      handshake_len
      network_out
      network_out_len;
  with network_out_bytes. assert (pts_to network_out network_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));

  (* copy POC output into client_hello_bytes[0..handshake_len) *)
  V.to_array_pts_to client_hello_bytes;
  copy_array_slice_to_array
    (V.vec_to_array tmp) handshake_len 0sz handshake_len
    (V.vec_to_array client_hello_bytes) 8192sz 0sz;
  with out_common. assert (pts_to (V.vec_to_array client_hello_bytes) out_common);
  pts_to_len (V.vec_to_array client_hello_bytes);
  assert (pure (B.length out_common == 8192));
  lemma_copy_expr_copied_slice
    old_client_hello_bytes (CL.raw_slice ob 0 (SZ.v handshake_len)) 0 (SZ.v handshake_len) 8192;
  Seq.lemma_eq_elim (CL.raw_slice ob 0 (SZ.v handshake_len)) ob;
  assert (pure (Seq.equal
    (CL.raw_slice out_common 0 (SZ.v handshake_len))
    (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch)))));
  V.to_vec_pts_to tmp;
  V.free tmp;

  (* recover l's vec ownership; second copy re-pins l's content to the start values *)
  unfold (L.is_valid_client_hello l_poc (Ghost.reveal ch));
  with w_p256. assert (V.pts_to l_poc.L.client_hello_p256_key_share w_p256);
  rewrite (V.pts_to l_poc.L.client_hello_p256_key_share w_p256)
       as (V.pts_to l_poc_p256_key_share w_p256);
  V.free l_poc_p256_key_share;
  with w_rnd. assert (V.pts_to l_poc.L.client_hello_random w_rnd);
  rewrite (V.pts_to l_poc.L.client_hello_random w_rnd)
       as (V.pts_to l.L.client_hello_random w_rnd);
  with w_sid. assert (V.pts_to l_poc.L.client_hello_session_id w_sid);
  rewrite (V.pts_to l_poc.L.client_hello_session_id w_sid)
       as (V.pts_to l.L.client_hello_session_id w_sid);
  with w_sn. assert (V.pts_to l_poc.L.client_hello_server_name w_sn);
  rewrite (V.pts_to l_poc.L.client_hello_server_name w_sn)
       as (V.pts_to l.L.client_hello_server_name w_sn);
  with w_ks. assert (V.pts_to l_poc.L.client_hello_key_share w_ks);
  rewrite (V.pts_to l_poc.L.client_hello_key_share w_ks)
       as (V.pts_to l.L.client_hello_key_share w_ks);
  with w_cs. assert (V.pts_to l_poc.L.client_hello_cipher_suites w_cs);
  rewrite (V.pts_to l_poc.L.client_hello_cipher_suites w_cs)
       as (V.pts_to l.L.client_hello_cipher_suites w_cs);
  with w_ss. assert (V.pts_to l_poc.L.client_hello_signature_schemes w_ss);
  rewrite (V.pts_to l_poc.L.client_hello_signature_schemes w_ss)
       as (V.pts_to l.L.client_hello_signature_schemes w_ss);
  copy_vec_to_vec_u8 start_random l.L.client_hello_random 32sz;
  (* The client's legacy_session_id is a 32-byte value (RFC 8446 4.1.2 / D.4
     middlebox compatibility).  We reuse the ClientHello random, which is a
     fresh 32-byte random already carried in [handshake_start] and travels in
     the same cleartext message; this keeps the session id RFC-compliant
     without adding a second random to the model state. *)
  copy_vec_to_vec_u8 start_random l.L.client_hello_session_id 32sz;
  copy_vec_to_vec_u8 start_server_name l.L.client_hello_server_name 255sz;
  copy_vec_to_vec_u8 start_key_share l.L.client_hello_key_share 32sz;
  copy_vec_to_vec_u16 start_cipher_suites l.L.client_hello_cipher_suites 64sz;
  copy_vec_to_vec_u16 start_signature_schemes l.L.client_hello_signature_schemes 32sz;

  client_hello_bytes_len := handshake_len;
  client_hello_present := true;
  V.to_vec_pts_to client_hello_bytes;

  with handshake_bytes. assert (V.pts_to client_hello_bytes handshake_bytes);
  V.pts_to_len client_hello_bytes;
  pts_to_len network_out;
  assert (pure (B.length handshake_bytes == 8192));
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));

  WS.lemma_serialize_tls_message_handshake (M.ClientHello (Ghost.reveal ch));
  assert (pure (SZ.v written ==
    B.length (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch))))));

  (* ---- semantic postconditions via client_hello_matches_start ---- *)
  assert (pure (Seq.equal random (Sem.clientHello_random (Ghost.reveal ch))));
  assert (pure (L.optional_byte_prefix_matches
    true server_name server_name_len (Sem.clientHello_server_name (Ghost.reveal ch))));
  written
}
#pop-options
