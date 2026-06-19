module TLS13.Impl.Serializer.Certificate

friend TLS13.Wire.Spec

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module CL = TLS13.ConnectionLog
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec

let common_byte_eq_ws (n:nat)
  : Lemma (C.byte n == WS.byte n)
=
  C.lemma_byte_reveal n;
  assert_norm (WS.byte n == U8.uint_to_t (n % 256));
  assert (C.byte n == U8.uint_to_t (n % 256));
  assert (WS.byte n == U8.uint_to_t (n % 256))

let u24_reveal (n:nat)
  : Lemma (Seq.equal (WS.u24 n) (C.write_u24_bytes n))
=
  common_byte_eq_ws (n / 65536);
  common_byte_eq_ws (n / 256);
  common_byte_eq_ws n;
  C.lemma_write_u24_bytes_reveal n;
  assert (Seq.equal
    (B.of_list [WS.byte (n / 65536); WS.byte (n / 256); WS.byte n])
    (C.write_u24_bytes n));
  Seq.lemma_eq_elim
    (WS.u24 n)
    (B.of_list [WS.byte (n / 65536); WS.byte (n / 256); WS.byte n])

let u16_reveal (n:nat)
  : Lemma (Seq.equal (WS.u16 n) (C.write_u16_bytes n))
=
  common_byte_eq_ws (n / 256);
  common_byte_eq_ws n;
  C.lemma_write_u16_bytes_reveal n;
  assert (Seq.equal
    (B.of_list [WS.byte (n / 256); WS.byte n])
    (C.write_u16_bytes n));
  Seq.lemma_eq_elim
    (WS.u16 n)
    (B.of_list [WS.byte (n / 256); WS.byte n])

let certificate_single_bytes (certificate:B.bytes) : GTot B.bytes =
  B.append
    (B.of_list [11uy])
    (B.append
      (C.write_u24_bytes (9 + B.length certificate))
      (B.append
        (B.of_list [0uy])
        (B.append
          (C.write_u24_bytes (5 + B.length certificate))
          (B.append
            (C.write_u24_bytes (B.length certificate))
            (B.append certificate (C.write_u16_bytes 0))))))

let serialize_certificate_single_shape
  (cert:M.certificate_msg)
  (certificate:B.bytes)
  : Lemma
      (requires cert.M.chain == [certificate])
      (ensures Seq.equal
        (WS.serialize_certificate_from_credential cert)
        (certificate_single_bytes certificate) /\
       B.length (WS.serialize_certificate_from_credential cert) ==
        13 + B.length certificate)
=
  assert (WS.serialize_certificate_entries cert.M.chain ==
    B.append
      (WS.u24 (B.length certificate))
      (B.append certificate (B.append (WS.u16 0) B.empty)));
  assert (B.length (WS.serialize_certificate_entries cert.M.chain) ==
    5 + B.length certificate);
  assert (WS.serialize_certificate_msg cert ==
    WS.append3
      (WS.u8 0)
      (WS.u24 (5 + B.length certificate))
      (WS.serialize_certificate_entries cert.M.chain));
  assert (B.length (WS.serialize_certificate_msg cert) ==
    9 + B.length certificate);
  assert (WS.serialize_certificate_from_credential cert ==
    WS.append3
      (WS.u8 11)
      (WS.u24 (9 + B.length certificate))
      (WS.serialize_certificate_msg cert));
  assert (Seq.equal (WS.u8 11) (B.of_list [11uy]));
  assert (Seq.equal (WS.u8 0) (B.of_list [0uy]));
  TLS13.Wire.Spec.Reveal.Util.lemma_singleton_of_list 11uy;
  TLS13.Wire.Spec.Reveal.Util.lemma_singleton_of_list 0uy;
  u24_reveal (9 + B.length certificate);
  u24_reveal (5 + B.length certificate);
  u24_reveal (B.length certificate);
  u16_reveal 0;
  Seq.lemma_eq_elim (WS.u24 (9 + B.length certificate))
    (C.write_u24_bytes (9 + B.length certificate));
  Seq.lemma_eq_elim (WS.u24 (5 + B.length certificate))
    (C.write_u24_bytes (5 + B.length certificate));
  Seq.lemma_eq_elim (WS.u24 (B.length certificate))
    (C.write_u24_bytes (B.length certificate));
  Seq.lemma_eq_elim (WS.u16 0) (C.write_u16_bytes 0);
  Seq.lemma_eq_elim (WS.u8 11) (B.of_list [11uy]);
  Seq.lemma_eq_elim (WS.u8 0) (B.of_list [0uy]);
  assert (Seq.equal
    (WS.serialize_certificate_from_credential cert)
    (certificate_single_bytes certificate))

let lemma_single_certificate_from_storage
  (storage:B.bytes)
  (storage_len:nat)
  (offsets:Seq.seq SZ.t)
  (lens:Seq.seq SZ.t)
  (cert:M.certificate_msg)
  : Lemma
      (requires storage_len <= B.length storage /\
                1 <= Seq.length offsets /\
                1 <= Seq.length lens /\
                L.certificate_chain_matches storage storage_len offsets lens 1 cert.M.chain /\
                (exists (certificate:B.bytes). cert.M.chain == [certificate]))
      (ensures
        (let off = SZ.v (Seq.index offsets 0) in
         let len = SZ.v (Seq.index lens 0) in
         off + len <= storage_len /\
         Seq.equal
           (WS.serialize_certificate_from_credential cert)
           (certificate_single_bytes (CL.raw_slice storage off (off + len))) /\
         B.length (WS.serialize_certificate_from_credential cert) == 13 + len))
=
  match cert.M.chain with
  | [certificate] ->
    let off = SZ.v (Seq.index offsets 0) in
    let len = SZ.v (Seq.index lens 0) in
    assert (off + len <= storage_len);
    assert (Seq.equal certificate (Seq.slice storage off (off + len)));
    Seq.lemma_len_slice storage off (off + len);
    assert (B.length (CL.raw_slice storage off (off + len)) == len);
    Seq.lemma_eq_elim certificate (CL.raw_slice storage off (off + len));
    serialize_certificate_single_shape cert (CL.raw_slice storage off (off + len))
  | _ ->
    assert False

let certificate_out_shape
  (out_bytes:B.bytes)
  (certificate:B.bytes)
  : Lemma
      (requires B.length out_bytes == 13 + B.length certificate /\
                Seq.equal (CL.raw_slice out_bytes 0 1) (B.of_list [11uy]) /\
                Seq.equal (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (9 + B.length certificate)) /\
                Seq.equal (CL.raw_slice out_bytes 4 5) (B.of_list [0uy]) /\
                Seq.equal (CL.raw_slice out_bytes 5 8) (C.write_u24_bytes (5 + B.length certificate)) /\
                Seq.equal (CL.raw_slice out_bytes 8 11) (C.write_u24_bytes (B.length certificate)) /\
                Seq.equal (CL.raw_slice out_bytes 11 (11 + B.length certificate)) certificate /\
                Seq.equal (CL.raw_slice out_bytes (11 + B.length certificate) (13 + B.length certificate))
                  (C.write_u16_bytes 0))
      (ensures Seq.equal out_bytes (certificate_single_bytes certificate))
=
  C.lemma_raw_slice_all out_bytes;
  C.lemma_raw_slice_empty out_bytes (13 + B.length certificate);
  CL.lemma_raw_slice_split out_bytes 0 1 4;
  CL.lemma_raw_slice_split out_bytes 0 4 5;
  CL.lemma_raw_slice_split out_bytes 0 5 8;
  CL.lemma_raw_slice_split out_bytes 0 8 11;
  CL.lemma_raw_slice_split out_bytes 0 11 (11 + B.length certificate);
  CL.lemma_raw_slice_split out_bytes 0 (11 + B.length certificate) (13 + B.length certificate);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 1) (B.of_list [11uy]);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (9 + B.length certificate));
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 4 5) (B.of_list [0uy]);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 5 8) (C.write_u24_bytes (5 + B.length certificate));
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 8 11) (C.write_u24_bytes (B.length certificate));
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 11 (11 + B.length certificate)) certificate;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes (11 + B.length certificate) (13 + B.length certificate))
    (C.write_u16_bytes 0);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes (13 + B.length certificate) (13 + B.length certificate)) B.empty;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 (13 + B.length certificate)) out_bytes

let certificate_fixed_header_slices
  (bytes:B.bytes)
  (cert_len:nat)
  : Lemma
      (requires B.length bytes == 13 + cert_len /\
                Seq.index bytes 0 == 11uy /\
                Seq.index bytes 1 == C.byte ((9 + cert_len) / 65536) /\
                Seq.index bytes 2 == C.byte ((9 + cert_len) / 256) /\
                Seq.index bytes 3 == C.byte (9 + cert_len) /\
                Seq.index bytes 4 == 0uy /\
                Seq.index bytes 5 == C.byte ((5 + cert_len) / 65536) /\
                Seq.index bytes 6 == C.byte ((5 + cert_len) / 256) /\
                Seq.index bytes 7 == C.byte (5 + cert_len) /\
                Seq.index bytes 8 == C.byte (cert_len / 65536) /\
                Seq.index bytes 9 == C.byte (cert_len / 256) /\
                Seq.index bytes 10 == C.byte cert_len)
      (ensures Seq.equal (CL.raw_slice bytes 0 1) (B.of_list [11uy]) /\
               Seq.equal (CL.raw_slice bytes 1 4) (C.write_u24_bytes (9 + cert_len)) /\
               Seq.equal (CL.raw_slice bytes 4 5) (B.of_list [0uy]) /\
               Seq.equal (CL.raw_slice bytes 5 8) (C.write_u24_bytes (5 + cert_len)) /\
               Seq.equal (CL.raw_slice bytes 8 11) (C.write_u24_bytes cert_len))
=
  C.lemma_write_u24_bytes_reveal (9 + cert_len);
  C.lemma_write_u24_bytes_reveal (5 + cert_len);
  C.lemma_write_u24_bytes_reveal cert_len;
  Seq.lemma_eq_elim
    (C.write_u24_bytes (9 + cert_len))
    (B.of_list [
      C.byte ((9 + cert_len) / 65536);
      C.byte ((9 + cert_len) / 256);
      C.byte (9 + cert_len)]);
  Seq.lemma_eq_elim
    (C.write_u24_bytes (5 + cert_len))
    (B.of_list [
      C.byte ((5 + cert_len) / 65536);
      C.byte ((5 + cert_len) / 256);
      C.byte (5 + cert_len)]);
  Seq.lemma_eq_elim
    (C.write_u24_bytes cert_len)
    (B.of_list [C.byte (cert_len / 65536); C.byte (cert_len / 256); C.byte cert_len]);
  Seq.lemma_len_slice bytes 0 1;
  Seq.lemma_len_slice bytes 1 4;
  Seq.lemma_len_slice bytes 4 5;
  Seq.lemma_len_slice bytes 5 8;
  Seq.lemma_len_slice bytes 8 11;
  C.lemma_raw_slice_index bytes 0 1 0;
  C.lemma_raw_slice_index bytes 1 4 0;
  C.lemma_raw_slice_index bytes 1 4 1;
  C.lemma_raw_slice_index bytes 1 4 2;
  C.lemma_raw_slice_index bytes 4 5 0;
  C.lemma_raw_slice_index bytes 5 8 0;
  C.lemma_raw_slice_index bytes 5 8 1;
  C.lemma_raw_slice_index bytes 5 8 2;
  C.lemma_raw_slice_index bytes 8 11 0;
  C.lemma_raw_slice_index bytes 8 11 1;
  C.lemma_raw_slice_index bytes 8 11 2;
  Seq.lemma_eq_intro (CL.raw_slice bytes 0 1) (B.of_list [11uy]);
  Seq.lemma_eq_intro (CL.raw_slice bytes 1 4) (C.write_u24_bytes (9 + cert_len));
  Seq.lemma_eq_intro (CL.raw_slice bytes 4 5) (B.of_list [0uy]);
  Seq.lemma_eq_intro (CL.raw_slice bytes 5 8) (C.write_u24_bytes (5 + cert_len));
  Seq.lemma_eq_intro (CL.raw_slice bytes 8 11) (C.write_u24_bytes cert_len)

let extension_zero_slice (bytes:B.bytes) (off:nat)
  : Lemma
      (requires off + 2 <= B.length bytes /\
                Seq.index bytes off == 0uy /\
                Seq.index bytes (off + 1) == 0uy)
      (ensures Seq.equal (CL.raw_slice bytes off (off + 2)) (C.write_u16_bytes 0))
=
  C.lemma_byte_reveal 0;
  assert_norm (U8.uint_to_t (0 % 256) == 0uy);
  assert (C.byte 0 == 0uy);
  C.lemma_write_u16_bytes_reveal 0;
  Seq.lemma_eq_elim (C.write_u16_bytes 0) (B.of_list [0uy; 0uy]);
  assert (off <= off + 2);
  Seq.lemma_len_slice bytes off (off + 2);
  C.lemma_raw_slice_index bytes off (off + 2) 0;
  C.lemma_raw_slice_index bytes off (off + 2) 1;
  Seq.lemma_eq_intro (CL.raw_slice bytes off (off + 2)) (C.write_u16_bytes 0)

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
                 SZ.v out_len ==
                   B.length (WS.serialize_certificate_from_credential (Ghost.reveal cert)))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_certificate_from_credential (Ghost.reveal cert)))
{
  unfold (L.is_valid_certificate_msg lcert (Ghost.reveal cert));
  with chain_bytes offsets lens. assert (
    V.pts_to lcert.L.certificate_msg_chain_bytes chain_bytes **
    V.pts_to lcert.L.certificate_msg_cert_offsets offsets **
    V.pts_to lcert.L.certificate_msg_cert_lens lens);
  V.pts_to_len lcert.L.certificate_msg_chain_bytes;
  V.pts_to_len lcert.L.certificate_msg_cert_offsets;
  V.pts_to_len lcert.L.certificate_msg_cert_lens;
  assert (pure (B.length chain_bytes == L.max_certificate_chain_bytes));
  assert (pure (Seq.length offsets == L.max_certificate_chain_entries));
  assert (pure (Seq.length lens == L.max_certificate_chain_entries));
  assert (pure (1 <= Seq.length offsets));
  assert (pure (1 <= Seq.length lens));

  V.to_array_pts_to lcert.L.certificate_msg_cert_offsets;
  let cert_off = (V.vec_to_array lcert.L.certificate_msg_cert_offsets).(0sz);
  V.to_vec_pts_to lcert.L.certificate_msg_cert_offsets;
  V.to_array_pts_to lcert.L.certificate_msg_cert_lens;
  let cert_len = (V.vec_to_array lcert.L.certificate_msg_cert_lens).(0sz);
  V.to_vec_pts_to lcert.L.certificate_msg_cert_lens;
  assert (pure (cert_off == Seq.index offsets 0));
  assert (pure (cert_len == Seq.index lens 0));

  lemma_single_certificate_from_storage
    chain_bytes
    (SZ.v lcert.L.certificate_msg_chain_bytes_len)
    offsets
    lens
    (Ghost.reveal cert);
  assert (pure (SZ.v cert_off + SZ.v cert_len <=
    SZ.v lcert.L.certificate_msg_chain_bytes_len));
  assert (pure (SZ.v out_len == 13 + SZ.v cert_len));
  assert (pure (B.length (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len)) ==
    SZ.v cert_len));
  assert (pure (SZ.fits (SZ.v cert_len + 5)));
  let cert_list_len = cert_len `SZ.add` 5sz;
  assert (pure (SZ.v cert_list_len == 5 + SZ.v cert_len));
  assert (pure (SZ.fits (SZ.v cert_len + 9)));
  let body_len = cert_len `SZ.add` 9sz;
  assert (pure (SZ.v body_len == 9 + SZ.v cert_len));
  assert (pure (11 + SZ.v cert_len <= SZ.v out_len));
  assert (pure (13 + SZ.v cert_len <= SZ.v out_len));

  pts_to_len out;
  out.(0sz) <- 11uy;
  C.u8_of_sizet_div2_byte body_len;
  out.(1sz) <- C.u8_of_sizet (SZ.div (SZ.div body_len 256sz) 256sz);
  out.(2sz) <- C.u8_of_sizet (SZ.div body_len 256sz);
  out.(3sz) <- C.u8_of_sizet body_len;
  out.(4sz) <- 0uy;
  C.u8_of_sizet_div2_byte cert_list_len;
  out.(5sz) <- C.u8_of_sizet (SZ.div (SZ.div cert_list_len 256sz) 256sz);
  out.(6sz) <- C.u8_of_sizet (SZ.div cert_list_len 256sz);
  out.(7sz) <- C.u8_of_sizet cert_list_len;
  C.u8_of_sizet_div2_byte cert_len;
  out.(8sz) <- C.u8_of_sizet (SZ.div (SZ.div cert_len 256sz) 256sz);
  out.(9sz) <- C.u8_of_sizet (SZ.div cert_len 256sz);
  out.(10sz) <- C.u8_of_sizet cert_len;
  with before_cert_copy. assert (pts_to out before_cert_copy);
  pts_to_len out;
  C.u8_of_sizet_v_byte (SZ.div body_len 256sz);
  C.u8_of_sizet_v_byte body_len;
  C.u8_of_sizet_v_byte (SZ.div cert_list_len 256sz);
  C.u8_of_sizet_v_byte cert_list_len;
  C.u8_of_sizet_v_byte (SZ.div cert_len 256sz);
  C.u8_of_sizet_v_byte cert_len;
  assert (pure (SZ.v (SZ.div body_len 256sz) == SZ.v body_len / 256));
  assert (pure (SZ.v (SZ.div cert_list_len 256sz) == SZ.v cert_list_len / 256));
  assert (pure (SZ.v (SZ.div cert_len 256sz) == SZ.v cert_len / 256));
  assert (pure (Seq.index before_cert_copy 0 == 11uy));
  assert (pure (Seq.index before_cert_copy 1 == C.byte (SZ.v body_len / 65536)));
  assert (pure (Seq.index before_cert_copy 2 == C.byte (SZ.v body_len / 256)));
  assert (pure (Seq.index before_cert_copy 3 == C.byte (SZ.v body_len)));
  assert (pure (Seq.index before_cert_copy 4 == 0uy));
  assert (pure (Seq.index before_cert_copy 5 == C.byte (SZ.v cert_list_len / 65536)));
  assert (pure (Seq.index before_cert_copy 6 == C.byte (SZ.v cert_list_len / 256)));
  assert (pure (Seq.index before_cert_copy 7 == C.byte (SZ.v cert_list_len)));
  assert (pure (Seq.index before_cert_copy 8 == C.byte (SZ.v cert_len / 65536)));
  assert (pure (Seq.index before_cert_copy 9 == C.byte (SZ.v cert_len / 256)));
  assert (pure (Seq.index before_cert_copy 10 == C.byte (SZ.v cert_len)));

  V.to_array_pts_to lcert.L.certificate_msg_chain_bytes;
  C.copy_array_slice_to_array
    (V.vec_to_array lcert.L.certificate_msg_chain_bytes)
    L.max_certificate_chain_bytes_sz
    cert_off
    cert_len
    out
    out_len
    11sz;
  V.to_vec_pts_to lcert.L.certificate_msg_chain_bytes;
  with before_ext. assert (pts_to out before_ext);

  let ext_off = cert_len `SZ.add` 11sz;
  assert (pure (SZ.v ext_off == 11 + SZ.v cert_len));
  pts_to_len out;
  out.(ext_off) <- 0uy;
  with after_ext0. assert (pts_to out after_ext0);
  let ext_off1 = ext_off `SZ.add` 1sz;
  assert (pure (SZ.v ext_off1 == 12 + SZ.v cert_len));
  pts_to_len out;
  out.(ext_off1) <- 0uy;
  with out_bytes. assert (pts_to out out_bytes);
  pts_to_len out;
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (B.length out_bytes == 13 + SZ.v cert_len));

  C.lemma_copy_expr_preserves_prefix_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len) 0 1;
  C.lemma_copy_expr_preserves_prefix_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len) 1 4;
  C.lemma_copy_expr_preserves_prefix_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len) 4 5;
  C.lemma_copy_expr_preserves_prefix_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len) 5 8;
  C.lemma_copy_expr_preserves_prefix_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len) 8 11;
  C.lemma_copy_expr_copied_slice
    before_cert_copy (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))
    11 (SZ.v cert_len) (SZ.v out_len);
  certificate_fixed_header_slices before_cert_copy (SZ.v cert_len);
  Seq.lemma_eq_elim (CL.raw_slice before_ext 0 1) (CL.raw_slice before_cert_copy 0 1);
  Seq.lemma_eq_elim (CL.raw_slice before_ext 1 4) (CL.raw_slice before_cert_copy 1 4);
  Seq.lemma_eq_elim (CL.raw_slice before_ext 4 5) (CL.raw_slice before_cert_copy 4 5);
  Seq.lemma_eq_elim (CL.raw_slice before_ext 5 8) (CL.raw_slice before_cert_copy 5 8);
  Seq.lemma_eq_elim (CL.raw_slice before_ext 8 11) (CL.raw_slice before_cert_copy 8 11);

  C.lemma_write_u16_bytes_reveal 0;
  Seq.lemma_index_upd1 before_ext (SZ.v ext_off) 0uy;
  Seq.lemma_index_upd2 after_ext0 (SZ.v ext_off1) 0uy (SZ.v ext_off);
  Seq.lemma_index_upd1 after_ext0 (SZ.v ext_off1) 0uy;
  extension_zero_slice out_bytes (SZ.v ext_off);

  // The two extension-byte stores occur after all earlier slices.
  C.lemma_raw_slice_index out_bytes 0 1 0;
  assert (pure (Seq.equal (CL.raw_slice out_bytes 0 1) (CL.raw_slice before_ext 0 1)));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 1 4) (CL.raw_slice before_ext 1 4)));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 4 5) (CL.raw_slice before_ext 4 5)));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 5 8) (CL.raw_slice before_ext 5 8)));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 8 11) (CL.raw_slice before_ext 8 11)));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 11 (11 + SZ.v cert_len))
    (CL.raw_slice before_ext 11 (11 + SZ.v cert_len))));
  Seq.lemma_eq_elim
    (CL.raw_slice before_ext 11 (11 + SZ.v cert_len))
    (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 0 1) (B.of_list [11uy])));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (9 + SZ.v cert_len))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 4 5) (B.of_list [0uy])));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 5 8) (C.write_u24_bytes (5 + SZ.v cert_len))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 8 11) (C.write_u24_bytes (SZ.v cert_len))));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 11 (11 + SZ.v cert_len))
    (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes (11 + SZ.v cert_len) (13 + SZ.v cert_len))
    (C.write_u16_bytes 0)));
  certificate_out_shape
    out_bytes
    (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len));
  assert (pure (Seq.equal
    out_bytes
    (certificate_single_bytes
      (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len)))));
  Seq.lemma_eq_elim
    (certificate_single_bytes
      (CL.raw_slice chain_bytes (SZ.v cert_off) (SZ.v cert_off + SZ.v cert_len)))
    (WS.serialize_certificate_from_credential (Ghost.reveal cert));
  fold (L.is_valid_certificate_msg lcert (Ghost.reveal cert));
  out_len
}
