module TLS13.Impl.Serializer.CertificateVerify

friend TLS13.Wire.Spec

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module Cast = FStar.Int.Cast
module CL = TLS13.ConnectionLog
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
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

let u16_reveal (n:nat)
  : Lemma (Seq.equal (WS.u16 n) (C.write_u16_bytes n))
=
  common_byte_eq_ws (n / 256);
  common_byte_eq_ws n;
  C.lemma_write_u16_bytes_reveal n;
  assert (Seq.equal
    (B.of_list [WS.byte (n / 256); WS.byte n])
    (C.write_u16_bytes n));
  Seq.lemma_eq_elim (WS.u16 n) (B.of_list [WS.byte (n / 256); WS.byte n])

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
  Seq.lemma_eq_elim (WS.u24 n) (B.of_list [WS.byte (n / 65536); WS.byte (n / 256); WS.byte n])

let signature_scheme_matches_to_u16 (wire:U16.t) (scheme:T.signature_scheme)
  : Lemma
      (requires L.signature_scheme_matches wire scheme)
      (ensures U16.v wire == WS.signature_scheme_to_u16 scheme)
=
  match scheme with
  | T.Rsa_pss_rsae_sha256 -> ()
  | T.Ecdsa_secp256r1_sha256 -> ()
  | T.Ed25519 -> ()
  | T.Unknown_signatureScheme _ -> ()

let serialize_cv_shape (cv:M.certificate_verify)
  : Lemma (Seq.equal
      (WS.serialize_certificate_verify_from_signature cv)
      (B.append
        (B.of_list [15uy])
        (B.append
          (WS.u24 (4 + B.length cv.M.signature))
          (B.append
            (WS.u16 (WS.signature_scheme_to_u16 cv.M.scheme))
            (B.append (WS.u16 (B.length cv.M.signature)) cv.M.signature)))))
=
  let body = WS.serialize_certificate_verify cv in
  assert (body ==
    B.append
      (WS.u16 (WS.signature_scheme_to_u16 cv.M.scheme))
      (B.append (WS.u16 (B.length cv.M.signature)) cv.M.signature));
  assert (B.length body == 4 + B.length cv.M.signature);
  assert (WS.serialize_certificate_verify_from_signature cv ==
    B.append (WS.u8 15) (B.append (WS.u24 (B.length body)) body));
  assert (Seq.equal (WS.u8 15) (B.of_list [15uy]));
  Seq.lemma_eq_elim (WS.u8 15) (B.of_list [15uy]);
  assert (B.length body == 4 + B.length cv.M.signature)

let out_cv_shape
  (out_bytes:B.bytes)
  (sig:B.bytes)
  (sig_len:nat)
  (scheme_n:nat)
  : Lemma
      (requires B.length out_bytes == 8 + sig_len /\
                B.length sig == sig_len /\
                Seq.equal (CL.raw_slice out_bytes 0 1) (B.of_list [15uy]) /\
                Seq.equal (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (4 + sig_len)) /\
                Seq.equal (CL.raw_slice out_bytes 4 6) (C.write_u16_bytes scheme_n) /\
                Seq.equal (CL.raw_slice out_bytes 6 8) (C.write_u16_bytes sig_len) /\
                Seq.equal (CL.raw_slice out_bytes 8 (8 + sig_len)) sig)
      (ensures Seq.equal out_bytes
        (B.append
          (B.of_list [15uy])
          (B.append
            (C.write_u24_bytes (4 + sig_len))
            (B.append
              (C.write_u16_bytes scheme_n)
              (B.append (C.write_u16_bytes sig_len) sig)))))
=
  C.lemma_raw_slice_all out_bytes;
  C.lemma_raw_slice_empty out_bytes (8 + sig_len);
  CL.lemma_raw_slice_split out_bytes 0 1 4;
  CL.lemma_raw_slice_split out_bytes 0 4 6;
  CL.lemma_raw_slice_split out_bytes 0 6 8;
  CL.lemma_raw_slice_split out_bytes 0 8 (8 + sig_len);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 1) (B.of_list [15uy]);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (4 + sig_len));
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 4 6) (C.write_u16_bytes scheme_n);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 6 8) (C.write_u16_bytes sig_len);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 8 (8 + sig_len)) sig;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes (8 + sig_len) (8 + sig_len)) B.empty;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 (8 + sig_len)) out_bytes

let cv_header_slices
  (bytes:B.bytes)
  (body_len:nat)
  (scheme_n:nat)
  (sig_len:nat)
  : Lemma
      (requires 8 <= B.length bytes /\
                Seq.index bytes 0 == 15uy /\
                Seq.index bytes 1 == C.byte (body_len / 65536) /\
                Seq.index bytes 2 == C.byte (body_len / 256) /\
                Seq.index bytes 3 == C.byte body_len /\
                Seq.index bytes 4 == C.byte (scheme_n / 256) /\
                Seq.index bytes 5 == C.byte scheme_n /\
                Seq.index bytes 6 == C.byte (sig_len / 256) /\
                Seq.index bytes 7 == C.byte sig_len)
      (ensures Seq.equal (CL.raw_slice bytes 0 1) (B.of_list [15uy]) /\
               Seq.equal (CL.raw_slice bytes 1 4) (C.write_u24_bytes body_len) /\
               Seq.equal (CL.raw_slice bytes 4 6) (C.write_u16_bytes scheme_n) /\
               Seq.equal (CL.raw_slice bytes 6 8) (C.write_u16_bytes sig_len))
=
  C.lemma_write_u24_bytes_reveal body_len;
  Seq.lemma_eq_elim
    (C.write_u24_bytes body_len)
    (B.of_list [C.byte (body_len / 65536); C.byte (body_len / 256); C.byte body_len]);
  C.lemma_write_u16_bytes_reveal scheme_n;
  Seq.lemma_eq_elim
    (C.write_u16_bytes scheme_n)
    (B.of_list [C.byte (scheme_n / 256); C.byte scheme_n]);
  C.lemma_write_u16_bytes_reveal sig_len;
  Seq.lemma_eq_elim
    (C.write_u16_bytes sig_len)
    (B.of_list [C.byte (sig_len / 256); C.byte sig_len]);
  assert (CL.raw_slice bytes 0 1 == Seq.slice bytes 0 1);
  assert (CL.raw_slice bytes 1 4 == Seq.slice bytes 1 4);
  assert (CL.raw_slice bytes 4 6 == Seq.slice bytes 4 6);
  assert (CL.raw_slice bytes 6 8 == Seq.slice bytes 6 8);
  Seq.lemma_len_slice bytes 0 1;
  Seq.lemma_len_slice bytes 1 4;
  Seq.lemma_len_slice bytes 4 6;
  Seq.lemma_len_slice bytes 6 8;
  assert (B.length (CL.raw_slice bytes 0 1) == 1);
  assert (B.length (CL.raw_slice bytes 1 4) == 3);
  assert (B.length (CL.raw_slice bytes 4 6) == 2);
  assert (B.length (CL.raw_slice bytes 6 8) == 2);
  assert (Seq.index (CL.raw_slice bytes 0 1) 0 == 15uy);
  assert (Seq.index (CL.raw_slice bytes 1 4) 0 == C.byte (body_len / 65536));
  assert (Seq.index (CL.raw_slice bytes 1 4) 1 == C.byte (body_len / 256));
  assert (Seq.index (CL.raw_slice bytes 1 4) 2 == C.byte body_len);
  assert (Seq.index (CL.raw_slice bytes 4 6) 0 == C.byte (scheme_n / 256));
  assert (Seq.index (CL.raw_slice bytes 4 6) 1 == C.byte scheme_n);
  assert (Seq.index (CL.raw_slice bytes 6 8) 0 == C.byte (sig_len / 256));
  assert (Seq.index (CL.raw_slice bytes 6 8) 1 == C.byte sig_len);
  Seq.lemma_eq_intro (CL.raw_slice bytes 0 1) (B.of_list [15uy]);
  Seq.lemma_eq_intro (CL.raw_slice bytes 1 4) (C.write_u24_bytes body_len);
  Seq.lemma_eq_intro (CL.raw_slice bytes 4 6) (C.write_u16_bytes scheme_n);
  Seq.lemma_eq_intro (CL.raw_slice bytes 6 8) (C.write_u16_bytes sig_len)

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
  unfold (L.is_valid_certificate_verify lcv (Ghost.reveal cv));
  with signature. assert (V.pts_to lcv.L.certificate_verify_signature signature);
  V.pts_to_len lcv.L.certificate_verify_signature;
  assert (pure (B.length signature == L.max_signature_len));
  assert (pure (B.length signature == SZ.v L.max_signature_len_sz));
  assert (pure (L.byte_prefix_matches
    signature
    lcv.L.certificate_verify_signature_len
    (Ghost.reveal cv).M.signature));
  assert (pure (Seq.equal
    (Ghost.reveal cv).M.signature
    (Seq.slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))));
  assert (pure (B.length (Ghost.reveal cv).M.signature == SZ.v lcv.L.certificate_verify_signature_len));
  WS.lemma_serialize_certificate_verify_from_signature_len (Ghost.reveal cv);
  assert (pure (SZ.v out_len == 8 + SZ.v lcv.L.certificate_verify_signature_len));

  let body_len = lcv.L.certificate_verify_signature_len `SZ.add` 4sz;
  assert (pure (SZ.v body_len == 4 + SZ.v lcv.L.certificate_verify_signature_len));
  assert (pure (SZ.v out_len == 8 + SZ.v lcv.L.certificate_verify_signature_len));
  let scheme_sz = SZ.uint16_to_sizet lcv.L.certificate_verify_scheme;

  pts_to_len out;
  assert (pure (8 <= SZ.v out_len));
  out.(0sz) <- 15uy;
  C.u8_of_sizet_div2_byte body_len;
  out.(1sz) <- C.u8_of_sizet (SZ.div (SZ.div body_len 256sz) 256sz);
  out.(2sz) <- C.u8_of_sizet (SZ.div body_len 256sz);
  out.(3sz) <- C.u8_of_sizet body_len;
  out.(4sz) <- C.u8_of_sizet (SZ.div scheme_sz 256sz);
  out.(5sz) <- C.u8_of_sizet scheme_sz;
  out.(6sz) <- C.u8_of_sizet (SZ.div lcv.L.certificate_verify_signature_len 256sz);
  out.(7sz) <- C.u8_of_sizet lcv.L.certificate_verify_signature_len;

  pts_to_len out;
  with out_before_sig. assert (pts_to out out_before_sig);
  assert (pure (B.length out_before_sig == SZ.v out_len));
  C.u8_of_sizet_v_byte (SZ.div body_len 256sz);
  C.u8_of_sizet_v_byte body_len;
  C.u8_of_sizet_v_byte (SZ.div scheme_sz 256sz);
  C.u8_of_sizet_v_byte scheme_sz;
  C.u8_of_sizet_v_byte (SZ.div lcv.L.certificate_verify_signature_len 256sz);
  C.u8_of_sizet_v_byte lcv.L.certificate_verify_signature_len;
  assert (pure (SZ.v (SZ.div body_len 256sz) == SZ.v body_len / 256));
  assert (pure (SZ.v (SZ.div scheme_sz 256sz) == SZ.v scheme_sz / 256));
  assert (pure (SZ.v (SZ.div lcv.L.certificate_verify_signature_len 256sz) ==
    SZ.v lcv.L.certificate_verify_signature_len / 256));
  assert (pure (Seq.index out_before_sig 0 == 15uy));
  assert (pure (Seq.index out_before_sig 1 == C.byte (SZ.v body_len / 65536)));
  assert (pure (Seq.index out_before_sig 2 == C.byte (SZ.v body_len / 256)));
  assert (pure (Seq.index out_before_sig 3 == C.byte (SZ.v body_len)));
  assert (pure (Seq.index out_before_sig 4 == C.byte (SZ.v scheme_sz / 256)));
  assert (pure (Seq.index out_before_sig 5 == C.byte (SZ.v scheme_sz)));
  assert (pure (Seq.index out_before_sig 6 == C.byte (SZ.v lcv.L.certificate_verify_signature_len / 256)));
  assert (pure (Seq.index out_before_sig 7 == C.byte (SZ.v lcv.L.certificate_verify_signature_len)));
  V.to_array_pts_to lcv.L.certificate_verify_signature;
  C.copy_array_slice_to_array
    (V.vec_to_array lcv.L.certificate_verify_signature)
    L.max_signature_len_sz
    0sz
    lcv.L.certificate_verify_signature_len
    out
    out_len
    8sz;
  V.to_vec_pts_to lcv.L.certificate_verify_signature;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (B.length out_bytes == 8 + SZ.v lcv.L.certificate_verify_signature_len));
  assert (pure (SZ.v lcv.L.certificate_verify_signature_len <= B.length signature));
  Seq.lemma_len_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len);
  assert (pure (B.length (CL.raw_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len)) ==
    SZ.v lcv.L.certificate_verify_signature_len));
  C.lemma_copy_expr_preserves_prefix_slice
    out_before_sig
    (CL.raw_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))
    8
    (SZ.v lcv.L.certificate_verify_signature_len)
    (SZ.v out_len)
    0
    1;
  C.lemma_copy_expr_preserves_prefix_slice
    out_before_sig
    (CL.raw_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))
    8
    (SZ.v lcv.L.certificate_verify_signature_len)
    (SZ.v out_len)
    1
    4;
  C.lemma_copy_expr_preserves_prefix_slice
    out_before_sig
    (CL.raw_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))
    8
    (SZ.v lcv.L.certificate_verify_signature_len)
    (SZ.v out_len)
    4
    6;
  C.lemma_copy_expr_preserves_prefix_slice
    out_before_sig
    (CL.raw_slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))
    8
    (SZ.v lcv.L.certificate_verify_signature_len)
    (SZ.v out_len)
    6
    8;
  cv_header_slices
    out_before_sig
    (SZ.v body_len)
    (SZ.v scheme_sz)
    (SZ.v lcv.L.certificate_verify_signature_len);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 1) (CL.raw_slice out_before_sig 0 1);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 1 4) (CL.raw_slice out_before_sig 1 4);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 4 6) (CL.raw_slice out_before_sig 4 6);
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 6 8) (CL.raw_slice out_before_sig 6 8);
  Seq.lemma_eq_elim (CL.raw_slice out_before_sig 0 1) (B.of_list [15uy]);
  Seq.lemma_eq_elim (CL.raw_slice out_before_sig 1 4) (C.write_u24_bytes (SZ.v body_len));
  Seq.lemma_eq_elim (CL.raw_slice out_before_sig 4 6) (C.write_u16_bytes (SZ.v scheme_sz));
  Seq.lemma_eq_elim (CL.raw_slice out_before_sig 6 8)
    (C.write_u16_bytes (SZ.v lcv.L.certificate_verify_signature_len));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 8 (8 + SZ.v lcv.L.certificate_verify_signature_len))
    (Seq.slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))));
  Seq.lemma_eq_elim
    (Seq.slice signature 0 (SZ.v lcv.L.certificate_verify_signature_len))
    (Ghost.reveal cv).M.signature;
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 8 (8 + SZ.v lcv.L.certificate_verify_signature_len))
    (Ghost.reveal cv).M.signature));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 0 1) (B.of_list [15uy])));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 1 4) (C.write_u24_bytes (4 + SZ.v lcv.L.certificate_verify_signature_len))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 4 6) (C.write_u16_bytes (SZ.v scheme_sz))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 6 8) (C.write_u16_bytes (SZ.v lcv.L.certificate_verify_signature_len))));
  signature_scheme_matches_to_u16 lcv.L.certificate_verify_scheme (Ghost.reveal cv).M.scheme;
  assert (pure (SZ.v scheme_sz == U16.v lcv.L.certificate_verify_scheme));
  assert (pure (SZ.v scheme_sz == WS.signature_scheme_to_u16 (Ghost.reveal cv).M.scheme));
  out_cv_shape
    out_bytes
    (Ghost.reveal cv).M.signature
    (SZ.v lcv.L.certificate_verify_signature_len)
    (WS.signature_scheme_to_u16 (Ghost.reveal cv).M.scheme);
  u24_reveal (4 + B.length (Ghost.reveal cv).M.signature);
  u16_reveal (WS.signature_scheme_to_u16 (Ghost.reveal cv).M.scheme);
  u16_reveal (B.length (Ghost.reveal cv).M.signature);
  serialize_cv_shape (Ghost.reveal cv);
  Seq.lemma_eq_elim
    (WS.u24 (4 + B.length (Ghost.reveal cv).M.signature))
    (C.write_u24_bytes (4 + B.length (Ghost.reveal cv).M.signature));
  Seq.lemma_eq_elim
    (WS.u16 (WS.signature_scheme_to_u16 (Ghost.reveal cv).M.scheme))
    (C.write_u16_bytes (WS.signature_scheme_to_u16 (Ghost.reveal cv).M.scheme));
  Seq.lemma_eq_elim
    (WS.u16 (B.length (Ghost.reveal cv).M.signature))
    (C.write_u16_bytes (B.length (Ghost.reveal cv).M.signature));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_certificate_verify_from_signature (Ghost.reveal cv))));
  fold (L.is_valid_certificate_verify lcv (Ghost.reveal cv));
  out_len
}
