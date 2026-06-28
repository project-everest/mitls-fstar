module TLS13.Impl.Serializer.FinishedPOC

#lang-pulse

(* Proof-of-concept: the BUILD direction (serialize) via the generated copyful
   l2r writer [GHS.write_handshake], for the simplest message (Finished).
   Establishes the template: build the [_low] repr from the L mirror, fold the
   sum [handshake_vmatch], bridge array->slice, call the writer, read the bytes
   == [WS.serialize_handshake (M.Finished fin)] from the safe-writer postcond. *)

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Seq = FStar.Seq
module T = TLS13.Types
module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module WS = TLS13.Wire.Spec
module Sem = TLS13.Wire.Semantics
module GHS = TLS13.Wire.Generated.Handshake
module GFin = TLS13.Wire.Generated.Finished
module GCV = TLS13.Wire.Generated.CertificateVerify
module GSS = TLS13.Wire.Generated.SignatureScheme
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module PPB = LowParse.PulseParse.Base
module PPBY = LowParse.PulseParse.Bytes
module PPVCL = LowParse.PulseParse.VCList
module LSeqB = LowParse.Pulse.SeqBytes
module LP = LowParse.Spec
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators

(* Intro the sum vmatch for a Finished body, reverse of Impl.Parser.elim_vmatch_finished. *)
ghost
fn intro_handshake_finished_vmatch
  (lv: PPBY.lvec U8.t)
  (cm: Ghost.erased (Seq.seq U8.t))
  requires V.pts_to lv.PPBY.lvec_vec cm ** pure (V.is_full_vec lv.PPBY.lvec_vec)
  ensures GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid (Ghost.reveal cm))
{
  fold (LSeqB.vmatch_copy_seqbytes lv (Ghost.reveal cm));
  rewrite (LSeqB.vmatch_copy_seqbytes lv (Ghost.reveal cm))
       as (GHS.handshake_body_finished_vmatch lv (Ghost.reveal cm));
  fold (GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid (Ghost.reveal cm)));
}

fn serialize_finished_handshake_poc
  (#fin: erased GFin.finished)
  (lfin: L.finished)
  (handshake_out: A.array U8.t)
  (handshake_out_len: SZ.t)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           A.pts_to handshake_out 'old_handshake **
           pure (B.length 'old_handshake == SZ.v handshake_out_len /\
                 SZ.v handshake_out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v handshake_out_len})
  ensures exists* handshake_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          A.pts_to handshake_out handshake_bytes **
          pure (B.length handshake_bytes == 36 /\
                SZ.v written == 36 /\
                Seq.equal handshake_bytes
                  (WS.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                WS.parse_tls_message T.Handshake handshake_bytes ==
                  Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  unfold (L.is_valid_finished lfin (Ghost.reveal fin));
  with verify_data. assert (V.pts_to lfin.L.finished_verify_data verify_data);
  let lv : PPBY.lvec U8.t = { PPBY.lvec_vec = lfin.L.finished_verify_data; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to lfin.L.finished_verify_data verify_data)
       as (V.pts_to lv.PPBY.lvec_vec verify_data);
  intro_handshake_finished_vmatch lv verify_data;
  A.pts_to_len handshake_out;
  let s = S.from_array handshake_out handshake_out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_finished_low lv)
             #(Ghost.hide (GHS.Body_finished_mid verify_data))
             s perr;
  with v'. assert (S.pts_to s v');
  (* serialized length of a 32-byte Finished handshake message is exactly 36 *)
  assert (pure (Seq.length verify_data == 32));
  GHS.handshake_bytesize_eq (GHS.Body_finished verify_data);
  assert (pure (GHS.handshake_conv (GHS.Body_finished_mid verify_data)
                  == Some (GHS.Body_finished verify_data)));
  (* recover the array and the L mirror vec from the writer-preserved vmatch *)
  S.to_array s;
  A.pts_to_len handshake_out;
  assert (pure (SZ.v sz == 36));
  WS.lemma_serialize_handshake_finished (Ghost.reveal fin);
  Seq.lemma_eq_elim verify_data (Ghost.reveal fin);
  WS.lemma_parse_serialize_handshake_finished (Ghost.reveal fin);
  unfold (GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid verify_data));
  rewrite (GHS.handshake_body_finished_vmatch lv verify_data)
       as (LSeqB.vmatch_copy_seqbytes lv verify_data);
  unfold (LSeqB.vmatch_copy_seqbytes lv verify_data);
  rewrite (V.pts_to lv.PPBY.lvec_vec verify_data)
       as (V.pts_to lfin.L.finished_verify_data verify_data);
  fold (L.is_valid_finished lfin (Ghost.reveal fin));
  sz
}

(* ===================================================================== *)
(* CertificateVerify                                                     *)
(* ===================================================================== *)

(* Inverse of the [match]-on-[signatureScheme] performed by the read direction
   (Impl.Parser scheme_u16): maps a wire U16 to the generated leaf scheme. *)
inline_for_extraction
let u16_to_sig_scheme (w:U16.t) : GSS.signatureScheme =
  if w = 1027us then GSS.Ecdsa_secp256r1_sha256
  else if w = 2052us then GSS.Rsa_pss_rsae_sha256
  else if w = 2055us then GSS.Ed25519
  else GSS.Unknown_signatureScheme w

(* [signature_scheme_matches] pins the wire U16 to its scheme, so the runtime
   [u16_to_sig_scheme] reconstruction agrees with the ghost generated scheme. *)
let lemma_u16_to_sig_scheme (w:U16.t) (s:GSS.signatureScheme)
  : Lemma (requires L.signature_scheme_matches w s)
          (ensures u16_to_sig_scheme w == s)
  = ()

(* Forward CertificateVerify conv: a mid whose signature fits the 65535-byte
   vlbytes bound converts to the obvious [Body_certificate_verify] record. *)
let lemma_cv_conv_fwd (cvm: GHS.handshake_body_certificate_verify_mid)
  : Lemma (requires Seq.length (snd cvm) <= 65535)
          (ensures GHS.handshake_conv (GHS.Body_certificate_verify_mid cvm) ==
                   Some (GHS.Body_certificate_verify
                          ({ GCV.algorithm = fst cvm;
                             GCV.signature = (snd cvm <: GCV.certificateVerify_signature) })))
  = ()

(* Copy the [len]-byte prefix of a full source Vec into a freshly allocated
   EXACT-length [len] Vec; the source is preserved.  Build-direction analogue of
   the read-direction [alloc_copy_vec_prefix]/[alloc_copy_slice]. *)
inline_for_extraction
fn alloc_copy_vec_exact (src: V.vec U8.t) (len: SZ.t) (cap: SZ.t)
  requires V.pts_to src 'src_bytes **
           pure (V.is_full_vec src /\ V.length src == SZ.v cap /\ SZ.v len <= SZ.v cap /\
                 Seq.length (Ghost.reveal 'src_bytes) == SZ.v cap)
  returns dst: V.vec U8.t
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v len /\
                  B.length dst_bytes == SZ.v len /\
                  Seq.length (Ghost.reveal 'src_bytes) == SZ.v cap /\
                  SZ.v len <= SZ.v cap /\
                  Seq.equal dst_bytes (Seq.slice (Ghost.reveal 'src_bytes) 0 (SZ.v len))))
{
  let dst = V.alloc 0uy len;
  V.pts_to_len src;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) cap;
  S.pts_to_len src_slice;
  let src_split = S.split src_slice len;
  S.pts_to_len (fst src_split);
  S.pts_to_len (snd src_split);
  let dst_slice = S.from_array (V.vec_to_array dst) len;
  S.pts_to_len dst_slice;
  S.copy dst_slice (fst src_split);
  Seq.lemma_split (Ghost.reveal 'src_bytes) (SZ.v len);
  S.join (fst src_split) (snd src_split) src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  dst
}

(* Intro the sum vmatch for a CertificateVerify body: the exact inverse of
   Impl.Parser.elim_vmatch_certificate_verify. *)
ghost
fn intro_handshake_certificate_verify_vmatch
  (xcv: GHS.handshake_body_certificate_verify_lowtype)
  (cvm: Ghost.erased GHS.handshake_body_certificate_verify_mid)
  requires V.pts_to (snd xcv).PPBY.lvec_vec (snd (Ghost.reveal cvm)) **
           pure (V.is_full_vec (snd xcv).PPBY.lvec_vec /\
                 fst xcv == fst (Ghost.reveal cvm))
  ensures GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv)
                               (GHS.Body_certificate_verify_mid (Ghost.reveal cvm))
{
  fold (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst (Ghost.reveal cvm)));
  rewrite (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst (Ghost.reveal cvm)))
       as (GSS.signatureScheme_vmatch (fst xcv) (fst (Ghost.reveal cvm)));
  fold (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd (Ghost.reveal cvm)));
  rewrite (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd (Ghost.reveal cvm)))
       as (GCV.certificateVerify_signature_vmatch (snd xcv) (snd (Ghost.reveal cvm)));
  fold (LPC.vmatch_pair GSS.signatureScheme_vmatch GCV.certificateVerify_signature_vmatch
          xcv (Ghost.reveal cvm));
  rewrite (LPC.vmatch_pair GSS.signatureScheme_vmatch GCV.certificateVerify_signature_vmatch
            xcv (Ghost.reveal cvm))
       as (GHS.handshake_body_certificate_verify_vmatch xcv (Ghost.reveal cvm));
  fold (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv)
                             (GHS.Body_certificate_verify_mid (Ghost.reveal cvm)));
}

fn serialize_certificate_verify_handshake_poc
  (#cv: erased GCV.certificateVerify)
  (lcv: L.certificate_verify)
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
           A.pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == B.length (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
          A.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
{
  unfold (L.is_valid_certificate_verify lcv (Ghost.reveal cv));
  with signature. assert (V.pts_to lcv.L.certificate_verify_signature signature);
  (* runtime scheme leaf == ghost cv.algorithm *)
  let sch = u16_to_sig_scheme lcv.L.certificate_verify_scheme;
  lemma_u16_to_sig_scheme lcv.L.certificate_verify_scheme
    (Sem.certificateVerify_scheme (Ghost.reveal cv));
  (* exact-length signature vec holding cv.signature *)
  V.pts_to_len lcv.L.certificate_verify_signature;
  let sig_vec = alloc_copy_vec_exact lcv.L.certificate_verify_signature
                  lcv.L.certificate_verify_signature_len L.max_signature_len_sz;
  with sig_copy. assert (V.pts_to sig_vec sig_copy);
  Seq.lemma_eq_elim sig_copy (Sem.certificateVerify_signature_bytes (Ghost.reveal cv));
  let lv : PPBY.lvec U8.t = { PPBY.lvec_vec = sig_vec;
                              PPBY.lvec_len = lcv.L.certificate_verify_signature_len };
  rewrite (V.pts_to sig_vec sig_copy)
       as (V.pts_to lv.PPBY.lvec_vec (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)));
  let xcv : GCV.certificateVerify_lowtype = (sch, lv);
  let cvm : Ghost.erased GHS.handshake_body_certificate_verify_mid =
    Ghost.hide ((Ghost.reveal cv).GCV.algorithm,
                ((Ghost.reveal cv).GCV.signature <: Seq.seq U8.t));
  rewrite (V.pts_to lv.PPBY.lvec_vec (Sem.certificateVerify_signature_bytes (Ghost.reveal cv)))
       as (V.pts_to (snd xcv).PPBY.lvec_vec (snd (Ghost.reveal cvm)));
  intro_handshake_certificate_verify_vmatch xcv cvm;
  A.pts_to_len out;
  let s = S.from_array out out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_certificate_verify_low xcv)
             #(Ghost.hide (GHS.Body_certificate_verify_mid (Ghost.reveal cvm)))
             s perr;
  with v'. assert (S.pts_to s v');
  WS.lemma_serialize_handshake_certificate_verify (Ghost.reveal cv);
  GHS.handshake_bytesize_eq (GHS.Body_certificate_verify (Ghost.reveal cv));
  lemma_cv_conv_fwd (Ghost.reveal cvm);
  assert (pure (GHS.handshake_conv (GHS.Body_certificate_verify_mid (Ghost.reveal cvm))
                  == Some (GHS.Body_certificate_verify (Ghost.reveal cv))));
  S.to_array s;
  A.pts_to_len out;
  (* recover the signature copy from the writer-preserved vmatch and free it *)
  unfold (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv)
                               (GHS.Body_certificate_verify_mid (Ghost.reveal cvm)));
  rewrite (GHS.handshake_body_certificate_verify_vmatch xcv (Ghost.reveal cvm))
       as (LPC.vmatch_pair GSS.signatureScheme_vmatch GCV.certificateVerify_signature_vmatch
             xcv (Ghost.reveal cvm));
  unfold (LPC.vmatch_pair GSS.signatureScheme_vmatch GCV.certificateVerify_signature_vmatch
            xcv (Ghost.reveal cvm));
  rewrite (GSS.signatureScheme_vmatch (fst xcv) (fst (Ghost.reveal cvm)))
       as (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst (Ghost.reveal cvm)));
  unfold (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst (Ghost.reveal cvm)));
  rewrite (GCV.certificateVerify_signature_vmatch (snd xcv) (snd (Ghost.reveal cvm)))
       as (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd (Ghost.reveal cvm)));
  unfold (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd (Ghost.reveal cvm)));
  V.free (snd xcv).PPBY.lvec_vec;
  fold (L.is_valid_certificate_verify lcv (Ghost.reveal cv));
  sz
}

(* ===================================================================== *)
(* EncryptedExtensions (empty)                                           *)
(* ===================================================================== *)

let lemma_ee_nil_bytesize ()
  : Lemma (GEE.encryptedExtensions_list_bytesize ([] <: list GEEE.extensionEncryptedExtensions) == 0)
  = GEE.encryptedExtensions_list_bytesize_nil

(* Forward EncryptedExtensions conv: a list whose bytesize fits the 65535-byte
   vldata bound converts to the obvious [Body_encrypted_extensions] record. *)
let lemma_ee_conv_fwd (cee: GHS.handshake_body_encrypted_extensions_mid)
  : Lemma (requires GEE.encryptedExtensions_list_bytesize cee <= 65535)
          (ensures GHS.handshake_conv (GHS.Body_encrypted_extensions_mid cee) ==
                   Some (GHS.Body_encrypted_extensions (cee <: GHS.handshake_body_encrypted_extensions)))
  = ()

(* Intro the sum vmatch for an EncryptedExtensions body: the exact inverse of
   Impl.Parser.elim_vmatch_encrypted_extensions (the vldata-strong wrapper is
   definitionally the inner vclist vmatch). *)
ghost
fn intro_handshake_encrypted_extensions_vmatch
  (xee: GHS.handshake_body_encrypted_extensions_lowtype)
  (cee: Ghost.erased GHS.handshake_body_encrypted_extensions_mid)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee (Ghost.reveal cee)
  ensures GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
                               (GHS.Body_encrypted_extensions_mid (Ghost.reveal cee))
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee (Ghost.reveal cee))
       as (GHS.handshake_body_encrypted_extensions_vmatch xee (Ghost.reveal cee));
  fold (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
                             (GHS.Body_encrypted_extensions_mid (Ghost.reveal cee)));
}

fn serialize_empty_encrypted_extensions_poc
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires A.pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 6)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          A.pts_to out out_bytes **
          pure (B.length out_bytes == 6 /\
                SZ.v written == 6 /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.EncryptedExtensions ([] <: GEE.encryptedExtensions))))
{
  lemma_ee_nil_bytesize ();
  let xee : GEE.encryptedExtensions_lowtype =
    None #(SZ.t & V.vec GEEE.extensionEncryptedExtensions_lowtype);
  fold (PPVCL.vmatch_vclist
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv)
          (None #(SZ.t & V.vec GEEE.extensionEncryptedExtensions_lowtype))
          ([] <: list GEEE.extensionEncryptedExtensions));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             (None #(SZ.t & V.vec GEEE.extensionEncryptedExtensions_lowtype))
             ([] <: list GEEE.extensionEncryptedExtensions))
       as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee ([] <: list GEEE.extensionEncryptedExtensions));
  intro_handshake_encrypted_extensions_vmatch xee
    (Ghost.hide ([] <: GHS.handshake_body_encrypted_extensions_mid));
  A.pts_to_len out;
  let s = S.from_array out out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_encrypted_extensions_low xee)
             #(Ghost.hide (GHS.Body_encrypted_extensions_mid
                             ([] <: GHS.handshake_body_encrypted_extensions_mid)))
             s perr;
  with v'. assert (S.pts_to s v');
  (* serialized length of the empty EncryptedExtensions handshake is exactly 6 *)
  GHS.handshake_bytesize_eq (GHS.Body_encrypted_extensions
                              ([] <: GHS.handshake_body_encrypted_extensions));
  lemma_ee_conv_fwd ([] <: GHS.handshake_body_encrypted_extensions_mid);
  assert (pure (GHS.handshake_conv
                  (GHS.Body_encrypted_extensions_mid
                    ([] <: GHS.handshake_body_encrypted_extensions_mid))
                  == Some (GHS.Body_encrypted_extensions
                            ([] <: GHS.handshake_body_encrypted_extensions))));
  S.to_array s;
  A.pts_to_len out;
  assert (pure (SZ.v sz == 6));
  WS.lemma_serialize_handshake_encrypted_extensions ([] <: GEE.encryptedExtensions);
  (* dispose the writer-preserved (empty) vmatch *)
  unfold (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
                               (GHS.Body_encrypted_extensions_mid
                                 ([] <: GHS.handshake_body_encrypted_extensions_mid)));
  rewrite (GHS.handshake_body_encrypted_extensions_vmatch xee
             ([] <: GHS.handshake_body_encrypted_extensions_mid))
       as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee ([] <: list GEEE.extensionEncryptedExtensions));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee ([] <: list GEEE.extensionEncryptedExtensions))
       as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             (None #(SZ.t & V.vec GEEE.extensionEncryptedExtensions_lowtype))
             ([] <: list GEEE.extensionEncryptedExtensions));
  unfold (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                             GEEE.extensionEncryptedExtensions_conv)
            (None #(SZ.t & V.vec GEEE.extensionEncryptedExtensions_lowtype))
            ([] <: list GEEE.extensionEncryptedExtensions));
  sz
}

(* =====================================================================
   Certificate / ServerHello / ClientHello: BUILD via the generated
   copyful writer is BLOCKED by a spec-completeness gap, NOT by proof
   difficulty.  Documented here; no code emitted (so the module stays
   fully verified).  See the per-message notes below.

   ROOT CAUSE (common to all three).  The generated writer serializes the
   *entire* high-level message:
       WS.serialize_handshake (M.<Msg> m)
         == LP.serialize GHS.handshake_serializer (GHS.Body_<msg> m)
   i.e. every field of [m] (an erased GHS.<msg>) reaches the wire.  The
   POC template feeds the writer a low value whose [handshake_vmatch] holds
   against [m], so the proof obligation
       out_bytes == WS.serialize_handshake (M.<Msg> m)
   forces us to reproduce *all* of [m] at runtime.  The only runtime input
   is the L mirror [l] together with [L.is_valid_<msg> l m].  For Finished,
   CertificateVerify and (empty) EncryptedExtensions, [is_valid_<msg>] pins
   *every* serialized field, so [m] is uniquely determined by [l] and the
   template closes.  For Certificate/ServerHello/ClientHello it does NOT:
   [is_valid_<msg>] constrains only a subset of fields, leaving the rest
   free.  Because [m] is universally quantified (erased implicit), a caller
   may pick two messages [m1 <> m2] that both satisfy [is_valid_<msg> l _]
   yet serialize to different bytes; one runtime output cannot equal both,
   so the contract is unsatisfiable as written -- by ANY implementation,
   not merely this template.  Concrete counterexamples are given per msg.

   FIX (out of scope here -- changes the .fsti / Messages spec, which the
   task forbids): strengthen [L.is_valid_<msg>] so it pins every serialized
   field of [m] (or add preconditions to the .fsti that do so).  Once [m]
   is determined by [l], the 9-step Finished/CertificateVerify template
   scales directly (pair-vmatch via LPC.vmatch_pair, lvec leaves via
   LSeqB.vmatch_copy_seqbytes, extension/entry lists via
   PPVCL.vmatch_vclist + vmatch_vclist_some_intro, exactly as sketched in
   the task's per-message shapes).

   ---------------------------------------------------------------------
   // TODO-BUILD: serialize_certificate_from_credential (Certificate)
   //   is_valid_certificate_msg pins ONLY the raw DER bytes of each entry
   //   (Impl.Messages.certificate_chain_matches checks
   //      Seq.equal cert_der (Seq.slice storage offset (offset+cert_len))).
   //   It does NOT constrain certificateEntry.extensions : list
   //   extensionCertificate (CertificateEntry_extensions.fsti: a free
   //   0..65535 list).  Counterexample: cert1, cert2 with identical
   //   certificate_list DER but cert1's entry has extensions=[] and cert2's
   //   has one extension; both satisfy is_valid_certificate_msg lcert _,
   //   both have certificate_entries == [der], but
   //   serialize_handshake (M.Certificate cert1) <> ...cert2.
   //   BLOCKED until is_valid_certificate_msg also pins each entry's
   //   extensions (e.g. forces them empty for this profile).

   // TODO-BUILD: serialize_server_hello_from_selection (ServerHello)
   //   + serialize_server_hello_record_from_selection.
   //   is_valid_server_hello pins ONLY random / key_share(x25519) /
   //   cipher_suite.  serverHelloBody (ServerHelloBody.fsti) additionally
   //   carries legacy_session_id_echo (vlbytes 0..32), a FREE
   //   legacy_compression_method : U8.t, and a free extensions list (plus
   //   serverHello.legacy_version) -- none constrained by is_valid.
   //   Counterexample: sh1, sh2 identical except
   //   legacy_compression_method = 0uy vs 1uy.  Both satisfy
   //   is_valid_server_hello lsh _ and are 90 bytes, but their wire
   //   serializations differ in that one byte.
   //   BLOCKED until is_valid_server_hello pins compression, session_id,
   //   legacy_version and the full extension list (contents + order).

   // TODO-BUILD: serialize_client_hello_from_start (ClientHello, record-
   //   level, dual output).  is_valid_client_hello pins ONLY random / SNI /
   //   key_share(x25519) / cipher_suites / signature_schemes.  clientHello
   //   also has legacy_version, legacy_session_id, legacy_compression_
   //   methods and many other extensions whose contents AND ordering are
   //   unconstrained.  Same unsatisfiability as ServerHello, a fortiori.
   //   BLOCKED until is_valid_client_hello pins every serialized field.
   ===================================================================== *)
