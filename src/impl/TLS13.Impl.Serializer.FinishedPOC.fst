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
module SM = Pulse.Lib.SeqMatch
module LPITE = LowParse.PulseParse.IfThenElse
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GESHKS = TLS13.Wire.Generated.ExtensionServerHello_extension_data_key_share
module GCert = TLS13.Wire.Generated.Certificate
module GCertE = TLS13.Wire.Generated.CertificateEntry
module GCL = TLS13.Wire.Generated.Certificate_certificate_list
module GEX = TLS13.Wire.Generated.CertificateEntry_extensions
module GECert = TLS13.Wire.Generated.ExtensionCertificate
module LPL = LowParse.Spec.List

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


(* ===================================================================== *)
(* ServerHello: BUILD via the generated copyful writer, RESOLVED by       *)
(* pinning the erased high record to its canonical (key_share-only) form.  *)
(* See the POC contract precondition + notes on serialize_server_hello_*.  *)
(* ===================================================================== *)
(* ---- canonical record (transparent copy of the non-HRR branch of
   TLS13.Impl.Server.Send.mk_server_hello_witness) ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
let poc_canonical_sh (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Pure GSH.serverHello
    (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
    (ensures fun _ -> True)
  = let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    let exts : GSHBody.serverHelloBody_extensions = [ks_ext] in
    let sid : GSHBody.serverHelloBody_legacy_session_id_echo = B.empty in
    let body : GSHBody.serverHelloBody = {
      GSHBody.legacy_session_id_echo = sid;
      GSHBody.cipher_suite = cs;
      GSHBody.legacy_compression_method = 0uy;
      GSHBody.extensions = exts;
    } in
    let r32 : Seq.lseq U8.t 32 = rnd in
    let bf : GSHB.serverHello_body_false = { GSHB.tag = r32; GSHB.value = body } in
    { GSH.legacy_version = GPV.TLS_1p2; GSH.body = GSHB.ServerHello_body_false bf }

(* ---- canonical mid ---- *)
let poc_sh_mid (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Pure GSH.serverHello_mid
    (requires Seq.length rnd == 32 /\ Seq.length ks == 32)
    (ensures fun _ -> True)
  = let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) } in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share (kse <: GESH.extensionServerHello_extension_data_key_share) in
    let exts : list GESH.extensionServerHello = [ks_ext] in
    let shbody_mid : GSHBody.serverHelloBody_mid = (((B.empty <: Seq.seq U8.t), cs), (0uy, exts)) in
    let body_mid : GSHB.serverHello_body_mid = ((rnd <: Seq.seq U8.t), (| false, shbody_mid |)) in
    (GPV.TLS_1p2, body_mid)
#pop-options

(* ---- forward conv lemma: the canonical mid converts to the canonical record ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_sh_conv_fwd (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures GSH.serverHello_conv (poc_sh_mid rnd ks cs) == Some (poc_canonical_sh rnd ks cs))
  = GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) } in
    let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
    (* (a) key_exchange vlbytes conv *)
    assert (GKSE.keyShareEntry_key_exchange_conv (ks <: GKSE.keyShareEntry_key_exchange_mid)
              == Some (ks <: GKSE.keyShareEntry_key_exchange));
    (* (b) keyShareEntry pair conv *)
    assert (GKSE.keyShareEntry_conv ((GNG.X25519, ks) <: GKSE.keyShareEntry_mid) == Some kse);
    (* (c) key_share extension vldata conv *)
    assert (GESHKS.extensionServerHello_extension_data_key_share_conv ((GNG.X25519, ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid)
              == Some ksesh);
    (* (d) extensionServerHello sum conv *)
    assert (GESH.extensionServerHello_conv (GESH.Extension_data_key_share_mid ((GNG.X25519, ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid))
              == Some ks_ext);
    (* (e) extensions list vldata conv *)
    assert (GSHBody.serverHelloBody_extensions_conv ([ks_ext] <: GSHBody.serverHelloBody_extensions_mid)
              == Some ([ks_ext] <: GSHBody.serverHelloBody_extensions));
    ()
#pop-options

(* ---- size lemma: the canonical ServerHello handshake message is 84 bytes ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_sh_size (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures GHS.handshake_bytesize (GHS.Body_server_hello (poc_canonical_sh rnd ks cs)) == 84)
  = let sh = poc_canonical_sh rnd ks cs in
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p2;
    GCS.cipherSuite_bytesize_eq cs;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    ()
#pop-options

(* ===================================================================== *)
(* Intro ghost helpers (inverses of Impl.Parser elim chain, copied)      *)
(* ===================================================================== *)

(* Re-pack an (unfolded) keyShareEntry vmatch_pair back into [keyShareEntry_vmatch]. *)
ghost
fn repack_kse (v0: GKSE.keyShareEntry_lowtype) (#cm: Ghost.erased GKSE.keyShareEntry_mid)
  requires V.pts_to (snd v0).PPBY.lvec_vec (snd cm) **
           pure (V.is_full_vec (snd v0).PPBY.lvec_vec /\ fst v0 == reveal (fst cm))
  ensures GKSE.keyShareEntry_vmatch v0 cm
{
  fold (LSeqB.vmatch_copy_seqbytes (snd v0) (snd cm));
  rewrite (LSeqB.vmatch_copy_seqbytes (snd v0) (snd cm))
      as (GKSE.keyShareEntry_key_exchange_vmatch (snd v0) (snd cm));
  fold (LPS.eq_as_slprop GNG.namedGroup (fst v0) (fst cm));
  rewrite (LPS.eq_as_slprop GNG.namedGroup (fst v0) (fst cm))
      as (GNG.namedGroup_vmatch (fst v0) (fst cm));
  fold (LPC.vmatch_pair GNG.namedGroup_vmatch GKSE.keyShareEntry_key_exchange_vmatch v0 cm);
  rewrite (LPC.vmatch_pair GNG.namedGroup_vmatch GKSE.keyShareEntry_key_exchange_vmatch v0 cm)
      as (GKSE.keyShareEntry_vmatch v0 cm);
}

(* Re-pack a keyShareEntry vmatch_pair back into a key_share element. *)
ghost
fn intro_vmatch_extSH_key_share
  (v0: GESH.extensionServerHello_extension_data_key_share_lowtype)
  (cm: GESH.extensionServerHello_extension_data_key_share_mid)
  (#h: GESH.extensionServerHello)
  requires GKSE.keyShareEntry_vmatch v0 cm **
           pure (GESH.extensionServerHello_conv
                   (GESH.Extension_data_key_share_mid cm) == Some h)
  ensures PPB.vmatch_conv GESH.extensionServerHello_vmatch
            GESH.extensionServerHello_conv
            (GESH.Extension_data_key_share_low v0) h
{
  rewrite (GKSE.keyShareEntry_vmatch v0 cm)
      as (GESH.extensionServerHello_extension_data_key_share_vmatch v0 cm);
  fold (GESH.extensionServerHello_vmatch
          (GESH.Extension_data_key_share_low v0)
          (GESH.Extension_data_key_share_mid cm));
  PPB.intro_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv
    (GESH.Extension_data_key_share_low v0)
    (GESH.Extension_data_key_share_mid cm) h;
}

(* Re-pack the session-id-echo lvec and extensions vclist into the serverHelloBody. *)
ghost
fn intro_serverHelloBody (shl: GSHBody.serverHelloBody_lowtype)
                         (#shm: GSHBody.serverHelloBody_mid)
  requires
    GSHBody.serverHelloBody_legacy_session_id_echo_vmatch (fst (fst shl)) (fst (fst shm)) **
    PPVCL.vmatch_vclist
      (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
      (snd (snd shl)) (snd (snd shm)) **
    pure (snd (fst shl) == snd (fst shm) /\ fst (snd shl) == fst (snd shm))
  ensures GSHBody.serverHelloBody_vmatch shl shm
{
  rewrite (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
            (snd (snd shl)) (snd (snd shm)))
      as (GSHBody.serverHelloBody_extensions_vmatch (snd (snd shl)) (snd (snd shm)));
  fold (LPS.eq_as_slprop U8.t (fst (snd shl)) (fst (snd shm)));
  fold (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch
          (snd shl) (snd shm));
  fold (LPS.eq_as_slprop GCS.cipherSuite (snd (fst shl)) (snd (fst shm)));
  rewrite (LPS.eq_as_slprop GCS.cipherSuite (snd (fst shl)) (snd (fst shm)))
      as (GCS.cipherSuite_vmatch (snd (fst shl)) (snd (fst shm)));
  fold (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch
          (fst shl) (fst shm));
  fold (LPC.vmatch_pair
          (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch)
          (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch)
          shl shm);
  rewrite (LPC.vmatch_pair
            (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch)
            (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch)
            shl shm)
      as (GSHBody.serverHelloBody_vmatch shl shm);
}

(* Re-pack the [serverHelloBody_vmatch] payload back into the ite payload. *)
ghost
fn intro_sh_ite_payload (xsh: GSH.serverHello_lowtype) (b: bool) (#cm: GSH.serverHello_mid)
  requires GSHBody.serverHelloBody_vmatch (dsnd (snd (snd xsh))) (dsnd (snd (snd cm))) **
           pure (b == dfst (snd (snd xsh)) /\ b == dfst (snd (snd cm)))
  ensures LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
            (snd (snd xsh)) (snd (snd cm))
{
  rewrite (GSHBody.serverHelloBody_vmatch (dsnd (snd (snd xsh))) (dsnd (snd (snd cm))))
      as (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (| b, dsnd (snd (snd xsh)) |) (snd (snd cm)));
  rewrite (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (| b, dsnd (snd (snd xsh)) |) (snd (snd cm)))
      as (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (snd (snd xsh)) (snd (snd cm)));
}

(* Re-pack the random tag lvec and ite payload into the serverHello read result. *)
ghost
fn intro_serverHello_body (xsh: GSH.serverHello_lowtype) (#cm: GSH.serverHello_mid)
  requires
    LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)) **
    LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
      (snd (snd xsh)) (snd (snd cm)) **
    pure (fst xsh == fst cm /\
          (match GSHB.serverHello_body_random_conv (fst (snd cm)) with
           | Some t -> GSHB.serverHello_body_cond t == dfst (snd (snd cm))
           | None -> True))
  ensures GSH.serverHello_vmatch xsh cm
{
  fold (LPS.eq_as_slprop GPV.protocolVersion (fst xsh) (fst cm));
  rewrite (LPS.eq_as_slprop GPV.protocolVersion (fst xsh) (fst cm))
      as (GPV.protocolVersion_vmatch (fst xsh) (fst cm));
  rewrite (LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)))
      as (GSHB.serverHello_body_random_vmatch (fst (snd xsh)) (fst (snd cm)));
  fold (LPITE.vmatch_ite GSHB.serverHello_body_random_vmatch GSHB.serverHello_body_cond
          GSHB.serverHello_body_random_conv GSHB.serverHello_body_payload_vmatch
          (snd xsh) (snd cm));
  rewrite (LPITE.vmatch_ite GSHB.serverHello_body_random_vmatch GSHB.serverHello_body_cond
            GSHB.serverHello_body_random_conv GSHB.serverHello_body_payload_vmatch
            (snd xsh) (snd cm))
      as (GSHB.serverHello_body_vmatch (snd xsh) (snd cm));
  fold (LPC.vmatch_pair GPV.protocolVersion_vmatch GSHB.serverHello_body_vmatch xsh cm);
  rewrite (LPC.vmatch_pair GPV.protocolVersion_vmatch GSHB.serverHello_body_vmatch xsh cm)
      as (GSH.serverHello_vmatch xsh cm);
}

(* Fold the serverHello vmatch directly into the handshake sum vmatch (the first
   two steps of Impl.Parser.intro_vmatch_server_hello, WITHOUT the read-side
   vmatch_conv wrapper -- the writer wants [handshake_vmatch], not the conv). *)
ghost
fn intro_handshake_server_hello_vmatch
  (xsh: GHS.handshake_body_server_hello_lowtype)
  (cm: GSH.serverHello_mid)
  requires GSH.serverHello_vmatch xsh cm
  ensures GHS.handshake_vmatch (GHS.Body_server_hello_low xsh) (GHS.Body_server_hello_mid cm)
{
  rewrite (GSH.serverHello_vmatch xsh cm)
      as (GHS.handshake_body_server_hello_vmatch xsh cm);
  fold (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh)
          (GHS.Body_server_hello_mid cm));
}

(* ===================================================================== *)
(* Sem-connection + handshake-level conv lemmas                          *)
(* ===================================================================== *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_canonical_random (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures Sem.serverHello_random (poc_canonical_sh rnd ks cs) == Some (rnd <: Seq.lseq U8.t 32))
  = ()

let lemma_canonical_key_share (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures Sem.serverHello_key_share_x25519 (poc_canonical_sh rnd ks cs) == Some (ks <: Seq.seq U8.t))
  = ()

let lemma_canonical_cs (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures Sem.serverHello_cipher_suite (poc_canonical_sh rnd ks cs) == Some cs)
  = ()

let lemma_ks_ext_conv (ks: B.bytes)
  : Lemma (requires Seq.length ks == 32)
          (ensures GESH.extensionServerHello_conv
                     (GESH.Extension_data_key_share_mid ((GNG.X25519, ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid))
                   == Some (GESH.Extension_data_key_share
                             (({ GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) })
                              <: GESH.extensionServerHello_extension_data_key_share)))
  = GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    ()

let lemma_sh_handshake_conv_fwd (rnd ks: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32)
          (ensures GHS.handshake_conv (GHS.Body_server_hello_mid (poc_sh_mid rnd ks cs))
                     == Some (GHS.Body_server_hello (poc_canonical_sh rnd ks cs)))
  = lemma_sh_conv_fwd rnd ks cs
#pop-options

(* ===================================================================== *)
(* Main: serialize a canonical ServerHello handshake message (84 bytes)  *)
(* ===================================================================== *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
fn serialize_server_hello_handshake_poc
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old: erased B.bytes)
  requires L.is_valid_server_hello lsh (reveal sh) ** A.pts_to out (reveal old) **
           pure (B.length (reveal old) == SZ.v out_len /\ SZ.v out_len == 84 /\
                 Seq.length (reveal rnd) == 32 /\
                 (reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 Seq.length (reveal ks) == 32 /\
                 reveal cs == GCS.TLS_CHACHA20_POLY1305_SHA256 /\
                 Ghost.reveal sh == poc_canonical_sh (reveal rnd) (reveal ks) (reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (reveal sh) ** A.pts_to out out_bytes **
          pure (B.length out_bytes == 84 /\ SZ.v written == 84 /\
                Seq.equal out_bytes (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  unfold (L.is_valid_server_hello lsh (reveal sh));
  with random. assert (V.pts_to lsh.L.server_hello_random random);
  with key_share. assert (V.pts_to lsh.L.server_hello_key_share key_share);
  lemma_canonical_random (reveal rnd) (reveal ks) (reveal cs);
  lemma_canonical_key_share (reveal rnd) (reveal ks) (reveal cs);
  Seq.lemma_eq_elim random (reveal rnd);
  Seq.lemma_eq_elim key_share (reveal ks);
  (* copy random & key_share into fresh exact-32 vecs; is_valid stays intact *)
  V.pts_to_len lsh.L.server_hello_random;
  let rnd_vec = alloc_copy_vec_exact lsh.L.server_hello_random 32sz 32sz;
  with rnd_copy. assert (V.pts_to rnd_vec rnd_copy);
  Seq.lemma_eq_elim rnd_copy (reveal rnd);
  V.pts_to_len lsh.L.server_hello_key_share;
  let ks_vec = alloc_copy_vec_exact lsh.L.server_hello_key_share 32sz 32sz;
  with ks_copy. assert (V.pts_to ks_vec ks_copy);
  Seq.lemma_eq_elim ks_copy (reveal ks);
  fold (L.is_valid_server_hello lsh (reveal sh));
  rewrite (V.pts_to rnd_vec rnd_copy) as (V.pts_to rnd_vec (reveal rnd));
  rewrite (V.pts_to ks_vec ks_copy) as (V.pts_to ks_vec (reveal ks));

  (* ---- key_share entry vmatch ---- *)
  let ks_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = ks_vec; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to ks_vec (reveal ks)) as (V.pts_to ks_lvec.PPBY.lvec_vec (reveal ks));
  let kse_low : GKSE.keyShareEntry_lowtype = (GNG.X25519, ks_lvec);
  rewrite (V.pts_to ks_lvec.PPBY.lvec_vec (reveal ks))
      as (V.pts_to (snd kse_low).PPBY.lvec_vec (reveal ks));
  repack_kse kse_low #(Ghost.hide ((GNG.X25519, reveal ks) <: GKSE.keyShareEntry_mid));

  (* ---- key_share extension element vmatch_conv ---- *)
  let ks_ext : Ghost.erased GESH.extensionServerHello =
    Ghost.hide (GESH.Extension_data_key_share
      (({ GKSE.group = GNG.X25519; GKSE.key_exchange = (reveal ks <: GKSE.keyShareEntry_key_exchange) })
       <: GESH.extensionServerHello_extension_data_key_share));
  lemma_ks_ext_conv (reveal ks);
  intro_vmatch_extSH_key_share kse_low ((GNG.X25519, reveal ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid) #(Ghost.reveal ks_ext);
  let ext_low : GESH.extensionServerHello_lowtype = GESH.Extension_data_key_share_low kse_low;
  rewrite (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             (GESH.Extension_data_key_share_low kse_low) (Ghost.reveal ks_ext))
      as (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             ext_low (Ghost.reveal ks_ext));

  (* ---- singleton extensions vclist ---- *)
  let ext_vec = V.alloc ext_low 1sz;
  SM.seq_list_match_nil_intro (Seq.empty #GESH.extensionServerHello_lowtype) ([] <: list GESH.extensionServerHello)
    (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv);
  SM.seq_list_match_cons_intro ext_low (Ghost.reveal ks_ext) (Seq.empty #GESH.extensionServerHello_lowtype) ([] <: list GESH.extensionServerHello)
    (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv);
  Seq.lemma_eq_elim (Seq.create 1 ext_low) (Seq.cons ext_low (Seq.empty #GESH.extensionServerHello_lowtype));
  rewrite (SM.seq_list_match (Seq.cons ext_low (Seq.empty #GESH.extensionServerHello_lowtype)) [Ghost.reveal ks_ext]
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv))
       as (SM.seq_list_match (Seq.create 1 ext_low) [Ghost.reveal ks_ext]
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
  let exts_low = PPVCL.vmatch_vclist_some_intro 1sz ext_vec #(Seq.create 1 ext_low) #[Ghost.reveal ks_ext] [Ghost.reveal ks_ext];

  (* ---- empty session-id-echo lvec ---- *)
  let sid_vec = V.alloc 0uy 0sz;
  Seq.lemma_eq_elim (Seq.create 0 0uy) (B.empty <: Seq.seq U8.t);
  rewrite (V.pts_to sid_vec (Seq.create 0 0uy)) as (V.pts_to sid_vec (B.empty <: Seq.seq U8.t));
  let sid_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = sid_vec; PPBY.lvec_len = 0sz };
  rewrite (V.pts_to sid_vec (B.empty <: Seq.seq U8.t)) as (V.pts_to sid_lvec.PPBY.lvec_vec (B.empty <: Seq.seq U8.t));
  fold (LSeqB.vmatch_copy_seqbytes sid_lvec (B.empty <: Seq.seq U8.t));
  rewrite (LSeqB.vmatch_copy_seqbytes sid_lvec (B.empty <: Seq.seq U8.t))
       as (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch sid_lvec (B.empty <: Seq.seq U8.t));

  (* ---- serverHelloBody vmatch ---- *)
  let shbody_low : GSHBody.serverHelloBody_lowtype =
    ((sid_lvec, GCS.TLS_CHACHA20_POLY1305_SHA256), (0uy, exts_low));
  let shm : Ghost.erased GSHBody.serverHelloBody_mid =
    Ghost.hide (((B.empty <: Seq.seq U8.t), reveal cs), (0uy, ([Ghost.reveal ks_ext] <: list GESH.extensionServerHello)));
  rewrite (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch sid_lvec (B.empty <: Seq.seq U8.t))
      as (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch (fst (fst shbody_low)) (fst (fst (Ghost.reveal shm))));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
             exts_low [Ghost.reveal ks_ext])
      as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
             (snd (snd shbody_low)) (snd (snd (Ghost.reveal shm))));
  intro_serverHelloBody shbody_low #(Ghost.reveal shm);

  (* ---- ite payload (false branch) + random tag ---- *)
  let cm : Ghost.erased GSH.serverHello_mid =
    Ghost.hide (poc_sh_mid (reveal rnd) (reveal ks) (reveal cs));
  let rnd_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = rnd_vec; PPBY.lvec_len = 32sz };
  let sh_body_low : GSHB.serverHello_body_lowtype = (rnd_lvec, (| false, shbody_low |));
  let xsh : GSH.serverHello_lowtype = (GPV.TLS_1p2, sh_body_low);
  rewrite (GSHBody.serverHelloBody_vmatch shbody_low (Ghost.reveal shm))
      as (GSHBody.serverHelloBody_vmatch (dsnd (snd (snd xsh))) (dsnd (snd (snd (Ghost.reveal cm)))));
  intro_sh_ite_payload xsh false #(Ghost.reveal cm);

  rewrite (V.pts_to rnd_vec (reveal rnd)) as (V.pts_to rnd_lvec.PPBY.lvec_vec (reveal rnd));
  fold (LSeqB.vmatch_copy_seqbytes rnd_lvec (reveal rnd));
  rewrite (LSeqB.vmatch_copy_seqbytes rnd_lvec (reveal rnd))
      as (LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd (Ghost.reveal cm))));
  intro_serverHello_body xsh #(Ghost.reveal cm);

  (* ---- handshake sum vmatch ---- *)
  intro_handshake_server_hello_vmatch xsh (Ghost.reveal cm);

  (* ---- write ---- *)
  A.pts_to_len out;
  let s = S.from_array out out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_server_hello_low xsh)
             #(Ghost.hide (GHS.Body_server_hello_mid (Ghost.reveal cm)))
             s perr;
  with v'. assert (S.pts_to s v');
  lemma_sh_handshake_conv_fwd (reveal rnd) (reveal ks) (reveal cs);
  lemma_sh_size (reveal rnd) (reveal ks) (reveal cs);
  GHS.handshake_bytesize_eq (GHS.Body_server_hello (poc_canonical_sh (reveal rnd) (reveal ks) (reveal cs)));
  S.to_array s;
  A.pts_to_len out;
  WS.lemma_serialize_handshake_server_hello (Ghost.reveal sh);
  GHS.free_handshake (GHS.Body_server_hello_low xsh) #(Ghost.hide (GHS.Body_server_hello_mid (Ghost.reveal cm)));
  sz
}
#pop-options

(* =====================================================================
   Certificate: BUILD via the generated copyful writer, RESOLVED by
   pinning the erased high record to its canonical single-entry form
   (empty request_context, one entry holding the whole chain DER with
   empty entry-extensions).  Mirrors TLS13.Impl.Server.Send.mk_cert_witness.
   ===================================================================== *)
(* ---- canonical entry + record (transparent copy of mk_cert_witness) ---- *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let poc_cert_entry (chain: B.bytes)
  : Pure GCertE.certificateEntry
    (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
    (ensures fun _ -> True)
  = { GCertE.cert_data = (chain <: GCertE.certificateEntry_cert_data);
      GCertE.extensions = ([] <: GCertE.certificateEntry_extensions) }

let poc_canonical_cert (chain: B.bytes)
  : Pure GCert.certificate
    (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
    (ensures fun c -> Sem.certificate_entries c == [ (chain <: Seq.seq U8.t) ] /\
                   GCert.certificate_bytesize c <= 16777215)
  = let cd : GCertE.certificateEntry_cert_data = chain in
    let ex : GCertE.certificateEntry_extensions = [] in
    let entry : GCertE.certificateEntry = { GCertE.cert_data = cd; GCertE.extensions = ex } in
    GEX.certificateEntry_extensions_list_bytesize_nil;
    GCL.certificate_certificate_list_list_bytesize_nil;
    assert (GCL.certificate_certificate_list_list_bytesize [entry] ==
            GCertE.certificateEntry_bytesize entry);
    let cl : GCert.certificate_certificate_list = [entry] in
    let rc : GCert.certificate_certificate_request_context = B.empty in
    { GCert.certificate_request_context = rc; GCert.certificate_list = cl }
#pop-options

(* ---- canonical mid ---- *)
let poc_cert_mid (chain: B.bytes)
  : Pure GCert.certificate_mid
    (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
    (ensures fun _ -> True)
  = ((B.empty <: Seq.seq U8.t),
     ([ poc_cert_entry chain ] <: list GCertE.certificateEntry))

(* ---- entry-level conv ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"
let lemma_cert_entry_conv (chain: B.bytes)
  : Lemma (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
          (ensures GCertE.certificateEntry_conv
                     (((chain <: Seq.seq U8.t), ([] <: list GECert.extensionCertificate))
                      <: GCertE.certificateEntry_mid)
                   == Some (poc_cert_entry chain))
  = LPL.serialize_list_nil _ GECert.extensionCertificate_serializer;
    ()
#pop-options

(* ---- certificate-level conv ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"
let lemma_cert_conv_fwd (chain: B.bytes)
  : Lemma (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
          (ensures GCert.certificate_conv (poc_cert_mid chain)
                   == Some (poc_canonical_cert chain))
  = lemma_cert_entry_conv chain;
    LPL.serialize_list_singleton _ GCertE.certificateEntry_serializer (poc_cert_entry chain);
    GEX.certificateEntry_extensions_list_bytesize_nil;
    GCL.certificate_certificate_list_list_bytesize_nil;
    ()
#pop-options

(* ---- bytesize bound (for WS.lemma_serialize_handshake_certificate guard) ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"
let lemma_cert_bytesize (chain: B.bytes)
  : Lemma (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
          (ensures GCert.certificate_bytesize (poc_canonical_cert chain) <= 16777215)
  = GEX.certificateEntry_extensions_list_bytesize_nil;
    GCL.certificate_certificate_list_list_bytesize_nil;
    ()
#pop-options

(* ---- handshake-level conv (wraps the handshake-body vldata 0..16777215) ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"
let lemma_cert_handshake_conv_fwd (chain: B.bytes)
  : Lemma (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
          (ensures GHS.handshake_conv (GHS.Body_certificate_mid (poc_cert_mid chain))
                   == Some (GHS.Body_certificate
                             ((poc_canonical_cert chain) <: GHS.handshake_body_certificate)))
  = lemma_cert_conv_fwd chain;
    lemma_cert_bytesize chain;
    ()
#pop-options

(* ---- extract count==1 + the single entry's (offset,len,slice) facts from
   the recursive certificate_chain_matches predicate, specialised to [chain] ---- *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let lemma_chain_extract
  (storage: B.bytes) (storage_len: nat) (offsets lens: Seq.seq SZ.t) (count: nat) (chain: B.bytes)
  : Lemma
    (requires
      L.certificate_chain_matches storage storage_len offsets lens count
        [ (chain <: Seq.seq U8.t) ] /\
      Seq.length offsets >= 1 /\ Seq.length lens >= 1)
    (ensures
      count == 1 /\
      storage_len <= B.length storage /\
      SZ.v (Seq.index offsets 0) + SZ.v (Seq.index lens 0) <= storage_len /\
      Seq.length (chain <: Seq.seq U8.t) == SZ.v (Seq.index lens 0) /\
      Seq.equal (chain <: Seq.seq U8.t)
                (Seq.slice storage (SZ.v (Seq.index offsets 0))
                                   (SZ.v (Seq.index offsets 0) + SZ.v (Seq.index lens 0))))
  = Seq.lemma_len_slice storage (SZ.v (Seq.index offsets 0))
                                (SZ.v (Seq.index offsets 0) + SZ.v (Seq.index lens 0))
#pop-options

(* ---- materialise the [poc_canonical_cert] post: its entry list is [chain] ---- *)
let lemma_cert_entries (chain: B.bytes)
  : Lemma (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
          (ensures Sem.certificate_entries (poc_canonical_cert chain)
                   == [ (chain <: Seq.seq U8.t) ])
  = ()

(* Copy the sub-region [src[off..off+len)] of a (full) source Vec into a fresh
   exact-[len] Vec; preserves [src].  Inverse of [copy_vec_into_at]. *)
inline_for_extraction
fn alloc_copy_subslice (src: V.vec U8.t) (off: SZ.t) (len: SZ.t) (cap: SZ.t)
  requires V.pts_to src 'src_bytes **
           pure (V.is_full_vec src /\ V.length src == SZ.v cap /\
                 SZ.v off + SZ.v len <= SZ.v cap /\
                 Seq.length (Ghost.reveal 'src_bytes) == SZ.v cap)
  returns dst: V.vec U8.t
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v len /\
                  B.length dst_bytes == SZ.v len /\
                  Seq.length (Ghost.reveal 'src_bytes) == SZ.v cap /\
                  SZ.v off + SZ.v len <= SZ.v cap /\
                  Seq.equal dst_bytes
                    (Seq.slice (Ghost.reveal 'src_bytes) (SZ.v off) (SZ.v off + SZ.v len))))
{
  let dst = V.alloc 0uy len;
  V.pts_to_len src;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) cap;
  S.pts_to_len src_slice;
  let sp1 = S.split src_slice off;
  S.pts_to_len (fst sp1);
  S.pts_to_len (snd sp1);
  let sp2 = S.split (snd sp1) len;
  S.pts_to_len (fst sp2);
  S.pts_to_len (snd sp2);
  let dst_slice = S.from_array (V.vec_to_array dst) len;
  S.pts_to_len dst_slice;
  S.copy dst_slice (fst sp2);
  Seq.slice_slice (Ghost.reveal 'src_bytes) (SZ.v off) (SZ.v cap) 0 (SZ.v len);
  Seq.lemma_split (Seq.slice (Ghost.reveal 'src_bytes) (SZ.v off) (SZ.v cap)) (SZ.v len);
  S.join (fst sp2) (snd sp2) (snd sp1);
  Seq.lemma_split (Ghost.reveal 'src_bytes) (SZ.v off);
  S.join (fst sp1) (snd sp1) src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  dst
}

(* Re-pack a certificateEntry's cert_data lvec and (empty) extensions vclist
   into the read result (verbatim port of Impl.Parser.intro_cert_entry). *)
ghost
fn intro_cert_entry (el: GCertE.certificateEntry_lowtype) (#em: GCertE.certificateEntry_mid)
  requires LSeqB.vmatch_copy_seqbytes (fst el) (fst em) **
           GCertE.certificateEntry_extensions_vmatch (snd el) (snd em)
  ensures GCertE.certificateEntry_vmatch el em
{
  rewrite (LSeqB.vmatch_copy_seqbytes (fst el) (fst em))
      as (GCertE.certificateEntry_cert_data_vmatch (fst el) (fst em));
  fold (LPC.vmatch_pair GCertE.certificateEntry_cert_data_vmatch
          GCertE.certificateEntry_extensions_vmatch el em);
  rewrite (LPC.vmatch_pair GCertE.certificateEntry_cert_data_vmatch
            GCertE.certificateEntry_extensions_vmatch el em)
      as (GCertE.certificateEntry_vmatch el em);
}

(* Fold the certificate vmatch directly into the handshake sum vmatch (the first
   steps of Impl.Parser.intro_vmatch_certificate WITHOUT the read-side
   vmatch_conv wrapper -- the writer wants bare [handshake_vmatch]). *)
ghost
fn intro_handshake_certificate_vmatch
  (xcert: GHS.handshake_body_certificate_lowtype)
  (cm: GHS.handshake_body_certificate_mid)
  requires LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm) **
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv)
             (snd xcert) (snd cm)
  ensures GHS.handshake_vmatch (GHS.Body_certificate_low xcert) (GHS.Body_certificate_mid cm)
{
  rewrite (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv)
            (snd xcert) (snd cm))
      as (GCert.certificate_certificate_list_vmatch (snd xcert) (snd cm));
  rewrite (LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm))
      as (GCert.certificate_certificate_request_context_vmatch (fst xcert) (fst cm));
  fold (LPC.vmatch_pair GCert.certificate_certificate_request_context_vmatch
          GCert.certificate_certificate_list_vmatch xcert cm);
  rewrite (LPC.vmatch_pair GCert.certificate_certificate_request_context_vmatch
            GCert.certificate_certificate_list_vmatch xcert cm)
      as (GHS.handshake_body_certificate_vmatch xcert cm);
  fold (GHS.handshake_vmatch (GHS.Body_certificate_low xcert)
          (GHS.Body_certificate_mid cm));
}

(* ===================================================================== *)
(* Certificate: BUILD via the generated copyful writer, pinned to the     *)
(* canonical single-entry / empty-context / empty-ext-extensions form.    *)
(* ===================================================================== *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
fn serialize_certificate_handshake_poc
  (#cert: erased GCert.certificate)
  (#chain: erased B.bytes)
  (lcert: L.certificate_msg)
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old: erased B.bytes)
  requires L.is_valid_certificate_msg lcert (reveal cert) ** A.pts_to out (reveal old) **
           pure (B.length (reveal old) == SZ.v out_len /\
                 1 <= Seq.length (reveal chain) /\ Seq.length (reveal chain) <= 32768 /\
                 Ghost.reveal cert == poc_canonical_cert (reveal chain) /\
                 SZ.v out_len == B.length (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg lcert (reveal cert) ** A.pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
{
  unfold (L.is_valid_certificate_msg lcert (reveal cert));
  with cb. assert (V.pts_to lcert.L.certificate_msg_chain_bytes cb);
  with offs. assert (V.pts_to lcert.L.certificate_msg_cert_offsets offs);
  with lns. assert (V.pts_to lcert.L.certificate_msg_cert_lens lns);
  lemma_cert_entries (reveal chain);
  V.pts_to_len lcert.L.certificate_msg_chain_bytes;
  V.pts_to_len lcert.L.certificate_msg_cert_offsets;
  V.pts_to_len lcert.L.certificate_msg_cert_lens;
  lemma_chain_extract cb (SZ.v lcert.L.certificate_msg_chain_bytes_len) offs lns
    (SZ.v lcert.L.certificate_msg_cert_count) (reveal chain);
  let off0 = V.op_Array_Access lcert.L.certificate_msg_cert_offsets 0sz;
  let len0 = V.op_Array_Access lcert.L.certificate_msg_cert_lens 0sz;
  let chain_vec = alloc_copy_subslice lcert.L.certificate_msg_chain_bytes off0 len0 32768sz;
  with cv_bytes. assert (V.pts_to chain_vec cv_bytes);
  Seq.lemma_eq_elim cv_bytes (reveal chain);
  fold (L.is_valid_certificate_msg lcert (reveal cert));
  rewrite (V.pts_to chain_vec cv_bytes) as (V.pts_to chain_vec (reveal chain));

  (* ---- cert_data lvec (the DER blob) ---- *)
  let cd_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = chain_vec; PPBY.lvec_len = len0 };
  rewrite (V.pts_to chain_vec (reveal chain)) as (V.pts_to cd_lvec.PPBY.lvec_vec (reveal chain));
  fold (LSeqB.vmatch_copy_seqbytes cd_lvec (reveal chain));

  (* ---- empty extensions vclist (None) ---- *)
  let ext_low : GCertE.certificateEntry_extensions_lowtype =
    None #(SZ.t & V.vec GECert.extensionCertificate_lowtype);
  fold (PPVCL.vmatch_vclist
          (PPB.vmatch_conv GECert.extensionCertificate_vmatch GECert.extensionCertificate_conv)
          (None #(SZ.t & V.vec GECert.extensionCertificate_lowtype))
          ([] <: list GECert.extensionCertificate));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECert.extensionCertificate_vmatch GECert.extensionCertificate_conv)
             (None #(SZ.t & V.vec GECert.extensionCertificate_lowtype))
             ([] <: list GECert.extensionCertificate))
      as (GCertE.certificateEntry_extensions_vmatch ext_low ([] <: list GECert.extensionCertificate));

  (* ---- certificateEntry vmatch ---- *)
  let entry_low : GCertE.certificateEntry_lowtype = (cd_lvec, ext_low);
  let entry_mid : Ghost.erased GCertE.certificateEntry_mid =
    Ghost.hide (((reveal chain <: Seq.seq U8.t), ([] <: list GECert.extensionCertificate)));
  rewrite (LSeqB.vmatch_copy_seqbytes cd_lvec (reveal chain))
      as (LSeqB.vmatch_copy_seqbytes (fst entry_low) (fst (Ghost.reveal entry_mid)));
  rewrite (GCertE.certificateEntry_extensions_vmatch ext_low ([] <: list GECert.extensionCertificate))
      as (GCertE.certificateEntry_extensions_vmatch (snd entry_low) (snd (Ghost.reveal entry_mid)));
  intro_cert_entry entry_low #(Ghost.reveal entry_mid);

  (* ---- entry vmatch_conv (relate to high record) ---- *)
  let entry_high : Ghost.erased GCertE.certificateEntry =
    Ghost.hide (poc_cert_entry (reveal chain));
  lemma_cert_entry_conv (reveal chain);
  PPB.intro_vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv
    entry_low (Ghost.reveal entry_mid) (Ghost.reveal entry_high);

  (* ---- singleton certificate_list vclist ---- *)
  let entry_vec = V.alloc entry_low 1sz;
  SM.seq_list_match_nil_intro (Seq.empty #GCertE.certificateEntry_lowtype) ([] <: list GCertE.certificateEntry)
    (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv);
  SM.seq_list_match_cons_intro entry_low (Ghost.reveal entry_high) (Seq.empty #GCertE.certificateEntry_lowtype) ([] <: list GCertE.certificateEntry)
    (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv);
  Seq.lemma_eq_elim (Seq.create 1 entry_low) (Seq.cons entry_low (Seq.empty #GCertE.certificateEntry_lowtype));
  rewrite (SM.seq_list_match (Seq.cons entry_low (Seq.empty #GCertE.certificateEntry_lowtype)) [Ghost.reveal entry_high]
            (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv))
       as (SM.seq_list_match (Seq.create 1 entry_low) [Ghost.reveal entry_high]
            (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv));
  let list_low = PPVCL.vmatch_vclist_some_intro 1sz entry_vec #(Seq.create 1 entry_low) #[Ghost.reveal entry_high] [Ghost.reveal entry_high];

  (* ---- empty request_context lvec ---- *)
  let rc_vec = V.alloc 0uy 0sz;
  Seq.lemma_eq_elim (Seq.create 0 0uy) (B.empty <: Seq.seq U8.t);
  rewrite (V.pts_to rc_vec (Seq.create 0 0uy)) as (V.pts_to rc_vec (B.empty <: Seq.seq U8.t));
  let rc_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = rc_vec; PPBY.lvec_len = 0sz };
  rewrite (V.pts_to rc_vec (B.empty <: Seq.seq U8.t)) as (V.pts_to rc_lvec.PPBY.lvec_vec (B.empty <: Seq.seq U8.t));
  fold (LSeqB.vmatch_copy_seqbytes rc_lvec (B.empty <: Seq.seq U8.t));

  (* ---- assemble certificate low repr + handshake sum vmatch ---- *)
  let xcert : GHS.handshake_body_certificate_lowtype = (rc_lvec, list_low);
  let cm : Ghost.erased GHS.handshake_body_certificate_mid =
    Ghost.hide ((poc_cert_mid (reveal chain)) <: GHS.handshake_body_certificate_mid);
  rewrite (LSeqB.vmatch_copy_seqbytes rc_lvec (B.empty <: Seq.seq U8.t))
      as (LSeqB.vmatch_copy_seqbytes (fst xcert) (fst (Ghost.reveal cm)));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv)
             list_low [Ghost.reveal entry_high])
      as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCertE.certificateEntry_vmatch GCertE.certificateEntry_conv)
             (snd xcert) (snd (Ghost.reveal cm)));
  intro_handshake_certificate_vmatch xcert (Ghost.reveal cm);

  (* ---- write ---- *)
  A.pts_to_len out;
  let s = S.from_array out out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_certificate_low xcert)
             #(Ghost.hide (GHS.Body_certificate_mid (Ghost.reveal cm)))
             s perr;
  with v'. assert (S.pts_to s v');
  lemma_cert_handshake_conv_fwd (reveal chain);
  lemma_cert_bytesize (reveal chain);
  S.to_array s;
  A.pts_to_len out;
  WS.lemma_serialize_handshake_certificate (Ghost.reveal cert);
  GHS.free_handshake (GHS.Body_certificate_low xcert)
    #(Ghost.hide (GHS.Body_certificate_mid (Ghost.reveal cm)));
  sz
}
#pop-options

(* =====================================================================
   ClientHello: BUILD via the generated copyful writer is BLOCKED by a
   spec-completeness gap, NOT by proof difficulty.  (ServerHello and
   Certificate, formerly listed here, are now RESOLVED above by pinning
   the erased high record to a canonical form via a POC precondition; the
   same technique would resolve ClientHello once its canonical profile is
   fixed.)  Documented here; no ClientHello code emitted (so the module
   stays fully verified).  See the per-message note below.

   ROOT CAUSE.  The generated writer serializes the
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
   template closes.  For ServerHello/Certificate/ClientHello it does NOT:
   [is_valid_<msg>] constrains only a subset of fields, leaving the rest
   free.  Because [m] is universally quantified (erased implicit), a caller
   may pick two messages [m1 <> m2] that both satisfy [is_valid_<msg> l _]
   yet serialize to different bytes; one runtime output cannot equal both,
   so the contract is unsatisfiable as written -- by ANY implementation,
   not merely this template.  Concrete counterexamples are given per msg.

   FIX used for ServerHello/Certificate (and applicable to ClientHello):
   add a POC precondition pinning [m] to a canonical form built from the
   runtime-available fields (see serialize_server_hello_handshake_poc and
   serialize_certificate_handshake_poc).  The deeper FIX (out of scope here
   -- changes the .fsti / Messages spec, which the task forbids): strengthen
   [L.is_valid_<msg>] so it pins every serialized
   field of [m] (or add preconditions to the .fsti that do so).  Once [m]
   is determined by [l], the 9-step Finished/CertificateVerify template
   scales directly (pair-vmatch via LPC.vmatch_pair, lvec leaves via
   LSeqB.vmatch_copy_seqbytes, extension/entry lists via
   PPVCL.vmatch_vclist + vmatch_vclist_some_intro, exactly as sketched in
   the task's per-message shapes).

   ---------------------------------------------------------------------
   // RESOLVED (Certificate): serialize_certificate_handshake_poc, above.
   //   Sidestepped by PINNING the erased high record [cert] to its
   //   canonical single-entry form via a POC precondition
   //   (cert == poc_canonical_cert chain: empty certificate_request_context,
   //   exactly one certificateEntry holding the whole chain DER, with EMPTY
   //   entry-extensions), so every serialized field of [cert] is determined.
   //   The runtime single entry is reconstructed from the L mirror by
   //   extracting count==1 + (offset,len,slice) from certificate_chain_matches
   //   (lemma_chain_extract) and sub-slice-copying storage[off..off+len].
   //
   //   (Former blocker, for reference.)
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
   //   The POC precondition forces entry-extensions empty, removing the
   //   ambiguity.

   // RESOLVED (ServerHello): serialize_server_hello_handshake_poc, above.
   //   The blocker below is sidestepped by PINNING the erased high record
   //   [sh] to its canonical (key_share-only) form via a POC precondition
   //   (sh == poc_canonical_sh rnd ks cs with the cipher_suite fixed and the
   //   random cst-guard), so every serialized field of [sh] is determined.
   //   The remaining ClientHello case below is unresolved for the same
   //   under-determination reason ServerHello had before the pinning.
   //
   //   (Former blocker, for reference.)
   //   is_valid_server_hello pins ONLY random / key_share(x25519) /
   //   cipher_suite.  serverHelloBody (ServerHelloBody.fsti) additionally
   //   carries legacy_session_id_echo (vlbytes 0..32), a FREE
   //   legacy_compression_method : U8.t, and a free extensions list (plus
   //   serverHello.legacy_version) -- none constrained by is_valid.
   //   Counterexample: sh1, sh2 identical except
   //   legacy_compression_method = 0uy vs 1uy.  Both satisfy
   //   is_valid_server_hello lsh _ and are 84 bytes, but their wire
   //   serializations differ in that one byte.  The POC precondition pins
   //   these free fields, removing the ambiguity.

   // TODO-BUILD: serialize_client_hello_from_start (ClientHello, record-
   //   level, dual output).  is_valid_client_hello pins ONLY random / SNI /
   //   key_share(x25519) / cipher_suites / signature_schemes.  clientHello
   //   also has legacy_version, legacy_session_id, legacy_compression_
   //   methods and many other extensions whose contents AND ordering are
   //   unconstrained.  Same unsatisfiability as ServerHello, a fortiori.
   //   BLOCKED until is_valid_client_hello pins every serialized field.
   ===================================================================== *)
