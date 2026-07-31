module TLS13.Impl.Serializer.Handshake

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
module Rev = TLS13.Wire.Spec.Reveal.Handshake
module RevFin = TLS13.Wire.Spec.Reveal.Finished
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
module GOV = TLS13.Wire.Generated.OfferedVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GESHKS = TLS13.Wire.Generated.ExtensionServerHello_extension_data_key_share
module GCert = TLS13.Wire.Generated.Certificate
module GCertE = TLS13.Wire.Generated.CertificateEntry
module GCL = TLS13.Wire.Generated.Certificate_certificate_list
module GEX = TLS13.Wire.Generated.CertificateEntry_extensions
module GECert = TLS13.Wire.Generated.ExtensionCertificate
module LPL = LowParse.Spec.List
module GCH = TLS13.Wire.Generated.ClientHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GRND = TLS13.Wire.Generated.Random
module GKSCH = TLS13.Wire.Generated.KeyShareClientHello
module GSSL = TLS13.Wire.Generated.SignatureSchemeList
module GSN = TLS13.Wire.Generated.ServerName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GSVCH = TLS13.Wire.Generated.SupportedVersionsClientHello
module GNGL = TLS13.Wire.Generated.NamedGroupList
module GHN = TLS13.Wire.Generated.HostName
module GHCH = TLS13.Wire.Generated.Handshake_body_client_hello
module LL = FStar.List.Tot

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
  Rev.lemma_serialize_handshake_finished (Ghost.reveal fin);
  Seq.lemma_eq_elim verify_data (Ghost.reveal fin);
  RevFin.lemma_parse_finished_handshake (Ghost.reveal fin);
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
  Rev.lemma_serialize_handshake_certificate_verify (Ghost.reveal cv);
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
  Rev.lemma_serialize_handshake_encrypted_extensions ([] <: GEE.encryptedExtensions);
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
(* [poc_canonical_sh] is now declared transparently in the interface
   (TLS13.Impl.Serializer.Handshake.fsti) so downstream bridging lemmas can
   unfold it definitionally.  The canonical mid below stays private. *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
(* ---- canonical mid ---- *)
noextract
let poc_sh_mid (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Pure GSH.serverHello_mid
    (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32)
    (ensures fun _ -> True)
  = let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) } in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share (kse <: GESH.extensionServerHello_extension_data_key_share) in
    let sv_ext : GESH.extensionServerHello = GESH.Extension_data_supported_versions (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
    let exts : list GESH.extensionServerHello = [ks_ext; sv_ext] in
    let shbody_mid : GSHBody.serverHelloBody_mid = (((sid <: Seq.seq U8.t), cs), (0uy, exts)) in
    let body_mid : GSHB.serverHello_body_mid = ((rnd <: Seq.seq U8.t), (| false, shbody_mid |)) in
    (GPV.TLS_1p2, body_mid)
#pop-options

(* ---- forward conv lemma: the canonical mid converts to the canonical record ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_sh_conv_fwd (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures GSH.serverHello_conv (poc_sh_mid rnd ks sid cs) == Some (poc_canonical_sh rnd ks sid cs))
  = GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) } in
    let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
    let sv_ext : GESH.extensionServerHello = GESH.Extension_data_supported_versions (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
    GSHBody.serverHelloBody_extensions_list_bytesize_cons sv_ext [];
    GSHBody.serverHelloBody_extensions_list_bytesize_cons ks_ext [sv_ext];
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
    (* (a) key_exchange vlbytes conv *)
    assert (GKSE.keyShareEntry_key_exchange_conv (ks <: GKSE.keyShareEntry_key_exchange_mid)
              == Some (ks <: GKSE.keyShareEntry_key_exchange));
    (* (b) keyShareEntry pair conv *)
    assert (GKSE.keyShareEntry_conv ((GNG.X25519, ks) <: GKSE.keyShareEntry_mid) == Some kse);
    (* (c) key_share extension vldata conv *)
    assert (GESHKS.extensionServerHello_extension_data_key_share_conv ((GNG.X25519, ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid)
              == Some ksesh);
    (* (d) extensionServerHello sum conv (key_share) *)
    assert (GESH.extensionServerHello_conv (GESH.Extension_data_key_share_mid ((GNG.X25519, ks) <: GESHKS.extensionServerHello_extension_data_key_share_mid))
              == Some ks_ext);
    (* (d') extensionServerHello sum conv (supported_versions) *)
    assert (GESH.extensionServerHello_conv (GESH.Extension_data_supported_versions_mid (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_mid))
              == Some sv_ext);
    (* (e) extensions list vldata conv *)
    assert (GSHBody.serverHelloBody_extensions_conv ([ks_ext; sv_ext] <: GSHBody.serverHelloBody_extensions_mid)
              == Some ([ks_ext; sv_ext] <: GSHBody.serverHelloBody_extensions));
    ()
#pop-options

(* ---- size lemma: the canonical ServerHello handshake message is 90 bytes ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_sh_size (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures GHS.handshake_bytesize (GHS.Body_server_hello (poc_canonical_sh rnd ks sid cs)) == 122)
  = let sh = poc_canonical_sh rnd ks sid cs in
    let sv_ext : GESH.extensionServerHello = GESH.Extension_data_supported_versions (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) } in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share (kse <: GESH.extensionServerHello_extension_data_key_share) in
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p2;
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
    GCS.cipherSuite_bytesize_eq cs;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    GSHBody.serverHelloBody_extensions_list_bytesize_cons sv_ext [];
    GSHBody.serverHelloBody_extensions_list_bytesize_cons ks_ext [sv_ext];
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

(* Intro the supported_versions element vmatch_conv (a protocolVersion LEAF;
   mirror of intro_vmatch_extSH_key_share but with eq_as_slprop in place of the
   keyShareEntry pair vmatch). *)
ghost
fn intro_vmatch_extSH_supported_versions
  (v0: GESH.extensionServerHello_extension_data_supported_versions_lowtype)
  (cm: GESH.extensionServerHello_extension_data_supported_versions_mid)
  (#h: GESH.extensionServerHello)
  requires LPS.eq_as_slprop GPV.protocolVersion v0 cm **
           pure (GESH.extensionServerHello_conv
                   (GESH.Extension_data_supported_versions_mid cm) == Some h)
  ensures PPB.vmatch_conv GESH.extensionServerHello_vmatch
            GESH.extensionServerHello_conv
            (GESH.Extension_data_supported_versions_low v0) h
{
  rewrite (LPS.eq_as_slprop GPV.protocolVersion v0 cm)
      as (GESH.extensionServerHello_extension_data_supported_versions_vmatch v0 cm);
  fold (GESH.extensionServerHello_vmatch
          (GESH.Extension_data_supported_versions_low v0)
          (GESH.Extension_data_supported_versions_mid cm));
  PPB.intro_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv
    (GESH.Extension_data_supported_versions_low v0)
    (GESH.Extension_data_supported_versions_mid cm) h;
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
let lemma_canonical_random (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures Sem.serverHello_random (poc_canonical_sh rnd ks sid cs) == Some (rnd <: Seq.lseq U8.t 32))
  = ()

let lemma_canonical_key_share (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures Sem.serverHello_key_share_x25519 (poc_canonical_sh rnd ks sid cs) == Some (ks <: Seq.seq U8.t))
  = ()

let lemma_canonical_cs (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures Sem.serverHello_cipher_suite (poc_canonical_sh rnd ks sid cs) == Some cs)
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

let lemma_sv_ext_conv ()
  : Lemma (ensures GESH.extensionServerHello_conv
                     (GESH.Extension_data_supported_versions_mid (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_mid))
                   == Some (GESH.Extension_data_supported_versions
                             (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions)))
  = ()

let lemma_sh_handshake_conv_fwd (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Lemma (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
          (ensures GHS.handshake_conv (GHS.Body_server_hello_mid (poc_sh_mid rnd ks sid cs))
                     == Some (GHS.Body_server_hello (poc_canonical_sh rnd ks sid cs)))
  = lemma_sh_conv_fwd rnd ks sid cs
#pop-options

(* ===================================================================== *)
(* Main: serialize a canonical ServerHello handshake message (90 bytes)  *)
(* ===================================================================== *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
fn serialize_server_hello_handshake_poc
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#sid: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old: erased B.bytes)
  requires L.is_valid_server_hello lsh (reveal sh) ** A.pts_to out (reveal old) **
           pure (B.length (reveal old) == SZ.v out_len /\ SZ.v out_len == 122 /\
                 Seq.length (reveal rnd) == 32 /\
                 (reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 Seq.length (reveal ks) == 32 /\
                 Seq.length (reveal sid) == 32 /\
                 reveal cs == GCS.TLS_CHACHA20_POLY1305_SHA256 /\
                 Ghost.reveal sh == poc_canonical_sh (reveal rnd) (reveal ks) (reveal sid) (reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (reveal sh) ** A.pts_to out out_bytes **
          pure (B.length out_bytes == 122 /\ SZ.v written == 122 /\
                Seq.equal out_bytes (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  unfold (L.is_valid_server_hello lsh (reveal sh));
  with random. assert (V.pts_to lsh.L.server_hello_random random);
  with key_share. assert (V.pts_to lsh.L.server_hello_key_share key_share);
  with sid_bytes. assert (V.pts_to lsh.L.server_hello_session_id sid_bytes);
  lemma_canonical_random (reveal rnd) (reveal ks) (reveal sid) (reveal cs);
  lemma_canonical_key_share (reveal rnd) (reveal ks) (reveal sid) (reveal cs);
  Seq.lemma_eq_elim random (reveal rnd);
  Seq.lemma_eq_elim key_share (reveal ks);
  Seq.lemma_eq_elim sid_bytes (reveal sid);
  (* copy random & key_share into fresh exact-32 vecs; is_valid stays intact *)
  V.pts_to_len lsh.L.server_hello_random;
  let rnd_vec = alloc_copy_vec_exact lsh.L.server_hello_random 32sz 32sz;
  with rnd_copy. assert (V.pts_to rnd_vec rnd_copy);
  Seq.lemma_eq_elim rnd_copy (reveal rnd);
  V.pts_to_len lsh.L.server_hello_key_share;
  let ks_vec = alloc_copy_vec_exact lsh.L.server_hello_key_share 32sz 32sz;
  with ks_copy. assert (V.pts_to ks_vec ks_copy);
  Seq.lemma_eq_elim ks_copy (reveal ks);
  V.pts_to_len lsh.L.server_hello_session_id;
  let sid_vec = alloc_copy_vec_exact lsh.L.server_hello_session_id 32sz 32sz;
  with sid_copy. assert (V.pts_to sid_vec sid_copy);
  Seq.lemma_eq_elim sid_copy (reveal sid);
  fold (L.is_valid_server_hello lsh (reveal sh));
  rewrite (V.pts_to rnd_vec rnd_copy) as (V.pts_to rnd_vec (reveal rnd));
  rewrite (V.pts_to ks_vec ks_copy) as (V.pts_to ks_vec (reveal ks));
  rewrite (V.pts_to sid_vec sid_copy) as (V.pts_to sid_vec (reveal sid));

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
  let ks_low : GESH.extensionServerHello_lowtype = GESH.Extension_data_key_share_low kse_low;
  rewrite (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             (GESH.Extension_data_key_share_low kse_low) (Ghost.reveal ks_ext))
      as (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             ks_low (Ghost.reveal ks_ext));

  (* ---- supported_versions extension element vmatch_conv (protocolVersion leaf) ---- *)
  let sv_ext : Ghost.erased GESH.extensionServerHello =
    Ghost.hide (GESH.Extension_data_supported_versions
      (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions));
  fold (LPS.eq_as_slprop GPV.protocolVersion GPV.TLS_1p3 GPV.TLS_1p3);
  lemma_sv_ext_conv ();
  intro_vmatch_extSH_supported_versions
    (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_lowtype)
    (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_mid)
    #(Ghost.reveal sv_ext);
  let sv_low : GESH.extensionServerHello_lowtype =
    GESH.Extension_data_supported_versions_low (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_lowtype);
  rewrite (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             (GESH.Extension_data_supported_versions_low (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions_lowtype)) (Ghost.reveal sv_ext))
      as (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             sv_low (Ghost.reveal sv_ext));

  (* ---- two-element extensions vclist [ks_ext; sv_ext] ---- *)
  let ext_vec = V.alloc ks_low 2sz;
  V.op_Array_Assignment ext_vec 1sz sv_low;
  with vc. assert (V.pts_to ext_vec vc);
  rewrite (V.pts_to ext_vec vc) as (V.pts_to ext_vec (Seq.upd (Seq.create 2 ks_low) 1 sv_low));
  SM.seq_list_match_nil_intro (Seq.empty #GESH.extensionServerHello_lowtype) ([] <: list GESH.extensionServerHello)
    (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv);
  SM.seq_list_match_cons_intro sv_low (Ghost.reveal sv_ext) (Seq.empty #GESH.extensionServerHello_lowtype) ([] <: list GESH.extensionServerHello)
    (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv);
  SM.seq_list_match_cons_intro ks_low (Ghost.reveal ks_ext) (Seq.cons sv_low (Seq.empty #GESH.extensionServerHello_lowtype)) ([Ghost.reveal sv_ext] <: list GESH.extensionServerHello)
    (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv);
  Seq.lemma_eq_elim (Seq.upd (Seq.create 2 ks_low) 1 sv_low) (Seq.cons ks_low (Seq.cons sv_low (Seq.empty #GESH.extensionServerHello_lowtype)));
  rewrite (SM.seq_list_match (Seq.cons ks_low (Seq.cons sv_low (Seq.empty #GESH.extensionServerHello_lowtype))) [Ghost.reveal ks_ext; Ghost.reveal sv_ext]
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv))
       as (SM.seq_list_match (Seq.upd (Seq.create 2 ks_low) 1 sv_low) [Ghost.reveal ks_ext; Ghost.reveal sv_ext]
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
  let exts_low = PPVCL.vmatch_vclist_some_intro 2sz ext_vec #(Seq.upd (Seq.create 2 ks_low) 1 sv_low) #[Ghost.reveal ks_ext; Ghost.reveal sv_ext] [Ghost.reveal ks_ext; Ghost.reveal sv_ext];

  (* ---- 32-byte session-id-echo lvec (RFC 8446 D.4 middlebox compat) ---- *)
  let sid_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = sid_vec; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to sid_vec (reveal sid)) as (V.pts_to sid_lvec.PPBY.lvec_vec (reveal sid));
  fold (LSeqB.vmatch_copy_seqbytes sid_lvec (reveal sid));
  rewrite (LSeqB.vmatch_copy_seqbytes sid_lvec (reveal sid))
       as (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch sid_lvec (reveal sid));

  (* ---- serverHelloBody vmatch ---- *)
  let shbody_low : GSHBody.serverHelloBody_lowtype =
    ((sid_lvec, GCS.TLS_CHACHA20_POLY1305_SHA256), (0uy, exts_low));
  let shm : Ghost.erased GSHBody.serverHelloBody_mid =
    Ghost.hide (((reveal sid <: Seq.seq U8.t), reveal cs), (0uy, ([Ghost.reveal ks_ext; Ghost.reveal sv_ext] <: list GESH.extensionServerHello)));
  rewrite (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch sid_lvec (reveal sid))
      as (GSHBody.serverHelloBody_legacy_session_id_echo_vmatch (fst (fst shbody_low)) (fst (fst (Ghost.reveal shm))));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
             exts_low [Ghost.reveal ks_ext; Ghost.reveal sv_ext])
      as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
             (snd (snd shbody_low)) (snd (snd (Ghost.reveal shm))));
  intro_serverHelloBody shbody_low #(Ghost.reveal shm);

  (* ---- ite payload (false branch) + random tag ---- *)
  let cm : Ghost.erased GSH.serverHello_mid =
    Ghost.hide (poc_sh_mid (reveal rnd) (reveal ks) (reveal sid) (reveal cs));
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
  lemma_sh_handshake_conv_fwd (reveal rnd) (reveal ks) (reveal sid) (reveal cs);
  lemma_sh_size (reveal rnd) (reveal ks) (reveal sid) (reveal cs);
  GHS.handshake_bytesize_eq (GHS.Body_server_hello (poc_canonical_sh (reveal rnd) (reveal ks) (reveal sid) (reveal cs)));
  S.to_array s;
  A.pts_to_len out;
  Rev.lemma_serialize_handshake_server_hello (Ghost.reveal sh);
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
noextract
let poc_cert_entry (chain: B.bytes)
  : Pure GCertE.certificateEntry
    (requires 1 <= Seq.length chain /\ Seq.length chain <= 32768)
    (ensures fun _ -> True)
  = { GCertE.cert_data = (chain <: GCertE.certificateEntry_cert_data);
      GCertE.extensions = ([] <: GCertE.certificateEntry_extensions) }

(* [poc_canonical_cert] is now declared transparently in the interface
   (TLS13.Impl.Serializer.Handshake.fsti) so downstream bridging lemmas can
   unfold it definitionally.  The canonical entry above / mid below stay
   private. *)
#pop-options

(* ---- canonical mid ---- *)
noextract
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

(* ---- bytesize bound (for Rev.lemma_serialize_handshake_certificate guard) ---- *)
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
  Rev.lemma_serialize_handshake_certificate (Ghost.reveal cert);
  GHS.free_handshake (GHS.Body_certificate_low xcert)
    #(Ghost.hide (GHS.Body_certificate_mid (Ghost.reveal cm)));
  sz
}
#pop-options

(* ===================================================================== *)
(* Shared canonical extension high values (each discharges its refinement)*)
(* ===================================================================== *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
(* [ch_sn_high], [ch_sg_high], [ch_sa_high], [ch_ks_high], [ch_sv_high] are now
   declared transparently in the interface (TLS13.Impl.Serializer.Handshake.fsti)
   so downstream bridging lemmas can unfold them; [ch_exts] below stays private. *)

noextract
let ch_exts (sni ks: B.bytes) (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Pure (list GECH.extensionClientHello)
    (requires 1 <= Seq.length sni /\ Seq.length sni <= 65461 /\ Seq.length ks == 32)
    (ensures fun _ -> True)
  = [ ch_sn_high sni; ch_sg_high; ch_sa_high sa; ch_ks_high ks; ch_sv_high ]
#pop-options

(* [poc_canonical_ch] is now declared transparently in the interface
   (TLS13.Impl.Serializer.Handshake.fsti) so downstream bridging lemmas can
   unfold it definitionally. *)

(* ---- Sem accessor lemmas (canonical pins random/server_name/key_share) ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_ch_random (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_random (poc_canonical_ch rnd sni ks sid cs sa) == (rnd <: Seq.lseq U8.t 32))
  = ()

let lemma_ch_server_name (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_server_name (poc_canonical_ch rnd sni ks sid cs sa) == Some (sni <: Seq.seq U8.t))
  = ()

let lemma_ch_key_share (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_key_share_x25519 (poc_canonical_ch rnd sni ks sid cs sa) == Some (ks <: Seq.seq U8.t))
  = ()

let lemma_ch_cipher_suites (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_cipher_suites (poc_canonical_ch rnd sni ks sid cs sa) == (cs <: list GCS.cipherSuite))
  = ()

let lemma_ch_sig_algs (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_sig_algs (poc_canonical_ch rnd sni ks sid cs sa) == Some (sa <: list GSS.signatureScheme))
  = ()
#pop-options

(* ---- canonical mid (same data, untyped tuple form) ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
noextract
let poc_ch_mid (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Pure GCH.clientHello_mid
    (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
              1 <= Seq.length sni /\ Seq.length sni <= 65461)
    (ensures fun _ -> True)
  = (((GPV.TLS_1p2, (rnd <: Seq.seq U8.t)),
      ((sid <: Seq.seq U8.t), (cs <: list GCS.cipherSuite))),
     ((Seq.create 1 0uy <: Seq.seq U8.t), (ch_exts sni ks sa <: list GECH.extensionClientHello)))
#pop-options

(* ===================================================================== *)
(* serialize_list length lemmas (each leaf serializes to exactly 2 bytes) *)
(* ===================================================================== *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec lemma_serialize_list_cs_len (cs: list GCS.cipherSuite)
  : Lemma (ensures Seq.length (LP.serialize (LPL.serialize_list _ GCS.cipherSuite_serializer) cs)
                   == 2 * LL.length cs)
          (decreases cs)
  = match cs with
    | [] -> LPL.serialize_list_nil _ GCS.cipherSuite_serializer
    | hd :: tl ->
      LPL.serialize_list_cons _ GCS.cipherSuite_serializer hd tl;
      lemma_serialize_list_cs_len tl

let rec lemma_serialize_list_sig_len (sa: list GSS.signatureScheme)
  : Lemma (ensures Seq.length (LP.serialize (LPL.serialize_list _ GSS.signatureScheme_serializer) sa)
                   == 2 * LL.length sa)
          (decreases sa)
  = match sa with
    | [] -> LPL.serialize_list_nil _ GSS.signatureScheme_serializer
    | hd :: tl ->
      LPL.serialize_list_cons _ GSS.signatureScheme_serializer hd tl;
      lemma_serialize_list_sig_len tl
#pop-options

(* ===================================================================== *)
(* Per-extension conv lemmas (inputs to the intro_vmatch_extCH helpers)   *)
(* ===================================================================== *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
let lemma_ch_sn_ext_conv (sni: B.bytes)
  : Lemma (requires 1 <= Seq.length sni /\ Seq.length sni <= 65461)
          (ensures GECH.extensionClientHello_conv
                     (GECH.Extension_data_server_name_mid
                       ([GSN.Name_host_name (sni <: GHN.hostName)] <: GSNL.serverNameList_mid))
                   == Some (ch_sn_high sni))
  = let hn : GHN.hostName = sni in
    GSNL.serverNameList_list_bytesize_nil;
    GSNL.serverNameList_list_bytesize_cons (GSN.Name_host_name hn) [];
    GSN.serverName_bytesize_eqn_host_name hn;
    GHN.hostName_bytesize_eqn hn;
    ()

let lemma_ch_sg_ext_conv ()
  : Lemma (ensures GECH.extensionClientHello_conv
                     (GECH.Extension_data_supported_groups_mid
                       ([GNG.X25519] <: GNGL.namedGroupList_mid))
                   == Some ch_sg_high)
  = LPL.serialize_list_nil _ GNG.namedGroup_serializer;
    LPL.serialize_list_singleton _ GNG.namedGroup_serializer GNG.X25519;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    ()

let lemma_ch_sa_ext_conv (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires LL.length sa <= 16)
          (ensures GECH.extensionClientHello_conv
                     (GECH.Extension_data_signature_algorithms_mid (sa <: GSSL.signatureSchemeList_mid))
                   == Some (ch_sa_high sa))
  = lemma_serialize_list_sig_len sa;
    ()

let lemma_ch_ks_ext_conv (ks: B.bytes)
  : Lemma (requires Seq.length ks == 32)
          (ensures GECH.extensionClientHello_conv
                     (GECH.Extension_data_key_share_mid
                       ([({ GKSE.group = GNG.X25519; GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) })]
                        <: GKSCH.keyShareClientHello_mid))
                   == Some (ch_ks_high ks))
  = let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GKSCH.keyShareClientHello_list_bytesize_nil;
    GKSCH.keyShareClientHello_list_bytesize_cons kse [];
    GKSE.keyShareEntry_bytesize_eqn kse;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    ()

let lemma_ch_sv_ext_conv ()
  : Lemma (ensures GECH.extensionClientHello_conv
                     (GECH.Extension_data_supported_versions_mid
                       ([GOV.Offered_TLS_1p3] <: GSVCH.supportedVersionsClientHello_mid))
                   == Some ch_sv_high)
  = LPL.serialize_list_nil _ GOV.offeredVersion_serializer;
    LPL.serialize_list_singleton _ GOV.offeredVersion_serializer GOV.Offered_TLS_1p3;
    GOV.offeredVersion_bytesize_eq GOV.Offered_TLS_1p3;
    ()
#pop-options

(* ---- forward conv: mid converts to the canonical record ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 300"
let lemma_ch_conv_fwd (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures GCH.clientHello_conv (poc_ch_mid rnd sni ks sid cs sa) == Some (poc_canonical_ch rnd sni ks sid cs sa))
  = let sn_ext = ch_sn_high sni in
    let sg_ext = ch_sg_high in
    let sa_ext = ch_sa_high sa in
    let ks_ext = ch_ks_high ks in
    let sv_ext = ch_sv_high in
    GCH.clientHello_extensions_list_bytesize_nil;
    GCH.clientHello_extensions_list_bytesize_cons sv_ext [];
    GCH.clientHello_extensions_list_bytesize_cons ks_ext [sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sa_ext [ks_ext; sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sg_ext [sa_ext; ks_ext; sv_ext];
    GCH.clientHello_extensions_list_bytesize_cons sn_ext [sg_ext; sa_ext; ks_ext; sv_ext];
    lemma_serialize_list_cs_len cs;
    lemma_serialize_list_sig_len sa;
    ()
#pop-options

(* ---- handshake-level conv (wraps the body) ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_ch_handshake_conv_fwd (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures GHS.handshake_conv (GHS.Body_client_hello_mid (poc_ch_mid rnd sni ks sid cs sa))
                   == Some (GHS.Body_client_hello ((poc_canonical_ch rnd sni ks sid cs sa) <: GHS.handshake_body_client_hello)))
  = lemma_ch_conv_fwd rnd sni ks sid cs sa
#pop-options
(* ===================================================================== *)
(* Intro ghost helpers for the 5 ClientHello extensions (copied/adapted   *)
(* from Impl.Parser; sg built by analogy to sa).                          *)
(* ===================================================================== *)

(* Re-pack a hostName lvec into a server_name element (port of
   Impl.Parser.intro_vmatch_serverName_host). *)
ghost
fn intro_vmatch_serverName_host
  (v0: GHN.hostName_lowtype)
  (cm: GHN.hostName_mid)
  (#h: GSN.serverName)
  requires LSeqB.vmatch_copy_seqbytes v0 cm **
           pure (GSN.serverName_conv (GSN.Name_host_name_mid cm) == Some h)
  ensures PPB.vmatch_conv GSN.serverName_vmatch GSN.serverName_conv
            (GSN.Name_host_name_low v0) h
{
  rewrite (LSeqB.vmatch_copy_seqbytes v0 cm)
      as (GHN.hostName_vmatch v0 cm);
  fold (GSN.serverName_vmatch
          (GSN.Name_host_name_low v0)
          (GSN.Name_host_name_mid cm));
  PPB.intro_vmatch_conv GSN.serverName_vmatch GSN.serverName_conv
    (GSN.Name_host_name_low v0) (GSN.Name_host_name_mid cm) h;
}

ghost
fn intro_vmatch_extCH_sn
  (v0: GSNL.serverNameList_lowtype)
  (cm: GSNL.serverNameList_mid)
  (#h: GECH.extensionClientHello)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GSN.serverName_vmatch GSN.serverName_conv) v0 cm **
           pure (GECH.extensionClientHello_conv
                   (GECH.Extension_data_server_name_mid cm) == Some h)
  ensures PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
            (GECH.Extension_data_server_name_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GSN.serverName_vmatch GSN.serverName_conv) v0 cm)
      as (GECH.extensionClientHello_extension_data_server_name_vmatch v0 cm);
  fold (GECH.extensionClientHello_vmatch
          (GECH.Extension_data_server_name_low v0)
          (GECH.Extension_data_server_name_mid cm));
  PPB.intro_vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
    (GECH.Extension_data_server_name_low v0)
    (GECH.Extension_data_server_name_mid cm) h;
}

ghost
fn intro_vmatch_extCH_sg
  (v0: GNGL.namedGroupList_lowtype)
  (cm: GNGL.namedGroupList_mid)
  (#h: GECH.extensionClientHello)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GNG.namedGroup_vmatch GNG.namedGroup_conv) v0 cm **
           pure (GECH.extensionClientHello_conv
                   (GECH.Extension_data_supported_groups_mid cm) == Some h)
  ensures PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
            (GECH.Extension_data_supported_groups_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GNG.namedGroup_vmatch GNG.namedGroup_conv) v0 cm)
      as (GECH.extensionClientHello_extension_data_supported_groups_vmatch v0 cm);
  fold (GECH.extensionClientHello_vmatch
          (GECH.Extension_data_supported_groups_low v0)
          (GECH.Extension_data_supported_groups_mid cm));
  PPB.intro_vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
    (GECH.Extension_data_supported_groups_low v0)
    (GECH.Extension_data_supported_groups_mid cm) h;
}

ghost
fn intro_vmatch_extCH_sa
  (v0: GSSL.signatureSchemeList_lowtype)
  (cm: GSSL.signatureSchemeList_mid)
  (#h: GECH.extensionClientHello)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv) v0 cm **
           pure (GECH.extensionClientHello_conv
                   (GECH.Extension_data_signature_algorithms_mid cm) == Some h)
  ensures PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
            (GECH.Extension_data_signature_algorithms_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv) v0 cm)
      as (GECH.extensionClientHello_extension_data_signature_algorithms_vmatch v0 cm);
  fold (GECH.extensionClientHello_vmatch
          (GECH.Extension_data_signature_algorithms_low v0)
          (GECH.Extension_data_signature_algorithms_mid cm));
  PPB.intro_vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
    (GECH.Extension_data_signature_algorithms_low v0)
    (GECH.Extension_data_signature_algorithms_mid cm) h;
}

ghost
fn intro_vmatch_extCH_ks
  (v0: GKSCH.keyShareClientHello_lowtype)
  (cm: GKSCH.keyShareClientHello_mid)
  (#h: GECH.extensionClientHello)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GKSE.keyShareEntry_vmatch GKSE.keyShareEntry_conv) v0 cm **
           pure (GECH.extensionClientHello_conv
                   (GECH.Extension_data_key_share_mid cm) == Some h)
  ensures PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
            (GECH.Extension_data_key_share_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GKSE.keyShareEntry_vmatch GKSE.keyShareEntry_conv) v0 cm)
      as (GECH.extensionClientHello_extension_data_key_share_vmatch v0 cm);
  fold (GECH.extensionClientHello_vmatch
          (GECH.Extension_data_key_share_low v0)
          (GECH.Extension_data_key_share_mid cm));
  PPB.intro_vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
    (GECH.Extension_data_key_share_low v0)
    (GECH.Extension_data_key_share_mid cm) h;
}

ghost
fn intro_vmatch_extCH_sv
  (v0: GSVCH.supportedVersionsClientHello_lowtype)
  (cm: GSVCH.supportedVersionsClientHello_mid)
  (#h: GECH.extensionClientHello)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GOV.offeredVersion_vmatch GOV.offeredVersion_conv) v0 cm **
           pure (GECH.extensionClientHello_conv
                   (GECH.Extension_data_supported_versions_mid cm) == Some h)
  ensures PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
            (GECH.Extension_data_supported_versions_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GOV.offeredVersion_vmatch GOV.offeredVersion_conv) v0 cm)
      as (GECH.extensionClientHello_extension_data_supported_versions_vmatch v0 cm);
  fold (GECH.extensionClientHello_vmatch
          (GECH.Extension_data_supported_versions_low v0)
          (GECH.Extension_data_supported_versions_mid cm));
  PPB.intro_vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
    (GECH.Extension_data_supported_versions_low v0)
    (GECH.Extension_data_supported_versions_mid cm) h;
}

(* Fold the nested clientHello_lowtype vmatch_pair chain directly into the
   handshake sum vmatch (adapted from Impl.Parser.intro_vmatch_client_hello,
   WITHOUT the final read-side vmatch_conv wrapper). *)
ghost
fn intro_handshake_client_hello_vmatch
  (xch: GCH.clientHello_lowtype)
  (cm: GCH.clientHello_mid)
  requires
    LSeqB.vmatch_copy_seqbytes (snd (fst (fst xch))) (snd (fst (fst cm))) **
    LSeqB.vmatch_copy_seqbytes (fst (snd (fst xch))) (fst (snd (fst cm))) **
    PPVCL.vmatch_vclist
      (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv)
      (snd (snd (fst xch))) (snd (snd (fst cm))) **
    LSeqB.vmatch_copy_seqbytes (fst (snd xch)) (fst (snd cm)) **
    PPVCL.vmatch_vclist
      (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
      (snd (snd xch)) (snd (snd cm)) **
    pure (fst (fst (fst xch)) == fst (fst (fst cm)))
  ensures GHS.handshake_vmatch (GHS.Body_client_hello_low xch) (GHS.Body_client_hello_mid cm)
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
             (snd (snd xch)) (snd (snd cm)))
      as (GCH.clientHello_extensions_vmatch (snd (snd xch)) (snd (snd cm)));
  rewrite (LSeqB.vmatch_copy_seqbytes (fst (snd xch)) (fst (snd cm)))
      as (GCH.clientHello_legacy_compression_methods_vmatch (fst (snd xch)) (fst (snd cm)));
  fold (LPC.vmatch_pair GCH.clientHello_legacy_compression_methods_vmatch
                        GCH.clientHello_extensions_vmatch (snd xch) (snd cm));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv)
             (snd (snd (fst xch))) (snd (snd (fst cm))))
      as (GCH.clientHello_cipher_suites_vmatch (snd (snd (fst xch))) (snd (snd (fst cm))));
  rewrite (LSeqB.vmatch_copy_seqbytes (fst (snd (fst xch))) (fst (snd (fst cm))))
      as (GCH.clientHello_legacy_session_id_vmatch (fst (snd (fst xch))) (fst (snd (fst cm))));
  fold (LPC.vmatch_pair GCH.clientHello_legacy_session_id_vmatch
                        GCH.clientHello_cipher_suites_vmatch
                        (snd (fst xch)) (snd (fst cm)));
  rewrite (LSeqB.vmatch_copy_seqbytes (snd (fst (fst xch))) (snd (fst (fst cm))))
      as (GRND.random_vmatch (snd (fst (fst xch))) (snd (fst (fst cm))));
  fold (LPS.eq_as_slprop GPV.protocolVersion (fst (fst (fst xch))) (fst (fst (fst cm))));
  rewrite (LPS.eq_as_slprop GPV.protocolVersion (fst (fst (fst xch))) (fst (fst (fst cm))))
      as (GPV.protocolVersion_vmatch (fst (fst (fst xch))) (fst (fst (fst cm))));
  fold (LPC.vmatch_pair GPV.protocolVersion_vmatch GRND.random_vmatch
          (fst (fst xch)) (fst (fst cm)));
  fold (LPC.vmatch_pair
          (LPC.vmatch_pair GPV.protocolVersion_vmatch GRND.random_vmatch)
          (LPC.vmatch_pair GCH.clientHello_legacy_session_id_vmatch
                           GCH.clientHello_cipher_suites_vmatch)
          (fst xch) (fst cm));
  fold (LPC.vmatch_pair
          (LPC.vmatch_pair
            (LPC.vmatch_pair GPV.protocolVersion_vmatch GRND.random_vmatch)
            (LPC.vmatch_pair GCH.clientHello_legacy_session_id_vmatch
                             GCH.clientHello_cipher_suites_vmatch))
          (LPC.vmatch_pair GCH.clientHello_legacy_compression_methods_vmatch
                           GCH.clientHello_extensions_vmatch)
          xch cm);
  rewrite (LPC.vmatch_pair
             (LPC.vmatch_pair
               (LPC.vmatch_pair GPV.protocolVersion_vmatch GRND.random_vmatch)
               (LPC.vmatch_pair GCH.clientHello_legacy_session_id_vmatch
                                GCH.clientHello_cipher_suites_vmatch))
             (LPC.vmatch_pair GCH.clientHello_legacy_compression_methods_vmatch
                              GCH.clientHello_extensions_vmatch)
             xch cm)
      as (GHCH.handshake_body_client_hello_vmatch xch cm);
  fold (GHS.handshake_vmatch (GHS.Body_client_hello_low xch) (GHS.Body_client_hello_mid cm));
}

(* Build a singleton vclist from one element vmatch (allocates the 1-vec,
   which the vclist then owns). *)
fn mk_singleton_vclist
  (#el #eh: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (e_low: el)
  (#e_high: Ghost.erased eh)
  requires elem_vmatch e_low (reveal e_high)
  returns r: PPVCL.vclist_lowtype el
  ensures PPVCL.vmatch_vclist elem_vmatch r [reveal e_high]
{
  let vec = V.alloc e_low 1sz;
  SM.seq_list_match_nil_intro (Seq.empty #el) ([] <: list eh) elem_vmatch;
  SM.seq_list_match_cons_intro e_low (reveal e_high) (Seq.empty #el) ([] <: list eh) elem_vmatch;
  Seq.lemma_eq_elim (Seq.create 1 e_low) (Seq.cons e_low (Seq.empty #el));
  rewrite (SM.seq_list_match (Seq.cons e_low (Seq.empty #el)) [reveal e_high] elem_vmatch)
       as (SM.seq_list_match (Seq.create 1 e_low) [reveal e_high] elem_vmatch);
  let r = PPVCL.vmatch_vclist_some_intro 1sz vec #(Seq.create 1 e_low) #[reveal e_high] [reveal e_high];
  r
}

(* ===================================================================== *)
(* U16 -> leaf coercions and matching lemmas (for the variable vclists)   *)
(* ===================================================================== *)

let u16_to_cipher_suite (w: U16.t) : GCS.cipherSuite =
  if w = 4867us then GCS.TLS_CHACHA20_POLY1305_SHA256
  else GCS.Unknown_cipherSuite w

let lemma_u16_to_cipher_suite_matches (w: U16.t) (c: GCS.cipherSuite)
  : Lemma (requires L.cipher_suite_matches w c)
          (ensures u16_to_cipher_suite w == c)
  = match c with
    | GCS.TLS_CHACHA20_POLY1305_SHA256 ->
      assert_norm (U16.v 4867us == 0x1303);
      U16.v_inj w 4867us
    | GCS.Unknown_cipherSuite n ->
      assert_norm (U16.v 4867us == 0x1303);
      U16.v_inj w n

(* [u16_to_sig_scheme] + [lemma_u16_to_sig_scheme] are defined above (reused by
   the CertificateVerify serializer); reuse them here for signature_schemes. *)

let rec lemma_cipher_suites_match_coerce
  (wire: Seq.seq U16.t) (n: nat) (cs: list GCS.cipherSuite)
  : Lemma (requires L.cipher_suites_match wire n cs)
          (ensures LL.length cs == n /\ n <= Seq.length wire /\
                   (forall (k:nat). k < n ==>
                     u16_to_cipher_suite (Seq.index wire k) == LL.index cs k))
          (decreases n)
  = if n = 0 then ()
    else begin
      let a :: rest = cs in
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      lemma_u16_to_cipher_suite_matches (Seq.index wire 0) a;
      lemma_cipher_suites_match_coerce wire' (n - 1) rest;
      introduce forall (k:nat). k < n ==>
                  u16_to_cipher_suite (Seq.index wire k) == LL.index cs k
      with begin
        introduce _ ==> _
        with _. begin
          if k = 0 then ()
          else begin
            assert (Seq.index wire k == Seq.index wire' (k - 1));
            assert (u16_to_cipher_suite (Seq.index wire' (k-1)) == LL.index rest (k-1))
          end
        end
      end
    end

let rec lemma_sig_schemes_match_coerce
  (wire: Seq.seq U16.t) (n: nat) (ss: list GSS.signatureScheme)
  : Lemma (requires L.signature_schemes_match wire n ss)
          (ensures LL.length ss == n /\ n <= Seq.length wire /\
                   (forall (k:nat). k < n ==>
                     u16_to_sig_scheme (Seq.index wire k) == LL.index ss k))
          (decreases n)
  = if n = 0 then ()
    else begin
      let a :: rest = ss in
      let wire' = Seq.slice wire 1 (Seq.length wire) in
      lemma_u16_to_sig_scheme (Seq.index wire 0) a;
      lemma_sig_schemes_match_coerce wire' (n - 1) rest;
      introduce forall (k:nat). k < n ==>
                  u16_to_sig_scheme (Seq.index wire k) == LL.index ss k
      with begin
        introduce _ ==> _
        with _. begin
          if k = 0 then ()
          else begin
            assert (Seq.index wire k == Seq.index wire' (k - 1));
            assert (u16_to_sig_scheme (Seq.index wire' (k-1)) == LL.index rest (k-1))
          end
        end
      end
    end

(* per-element vmatch_conv builders (leaf eq_as_slprop) *)
ghost
fn mk1_cipher_suite (e: GCS.cipherSuite)
  requires emp
  ensures PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv e e
{
  fold (LPS.eq_as_slprop GCS.cipherSuite e e);
  rewrite (LPS.eq_as_slprop GCS.cipherSuite e e) as (GCS.cipherSuite_vmatch e e);
  PPB.intro_vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv e e e;
}

ghost
fn mk1_sig_scheme (e: GSS.signatureScheme)
  requires emp
  ensures PPB.vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv e e
{
  fold (LPS.eq_as_slprop GSS.signatureScheme e e);
  rewrite (LPS.eq_as_slprop GSS.signatureScheme e e) as (GSS.signatureScheme_vmatch e e);
  PPB.intro_vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv e e e;
}

(* Generic loop builder: vclist of leaves from a U16 source vec. The source
   vec is preserved (read-only), so the L mirror stays owned by the caller. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
inline_for_extraction
fn mk_vclist_from_u16_leaf_array
  (#eh: Type0)
  (#elem_vmatch: eh -> eh -> slprop)
  (#elem_conv: eh -> GTot (option eh))
  (coerce: (w: U16.t -> eh))
  (mk1: (e: eh) -> stt_ghost unit emp_inames emp (fun _ -> PPB.vmatch_conv elem_vmatch elem_conv e e))
  (src: V.vec U16.t)
  (n: SZ.t)
  (#p: perm)
  (#wire: Ghost.erased (Seq.seq U16.t))
  (#l: Ghost.erased (list eh))
  requires
    V.pts_to src #p wire **
    pure (SZ.v n <= Seq.length wire /\
          SZ.v n == LL.length (Ghost.reveal l) /\ SZ.v n > 0 /\
          (forall (k:nat). k < SZ.v n ==>
            coerce (Seq.index wire k) == LL.index (Ghost.reveal l) k))
  returns r: PPVCL.vclist_lowtype eh
  ensures
    V.pts_to src #p wire **
    PPVCL.vmatch_vclist (PPB.vmatch_conv elem_vmatch elem_conv) r (Ghost.reveal l)
{
  let sl : Ghost.erased (Seq.seq eh) = Ghost.hide (Seq.seq_of_list (Ghost.reveal l));
  let w0 = V.op_Array_Access src 0sz;
  let e0 = coerce w0;
  let vec = V.alloc e0 n;
  V.pts_to_len vec;
  Seq.lemma_seq_of_list_index (Ghost.reveal l) 0;
  mk1 e0;
  rewrite (PPB.vmatch_conv elem_vmatch elem_conv e0 e0)
    as (PPB.vmatch_conv elem_vmatch elem_conv (Seq.index (Seq.create (SZ.v n) e0) 0) (Seq.index (Ghost.reveal sl) 0));
  SM.seq_seq_match_singleton_intro (PPB.vmatch_conv elem_vmatch elem_conv)
    (Seq.create (SZ.v n) e0) (Ghost.reveal sl) 0
    (Seq.index (Seq.create (SZ.v n) e0) 0) (Seq.index (Ghost.reveal sl) 0);
  let mut pi = 1sz;
  while (let i = !pi; SZ.lt i n)
  invariant exists* i (s1: Seq.seq eh).
    R.pts_to pi i **
    V.pts_to src #p wire **
    V.pts_to vec s1 **
    SM.seq_seq_match (PPB.vmatch_conv elem_vmatch elem_conv) s1 (Ghost.reveal sl) 0 (SZ.v i) **
    pure (1 <= SZ.v i /\ SZ.v i <= SZ.v n /\ V.is_full_vec vec /\ Seq.length s1 == SZ.v n)
  decreases (SZ.v n - SZ.v (!pi))
  {
    let i = !pi;
    with s1. assert (V.pts_to vec s1);
    let wi = V.op_Array_Access src i;
    let ei = coerce wi;
    V.op_Array_Assignment vec i ei;
    with s1'. assert (V.pts_to vec s1');
    SM.seq_seq_match_rewrite_seq (PPB.vmatch_conv elem_vmatch elem_conv) s1 s1' (Ghost.reveal sl) (Ghost.reveal sl) 0 (SZ.v i);
    Seq.lemma_seq_of_list_index (Ghost.reveal l) (SZ.v i);
    mk1 ei;
    rewrite (PPB.vmatch_conv elem_vmatch elem_conv ei ei)
      as (PPB.vmatch_conv elem_vmatch elem_conv (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i)));
    SM.seq_seq_match_enqueue_right (PPB.vmatch_conv elem_vmatch elem_conv) s1' (Ghost.reveal sl) 0 (SZ.v i)
      (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i));
    pi := SZ.add i 1sz;
  };
  with s_final. assert (V.pts_to vec s_final);
  SM.seq_seq_match_seq_list_match (PPB.vmatch_conv elem_vmatch elem_conv) s_final (Ghost.reveal l);
  let r = PPVCL.vmatch_vclist_some_intro n vec #s_final #(Ghost.reveal l) (Ghost.reveal l);
  r
}
#pop-options

(* element-level conv facts for the sn (host name) and ks (entry) leaves *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_ch_sn_host_conv (sni: B.bytes)
  : Lemma (requires 1 <= Seq.length sni /\ Seq.length sni <= 65461)
          (ensures GSN.serverName_conv (GSN.Name_host_name_mid (sni <: GHN.hostName_mid))
                   == Some (GSN.Name_host_name (sni <: GHN.hostName)))
  = ()

let lemma_ch_kse_conv (ks: B.bytes)
  : Lemma (requires Seq.length ks == 32)
          (ensures GKSE.keyShareEntry_conv
                     ((GNG.X25519, (ks <: GKSE.keyShareEntry_key_exchange_mid)) <: GKSE.keyShareEntry_mid)
                   == Some ({ GKSE.group = GNG.X25519;
                              GKSE.key_exchange = (ks <: GKSE.keyShareEntry_key_exchange) }))
  = GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn (ks <: GKSE.keyShareEntry_key_exchange);
    ()
#pop-options

(* ===================================================================== *)
(* Main: serialize a canonical ClientHello handshake message             *)
(* (5 extensions: server_name, supported_groups, signature_algorithms,    *)
(*  key_share, supported_versions).                                       *)
(* ===================================================================== *)
#push-options "--fuel 6 --ifuel 6 --z3rlimit 120"
fn serialize_client_hello_handshake_poc
  (#ch: erased GCH.clientHello)
  (#rnd #sni #ks #sid: erased B.bytes)
  (#cs: erased GCH.clientHello_cipher_suites)
  (#sa: erased GECH.extensionClientHello_extension_data_signature_algorithms)
  (l: L.client_hello)
  (out: A.array U8.t)
  (out_len: SZ.t)
  (#old: erased B.bytes)
  requires L.is_valid_client_hello l (reveal ch) ** A.pts_to out (reveal old) **
           pure (B.length (reveal old) == SZ.v out_len /\
                 SZ.v out_len == B.length (WS.serialize_handshake (M.ClientHello (reveal ch))) /\
                 Seq.length (reveal rnd) == 32 /\ Seq.length (reveal ks) == 32 /\
                 Seq.length (reveal sid) == 32 /\
                 1 <= Seq.length (reveal sni) /\ Seq.length (reveal sni) <= 255 /\
                 LL.length (reveal cs) <= 16 /\ LL.length (reveal sa) <= 16 /\
                 reveal ch == poc_canonical_ch (reveal rnd) (reveal sni) (reveal ks) (reveal sid) cs sa)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* ob.
          L.is_valid_client_hello l (reveal ch) ** A.pts_to out ob **
          pure (B.length ob == SZ.v out_len /\ SZ.v written == SZ.v out_len /\
                Seq.equal ob (WS.serialize_handshake (M.ClientHello (reveal ch))))
{
  unfold (L.is_valid_client_hello l (reveal ch));
  with random. assert (V.pts_to l.L.client_hello_random random);
  with sid_bytes. assert (V.pts_to l.L.client_hello_session_id sid_bytes);
  with server_name. assert (V.pts_to l.L.client_hello_server_name server_name);
  with key_share. assert (V.pts_to l.L.client_hello_key_share key_share);
  with cs_wire. assert (V.pts_to l.L.client_hello_cipher_suites cs_wire);
  with ss_wire. assert (V.pts_to l.L.client_hello_signature_schemes ss_wire);
  lemma_ch_random (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  lemma_ch_server_name (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  lemma_ch_key_share (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  Seq.lemma_eq_elim random (reveal rnd);
  Seq.lemma_eq_elim key_share (reveal ks);
  Seq.lemma_eq_elim sid_bytes (reveal sid);
  let sn_len = l.L.client_hello_server_name_len;

  (* ---- build the VARIABLE cipher_suites + signature_schemes vclists from
          the L-mirror vecs (each helper call preserves its source vec) ---- *)
  let cs_len = l.L.client_hello_cipher_suites_len;
  let ss_len = l.L.client_hello_signature_schemes_len;
  lemma_ch_cipher_suites (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  lemma_ch_sig_algs (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  let cs_lo : Ghost.erased (list GCS.cipherSuite) = Ghost.hide (reveal cs <: list GCS.cipherSuite);
  let sa_lo : Ghost.erased (list GSS.signatureScheme) = Ghost.hide (reveal sa <: list GSS.signatureScheme);
  lemma_cipher_suites_match_coerce cs_wire (SZ.v cs_len) (reveal cs);
  let cs_vclist = mk_vclist_from_u16_leaf_array
    #GCS.cipherSuite #GCS.cipherSuite_vmatch #GCS.cipherSuite_conv
    u16_to_cipher_suite mk1_cipher_suite
    l.L.client_hello_cipher_suites cs_len #_ #cs_wire #cs_lo;
  rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv) cs_vclist (reveal cs_lo))
      as (PPVCL.vmatch_vclist (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv) cs_vclist (reveal cs <: list GCS.cipherSuite));
  lemma_sig_schemes_match_coerce ss_wire (SZ.v ss_len) (reveal sa);
  let sa_vclist = mk_vclist_from_u16_leaf_array
    #GSS.signatureScheme #GSS.signatureScheme_vmatch #GSS.signatureScheme_conv
    u16_to_sig_scheme mk1_sig_scheme
    l.L.client_hello_signature_schemes ss_len #_ #ss_wire #sa_lo;
  rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv) sa_vclist (reveal sa_lo))
      as (PPVCL.vmatch_vclist (PPB.vmatch_conv GSS.signatureScheme_vmatch GSS.signatureScheme_conv) sa_vclist (reveal sa <: GSSL.signatureSchemeList_mid));

  (* ---- copy random & key_share into fresh exact-32 vecs ---- *)
  V.pts_to_len l.L.client_hello_random;
  let rnd_vec = alloc_copy_vec_exact l.L.client_hello_random 32sz 32sz;
  with rnd_copy. assert (V.pts_to rnd_vec rnd_copy);
  Seq.lemma_eq_elim rnd_copy (reveal rnd);
  V.pts_to_len l.L.client_hello_key_share;
  let ks_vec = alloc_copy_vec_exact l.L.client_hello_key_share 32sz 32sz;
  with ks_copy. assert (V.pts_to ks_vec ks_copy);
  Seq.lemma_eq_elim ks_copy (reveal ks);
  V.pts_to_len l.L.client_hello_session_id;
  let sid_vec = alloc_copy_vec_exact l.L.client_hello_session_id 32sz 32sz;
  with sid_copy. assert (V.pts_to sid_vec sid_copy);
  Seq.lemma_eq_elim sid_copy (reveal sid);

  (* ---- copy SNI sub-slice server_name[0..sn_len) into a fresh exact vec ---- *)
  V.pts_to_len l.L.client_hello_server_name;
  let sni_vec = alloc_copy_subslice l.L.client_hello_server_name 0sz sn_len 255sz;
  with sni_copy. assert (V.pts_to sni_vec sni_copy);
  Seq.lemma_eq_elim sni_copy (reveal sni);
  assert (pure (SZ.v sn_len == Seq.length (reveal sni)));
  fold (L.is_valid_client_hello l (reveal ch));
  rewrite (V.pts_to rnd_vec rnd_copy) as (V.pts_to rnd_vec (reveal rnd));
  rewrite (V.pts_to ks_vec ks_copy) as (V.pts_to ks_vec (reveal ks));
  rewrite (V.pts_to sid_vec sid_copy) as (V.pts_to sid_vec (reveal sid));
  rewrite (V.pts_to sni_vec sni_copy) as (V.pts_to sni_vec (reveal sni));

  (* ---- random lvec ---- *)
  let rnd_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = rnd_vec; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to rnd_vec (reveal rnd)) as (V.pts_to rnd_lvec.PPBY.lvec_vec (reveal rnd));
  fold (LSeqB.vmatch_copy_seqbytes rnd_lvec (reveal rnd));

  (* ---- 32-byte legacy_session_id lvec (RFC 8446 D.4 middlebox compat) ---- *)
  let sid_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = sid_vec; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to sid_vec (reveal sid)) as (V.pts_to sid_lvec.PPBY.lvec_vec (reveal sid));
  fold (LSeqB.vmatch_copy_seqbytes sid_lvec (reveal sid));

  (* ---- 1-byte null legacy_compression_methods lvec ---- *)
  let comp_vec = V.alloc 0uy 1sz;
  let comp_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = comp_vec; PPBY.lvec_len = 1sz };
  rewrite (V.pts_to comp_vec (Seq.create 1 0uy)) as (V.pts_to comp_lvec.PPBY.lvec_vec (Seq.create 1 0uy));
  fold (LSeqB.vmatch_copy_seqbytes comp_lvec (Seq.create 1 0uy));

  (* ---- cipher_suites vclist already built above (cs_vclist : variable) ---- *)

  (* ---- server_name extension element ---- *)
  let sni_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = sni_vec; PPBY.lvec_len = sn_len };
  rewrite (V.pts_to sni_vec (reveal sni)) as (V.pts_to sni_lvec.PPBY.lvec_vec (reveal sni));
  fold (LSeqB.vmatch_copy_seqbytes sni_lvec (reveal sni));
  lemma_ch_sn_host_conv (reveal sni);
  intro_vmatch_serverName_host sni_lvec (reveal sni) #(GSN.Name_host_name (reveal sni <: GHN.hostName));
  let sn_vclist = mk_singleton_vclist
    #_ #_ #(PPB.vmatch_conv GSN.serverName_vmatch GSN.serverName_conv)
    (GSN.Name_host_name_low sni_lvec) #(GSN.Name_host_name (reveal sni <: GHN.hostName));
  lemma_ch_sn_ext_conv (reveal sni);
  intro_vmatch_extCH_sn sn_vclist
    ([GSN.Name_host_name (reveal sni <: GHN.hostName)] <: GSNL.serverNameList_mid)
    #(ch_sn_high (reveal sni));
  let sn_elem_low : GECH.extensionClientHello_low = GECH.Extension_data_server_name_low sn_vclist;
  rewrite (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             (GECH.Extension_data_server_name_low sn_vclist) (ch_sn_high (reveal sni)))
      as (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             sn_elem_low (ch_sn_high (reveal sni)));

  (* ---- supported_groups extension element ---- *)
  fold (LPS.eq_as_slprop GNG.namedGroup GNG.X25519 GNG.X25519);
  rewrite (LPS.eq_as_slprop GNG.namedGroup GNG.X25519 GNG.X25519)
      as (GNG.namedGroup_vmatch GNG.X25519 GNG.X25519);
  PPB.intro_vmatch_conv GNG.namedGroup_vmatch GNG.namedGroup_conv GNG.X25519 GNG.X25519 GNG.X25519;
  let sg_vclist = mk_singleton_vclist
    #_ #_ #(PPB.vmatch_conv GNG.namedGroup_vmatch GNG.namedGroup_conv) GNG.X25519 #GNG.X25519;
  lemma_ch_sg_ext_conv ();
  intro_vmatch_extCH_sg sg_vclist ([GNG.X25519] <: GNGL.namedGroupList_mid) #ch_sg_high;
  let sg_elem_low : GECH.extensionClientHello_low = GECH.Extension_data_supported_groups_low sg_vclist;
  rewrite (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             (GECH.Extension_data_supported_groups_low sg_vclist) ch_sg_high)
      as (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             sg_elem_low ch_sg_high);

  (* ---- signature_algorithms extension element (sa_vclist : variable) ---- *)
  lemma_ch_sa_ext_conv (reveal sa);
  intro_vmatch_extCH_sa sa_vclist (reveal sa <: GSSL.signatureSchemeList_mid) #(ch_sa_high (reveal sa));
  let sa_elem_low : GECH.extensionClientHello_low = GECH.Extension_data_signature_algorithms_low sa_vclist;
  rewrite (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             (GECH.Extension_data_signature_algorithms_low sa_vclist) (ch_sa_high (reveal sa)))
      as (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             sa_elem_low (ch_sa_high (reveal sa)));

  (* ---- key_share extension element ---- *)
  let ks_lvec : PPBY.lvec U8.t = { PPBY.lvec_vec = ks_vec; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to ks_vec (reveal ks)) as (V.pts_to ks_lvec.PPBY.lvec_vec (reveal ks));
  let kse_low : GKSE.keyShareEntry_lowtype = (GNG.X25519, ks_lvec);
  rewrite (V.pts_to ks_lvec.PPBY.lvec_vec (reveal ks))
      as (V.pts_to (snd kse_low).PPBY.lvec_vec (reveal ks));
  repack_kse kse_low #(Ghost.hide ((GNG.X25519, reveal ks) <: GKSE.keyShareEntry_mid));
  lemma_ch_kse_conv (reveal ks);
  PPB.intro_vmatch_conv GKSE.keyShareEntry_vmatch GKSE.keyShareEntry_conv
    kse_low ((GNG.X25519, reveal ks) <: GKSE.keyShareEntry_mid)
    ({ GKSE.group = GNG.X25519; GKSE.key_exchange = (reveal ks <: GKSE.keyShareEntry_key_exchange) });
  let ks_vclist = mk_singleton_vclist
    #_ #_ #(PPB.vmatch_conv GKSE.keyShareEntry_vmatch GKSE.keyShareEntry_conv)
    kse_low #({ GKSE.group = GNG.X25519; GKSE.key_exchange = (reveal ks <: GKSE.keyShareEntry_key_exchange) });
  lemma_ch_ks_ext_conv (reveal ks);
  intro_vmatch_extCH_ks ks_vclist
    ([({ GKSE.group = GNG.X25519; GKSE.key_exchange = (reveal ks <: GKSE.keyShareEntry_key_exchange) })]
      <: GKSCH.keyShareClientHello_mid)
    #(ch_ks_high (reveal ks));
  let ks_elem_low : GECH.extensionClientHello_low = GECH.Extension_data_key_share_low ks_vclist;
  rewrite (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             (GECH.Extension_data_key_share_low ks_vclist) (ch_ks_high (reveal ks)))
      as (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             ks_elem_low (ch_ks_high (reveal ks)));

  (* ---- supported_versions extension element ---- *)
  fold (LPS.eq_as_slprop GOV.offeredVersion GOV.Offered_TLS_1p3 GOV.Offered_TLS_1p3);
  rewrite (LPS.eq_as_slprop GOV.offeredVersion GOV.Offered_TLS_1p3 GOV.Offered_TLS_1p3)
      as (GOV.offeredVersion_vmatch GOV.Offered_TLS_1p3 GOV.Offered_TLS_1p3);
  PPB.intro_vmatch_conv GOV.offeredVersion_vmatch GOV.offeredVersion_conv
    GOV.Offered_TLS_1p3 GOV.Offered_TLS_1p3 GOV.Offered_TLS_1p3;
  let sv_vclist = mk_singleton_vclist
    #_ #_ #(PPB.vmatch_conv GOV.offeredVersion_vmatch GOV.offeredVersion_conv)
    GOV.Offered_TLS_1p3 #GOV.Offered_TLS_1p3;
  lemma_ch_sv_ext_conv ();
  intro_vmatch_extCH_sv sv_vclist ([GOV.Offered_TLS_1p3] <: GSVCH.supportedVersionsClientHello_mid) #ch_sv_high;
  let sv_elem_low : GECH.extensionClientHello_low = GECH.Extension_data_supported_versions_low sv_vclist;
  rewrite (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             (GECH.Extension_data_supported_versions_low sv_vclist) ch_sv_high)
      as (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv
             sv_elem_low ch_sv_high);

  (* ---- 5-element extensions vclist ---- *)
  let ext_vec = V.alloc sn_elem_low 5sz;
  V.op_Array_Assignment ext_vec 1sz sg_elem_low;
  V.op_Array_Assignment ext_vec 2sz sa_elem_low;
  V.op_Array_Assignment ext_vec 3sz ks_elem_low;
  V.op_Array_Assignment ext_vec 4sz sv_elem_low;
  with vc. assert (V.pts_to ext_vec vc);
  rewrite (V.pts_to ext_vec vc)
      as (V.pts_to ext_vec (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.create 5 sn_elem_low) 1 sg_elem_low) 2 sa_elem_low) 3 ks_elem_low) 4 sv_elem_low));
  SM.seq_list_match_nil_intro (Seq.empty #GECH.extensionClientHello_low) ([] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  SM.seq_list_match_cons_intro sv_elem_low ch_sv_high
    (Seq.empty #GECH.extensionClientHello_low) ([] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  SM.seq_list_match_cons_intro ks_elem_low (ch_ks_high (reveal ks))
    (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low))
    ([ch_sv_high] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  SM.seq_list_match_cons_intro sa_elem_low (ch_sa_high (reveal sa))
    (Seq.cons ks_elem_low (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low)))
    ([ch_ks_high (reveal ks); ch_sv_high] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  SM.seq_list_match_cons_intro sg_elem_low ch_sg_high
    (Seq.cons sa_elem_low (Seq.cons ks_elem_low (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low))))
    ([ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  SM.seq_list_match_cons_intro sn_elem_low (ch_sn_high (reveal sni))
    (Seq.cons sg_elem_low (Seq.cons sa_elem_low (Seq.cons ks_elem_low (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low)))))
    ([ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high] <: list GECH.extensionClientHello)
    (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv);
  Seq.lemma_eq_elim
    (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.create 5 sn_elem_low) 1 sg_elem_low) 2 sa_elem_low) 3 ks_elem_low) 4 sv_elem_low)
    (Seq.cons sn_elem_low (Seq.cons sg_elem_low (Seq.cons sa_elem_low (Seq.cons ks_elem_low (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low))))));
  rewrite (SM.seq_list_match
            (Seq.cons sn_elem_low (Seq.cons sg_elem_low (Seq.cons sa_elem_low (Seq.cons ks_elem_low (Seq.cons sv_elem_low (Seq.empty #GECH.extensionClientHello_low))))))
            [ch_sn_high (reveal sni); ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high]
            (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv))
       as (SM.seq_list_match
            (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.create 5 sn_elem_low) 1 sg_elem_low) 2 sa_elem_low) 3 ks_elem_low) 4 sv_elem_low)
            [ch_sn_high (reveal sni); ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high]
            (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv));
  let exts_vclist = PPVCL.vmatch_vclist_some_intro 5sz ext_vec
    #(Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.create 5 sn_elem_low) 1 sg_elem_low) 2 sa_elem_low) 3 ks_elem_low) 4 sv_elem_low)
    #[ch_sn_high (reveal sni); ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high]
    [ch_sn_high (reveal sni); ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high];
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
             exts_vclist [ch_sn_high (reveal sni); ch_sg_high; ch_sa_high (reveal sa); ch_ks_high (reveal ks); ch_sv_high])
      as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
             exts_vclist (ch_exts (reveal sni) (reveal ks) (reveal sa)));

  (* ---- assemble clientHello_lowtype and fold the handshake sum vmatch ---- *)
  let cm : Ghost.erased GCH.clientHello_mid =
    Ghost.hide (poc_ch_mid (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa));
  let xch : GCH.clientHello_lowtype =
    (((GPV.TLS_1p2, rnd_lvec), (sid_lvec, cs_vclist)), (comp_lvec, exts_vclist));
  rewrite (LSeqB.vmatch_copy_seqbytes rnd_lvec (reveal rnd))
      as (LSeqB.vmatch_copy_seqbytes (snd (fst (fst xch))) (snd (fst (fst (Ghost.reveal cm)))));
  rewrite (LSeqB.vmatch_copy_seqbytes sid_lvec (reveal sid))
      as (LSeqB.vmatch_copy_seqbytes (fst (snd (fst xch))) (fst (snd (fst (Ghost.reveal cm)))));
  rewrite (PPVCL.vmatch_vclist (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv)
             cs_vclist (reveal cs <: list GCS.cipherSuite))
      as (PPVCL.vmatch_vclist (PPB.vmatch_conv GCS.cipherSuite_vmatch GCS.cipherSuite_conv)
             (snd (snd (fst xch))) (snd (snd (fst (Ghost.reveal cm)))));
  rewrite (LSeqB.vmatch_copy_seqbytes comp_lvec (Seq.create 1 0uy))
      as (LSeqB.vmatch_copy_seqbytes (fst (snd xch)) (fst (snd (Ghost.reveal cm))));
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
             exts_vclist (ch_exts (reveal sni) (reveal ks) (reveal sa)))
      as (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GECH.extensionClientHello_vmatch GECH.extensionClientHello_conv)
             (snd (snd xch)) (snd (snd (Ghost.reveal cm))));
  intro_handshake_client_hello_vmatch xch (Ghost.reveal cm);

  (* ---- write ---- *)
  A.pts_to_len out;
  let s = S.from_array out out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_client_hello_low xch)
             #(Ghost.hide (GHS.Body_client_hello_mid (Ghost.reveal cm)))
             s perr;
  with v'. assert (S.pts_to s v');
  lemma_ch_handshake_conv_fwd (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa);
  GHS.handshake_bytesize_eq (GHS.Body_client_hello ((poc_canonical_ch (reveal rnd) (reveal sni) (reveal ks) (reveal sid) (reveal cs) (reveal sa)) <: GHS.handshake_body_client_hello));
  S.to_array s;
  A.pts_to_len out;
  Rev.lemma_serialize_handshake_client_hello (Ghost.reveal ch);
  GHS.free_handshake (GHS.Body_client_hello_low xch)
    #(Ghost.hide (GHS.Body_client_hello_mid (Ghost.reveal cm)));
  sz
}
#pop-options
