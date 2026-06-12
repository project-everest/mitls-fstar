module TLS13.Impl.Parser

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module RV = TLS13.Wire.Spec.Reveal

module Arr = Pulse.Lib.Array
module ArrC = Pulse.Lib.Array.Core
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util

module LP = LowParse.Spec
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPBY = LowParse.PulseParse.Bytes
module LSeqB = LowParse.Pulse.SeqBytes

module GHS = TLS13.Wire.Generated.Handshake
module GHST = TLS13.Wire.Generated.HandshakeType
module GCV = TLS13.Wire.Generated.CertificateVerify
module GSS = TLS13.Wire.Generated.SignatureScheme
module LPC = LowParse.Pulse.Combinators

module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GEEED = TLS13.Wire.Generated.ExtensionEncryptedExtensions_extension_data_default
module GALPN = TLS13.Wire.Generated.ExtensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation
module GPNL = TLS13.Wire.Generated.ProtocolNameList
module GPN = TLS13.Wire.Generated.ProtocolName
module PPVCL = LowParse.PulseParse.VCList
module PPVD = LowParse.PulseParse.VLData
module SM = Pulse.Lib.SeqMatch
module SMU = Pulse.Lib.SeqMatch.Util
module GR = Pulse.Lib.GhostReference

module Core = Pulse.Lib.Core
module PE = TLS13.Impl.Parser.PureExists
module Tac = FStar.Tactics
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module RVN = TLS13.Wire.Spec.NonExact

module DW = TLS13.Impl.Parser.DecoderWF
module RVD = TLS13.Wire.Spec.RevealDecode
module Rec = TLS13.Record
module RecSpec = TLS13.Record.Spec
module CS = TLS13.Spec.ConnectionState

(* ServerHello-related generated modules (aliases match TLS13.Wire.Spec.Reveal). *)
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GKSSH = TLS13.Wire.Generated.KeyShareServerHello
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GSV = TLS13.Wire.Generated.SupportedVersionsServerHello
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GESHKS = TLS13.Wire.Generated.ExtensionServerHello_extension_data_key_share
module GESHSV = TLS13.Wire.Generated.ExtensionServerHello_extension_data_supported_versions
module LPITE = LowParse.PulseParse.IfThenElse

(* Certificate-related generated modules (aliases match TLS13.Wire.Spec.Reveal). *)
module GCert = TLS13.Wire.Generated.Certificate
module GCE = TLS13.Wire.Generated.CertificateEntry
module CC = TLS13.Impl.Parser.CertChain

(**
  Verified implementation of the M/L parser boundary.  See the interface
  TLS13.Impl.Parser.fsti for the full contracts.

  The handshake message structure is parsed exclusively through the
  QuackyDucky-generated handshake parser (validator + copyful reader); the outer
  record framing and ApplicationData decryption go through the verified record
  layer.  No byte-level handshake parsing is hand-rolled here.
**)

(* ----------------------------------------------------------------------- *)
(* Helper: copy an array prefix into a freshly allocated fixed-size Vec.    *)
(* ----------------------------------------------------------------------- *)

inline_for_extraction
fn alloc_copy_prefix
  (src: array U8.t)
  (src_len: SZ.t)
  (cap: SZ.t)
  (#p: perm)
  requires pts_to src #p 'src_bytes **
           pure (B.length 'src_bytes == SZ.v src_len /\ SZ.v src_len <= SZ.v cap)
  returns dst: V.vec U8.t
  ensures pts_to src #p 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v cap /\
                  B.length dst_bytes == SZ.v cap /\
                  SZ.v src_len <= SZ.v cap /\
                  Seq.equal (Seq.slice dst_bytes 0 (SZ.v src_len)) (Ghost.reveal 'src_bytes)))
{
  let dst = V.alloc 0uy cap;
  V.to_array_pts_to dst;
  Arr.pts_to_len src;
  let src_slice = S.from_array src src_len;
  let dst_slice = S.from_array (V.vec_to_array dst) cap;
  let dst_split = S.split dst_slice src_len;
  S.pts_to_len src_slice;
  S.pts_to_len (fst dst_split);
  S.copy (fst dst_split) src_slice;
  S.to_array src_slice;
  S.join (fst dst_split) (snd dst_split) dst_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.lemma_len_slice copied 0 (SZ.v src_len);
  dst
}

(* Copy the suffix [src[start..src_len)] into the prefix of a freshly allocated
   [cap]-size Vec (zero-padded).  Used by the ignored-post-handshake fallback. *)
inline_for_extraction
fn alloc_copy_suffix
  (src: array U8.t)
  (start: SZ.t)
  (src_len: SZ.t)
  (cap: SZ.t)
  (#p: perm)
  requires pts_to src #p 'src_bytes **
           pure (B.length 'src_bytes == SZ.v src_len /\ SZ.v start <= SZ.v src_len /\
                 SZ.v src_len - SZ.v start <= SZ.v cap)
  returns dst: V.vec U8.t
  ensures pts_to src #p 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v cap /\
                  B.length dst_bytes == SZ.v cap /\
                  B.length (Ghost.reveal 'src_bytes) == SZ.v src_len /\
                  SZ.v start <= SZ.v src_len /\
                  SZ.v src_len - SZ.v start <= SZ.v cap /\
                  Seq.equal (Seq.slice dst_bytes 0 (SZ.v src_len - SZ.v start))
                            (Seq.slice (Ghost.reveal 'src_bytes) (SZ.v start) (SZ.v src_len))))
{
  let sub_len = src_len `SZ.sub` start;
  let dst = V.alloc 0uy cap;
  V.to_array_pts_to dst;
  Arr.pts_to_len src;
  let src_slice = S.from_array src src_len;
  S.pts_to_len src_slice;
  let src_split = S.split src_slice start;
  S.pts_to_len (fst src_split);
  S.pts_to_len (snd src_split);
  let dst_slice = S.from_array (V.vec_to_array dst) cap;
  let dst_split = S.split dst_slice sub_len;
  S.pts_to_len (fst dst_split);
  S.copy (fst dst_split) (snd src_split);
  Seq.lemma_split (Ghost.reveal 'src_bytes) (SZ.v start);
  S.join (fst src_split) (snd src_split) src_slice;
  S.to_array src_slice;
  S.join (fst dst_split) (snd dst_split) dst_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.lemma_len_slice copied 0 (SZ.v sub_len);
  dst
}

(* Widen a byte to a SizeT, value-preserving. *)
inline_for_extraction
let u8_to_sz (b:U8.t) : (r:SZ.t{SZ.v r == U8.v b}) =
  SZ.uint16_to_sizet (Cast.uint8_to_uint16 b)

(* Copy the prefix [src[0..src_len)] of a (full) source Vec into the prefix of a
   freshly allocated [cap]-size Vec (zero-padded).  Used by the CertificateVerify
   arm to land the wire signature in the fixed [max_signature_len] storage. *)
inline_for_extraction
fn alloc_copy_vec_prefix
  (src: V.vec U8.t)
  (src_len: SZ.t)
  (cap: SZ.t)
  requires V.pts_to src 'src_bytes **
           pure (V.is_full_vec src /\ V.length src == SZ.v src_len /\
                 SZ.v src_len <= SZ.v cap)
  returns dst: V.vec U8.t
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v cap /\
                  B.length dst_bytes == SZ.v cap /\
                  SZ.v src_len <= SZ.v cap /\
                  Seq.equal (Seq.slice dst_bytes 0 (SZ.v src_len)) (Ghost.reveal 'src_bytes)))
{
  let dst = V.alloc 0uy cap;
  V.pts_to_len src;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) src_len;
  let dst_slice = S.from_array (V.vec_to_array dst) cap;
  let dst_split = S.split dst_slice src_len;
  S.pts_to_len src_slice;
  S.pts_to_len (fst dst_split);
  S.copy (fst dst_split) src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.join (fst dst_split) (snd dst_split) dst_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.lemma_len_slice copied 0 (SZ.v src_len);
  dst
}

(* Copy the slice [src[start..start+len)] of a source array into a freshly
   allocated EXACT-length ([len]) full Vec.  Used by the record decoders for the
   outer fragment, ciphertext, header AAD and recovered inner payload. *)
inline_for_extraction
fn alloc_copy_slice
  (src: array U8.t)
  (src_len: SZ.t)
  (start: SZ.t)
  (len: SZ.t)
  (#p: perm)
  requires pts_to src #p 'src_bytes **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 SZ.v start + SZ.v len <= SZ.v src_len)
  returns dst: V.vec U8.t
  ensures pts_to src #p 'src_bytes **
          (exists* dst_bytes.
            V.pts_to dst dst_bytes **
            pure (V.is_full_vec dst /\
                  V.length dst == SZ.v len /\
                  B.length dst_bytes == SZ.v len /\
                  B.length (Ghost.reveal 'src_bytes) == SZ.v src_len /\
                  SZ.v start + SZ.v len <= SZ.v src_len /\
                  Seq.equal dst_bytes
                            (Seq.slice (Ghost.reveal 'src_bytes)
                                       (SZ.v start) (SZ.v start + SZ.v len))))
{
  let dst = V.alloc 0uy len;
  V.to_array_pts_to dst;
  Arr.pts_to_len src;
  let src_slice = S.from_array src src_len;
  S.pts_to_len src_slice;
  let src_split1 = S.split src_slice start;
  S.pts_to_len (fst src_split1);
  S.pts_to_len (snd src_split1);
  let src_split2 = S.split (snd src_split1) len;
  S.pts_to_len (fst src_split2);
  S.pts_to_len (snd src_split2);
  let dst_slice = S.from_array (V.vec_to_array dst) len;
  S.pts_to_len dst_slice;
  S.copy dst_slice (fst src_split2);
  Seq.lemma_split (Seq.slice (Ghost.reveal 'src_bytes) (SZ.v start) (SZ.v src_len)) (SZ.v len);
  S.join (fst src_split2) (snd src_split2) (snd src_split1);
  Seq.lemma_split (Ghost.reveal 'src_bytes) (SZ.v start);
  S.join (fst src_split1) (snd src_split1) src_slice;
  S.to_array src_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.slice_slice (Ghost.reveal 'src_bytes) (SZ.v start) (SZ.v src_len) 0 (SZ.v len);
  dst
}

(* ----------------------------------------------------------------------- *)
(* parse_tls_message                                                       *)
(* ----------------------------------------------------------------------- *)

(* Bridges between the spec-reveal alert lemma and the L-level alert helpers. *)

let alert_byte_recognized (b:U8.t) : prop =
  U8.v b == 0 \/ U8.v b == 10 \/ U8.v b == 20 \/ U8.v b == 40 \/
  U8.v b == 46 \/ U8.v b == 47 \/ U8.v b == 50 \/ U8.v b == 51 \/
  U8.v b == 70 \/ U8.v b == 110

let lemma_alert_recognized (b:U8.t)
  : Lemma (requires alert_byte_recognized b)
          (ensures L.alert_description_matches b
                     (L.alert_description_of_wire_or_unexpected b))
  = ()

let lemma_alert_arm (fragment:B.bytes) (b1:U8.t)
  : Lemma
    (requires B.length fragment == 2 /\
              Seq.index fragment 1 == b1 /\
              alert_byte_recognized b1)
    (ensures WS.parse_tls_message T.Alert fragment ==
             Some (M.TlsAlert (L.alert_description_of_wire_or_unexpected b1)))
  = RV.lemma_ptm_alert fragment

let lemma_alert_wire_success (fragment:B.bytes) (b1:U8.t)
  : Lemma
    (requires B.length fragment == 2 /\
              Seq.index fragment 1 == b1 /\
              alert_byte_recognized b1)
    (ensures CT.parsed_message_wire_success 0x15uy fragment (L.LTlsAlert b1))
  = RV.lemma_ptm_alert fragment;
    introduce forall (alert:T.alert_description).
      L.alert_description_matches b1 alert ==>
      CT.wire_parse_success 0x15uy fragment (M.TlsAlert alert)
    with introduce _ ==> _
    with _. (
      L.lemma_alert_description_of_wire_matches b1 alert
    )

(* Generic "simple-bodied" existential lambda used as the bridge slprop. *)
unfold let eqlam (#t:Type) (a:t) : (t -> slprop) = fun (x:t) -> pure (x == a)

(* --- Alert: produce the pure-only is_valid existential. --------------- *)

let alert_q (b1:U8.t) (a:T.alert_description) : (T.alert_description -> prop) =
  fun (malert:T.alert_description) ->
    L.alert_description_matches b1 malert /\ M.TlsAlert a == M.TlsAlert malert

let alert_def_eq (b1:U8.t) (a:T.alert_description)
  : squash (op_exists_Star (fun (malert:T.alert_description) -> pure (alert_q b1 a malert))
            == L.is_valid_tls_message (L.LTlsAlert b1) (M.TlsAlert a))
  = _ by (Tac.norm [delta_only [`%L.is_valid_tls_message; `%alert_q]; iota]; Tac.trefl ())

let alert_iff (b1:U8.t) (a:T.alert_description)
  (sq:squash (L.alert_description_matches b1 a)) (malert:T.alert_description)
  : Lemma ((malert == a) <==> alert_q b1 a malert) = ()

let alert_equiv (b1:U8.t) (a:T.alert_description)
  (sq:squash (L.alert_description_matches b1 a))
  : Core.slprop_equiv (op_exists_Star (eqlam a))
                      (L.is_valid_tls_message (L.LTlsAlert b1) (M.TlsAlert a))
  = PE.mk_pure_exists_equiv a (alert_q b1 a)
      (L.is_valid_tls_message (L.LTlsAlert b1) (M.TlsAlert a))
      (alert_def_eq b1 a) (alert_iff b1 a sq)

(* Provide explicit witnesses for the [exists ct m. ...] success obligation. *)
let lemma_wire_exists (wire:U8.t) (ct0:T.content_type) (m0:M.tls_message)
  (fragment:B.bytes)
  : Lemma
    (requires L.content_type_matches wire ct0 /\
              WS.parse_tls_message ct0 fragment == Some m0)
    (ensures (exists (ct:T.content_type) (m:M.tls_message).
                L.content_type_matches wire ct /\
                WS.parse_tls_message ct fragment == Some m))
  = introduce exists (ct:T.content_type) (m:M.tls_message).
        (L.content_type_matches wire ct /\
         WS.parse_tls_message ct fragment == Some m)
    with ct0 m0
    and ()

ghost
fn intro_is_valid_alert (b1:U8.t) (a:T.alert_description)
  requires pure (L.alert_description_matches b1 a)
  ensures L.is_valid_tls_message (L.LTlsAlert b1) (M.TlsAlert a)
{
  intro_exists (eqlam a) a;
  PE.core_rewrite (op_exists_Star (eqlam a))
    (L.is_valid_tls_message (L.LTlsAlert b1) (M.TlsAlert a))
    (alert_equiv b1 a ());
}

(* --- KeyUpdate: produce the pure-only is_valid existential. ----------- *)

let ku_q (b4:U8.t) (req:M.key_update_request) : (M.key_update_request -> prop) =
  fun (mreq:M.key_update_request) ->
    L.key_update_request_matches b4 mreq /\ M.TlsKeyUpdate req == M.TlsKeyUpdate mreq

let ku_def_eq (b4:U8.t) (req:M.key_update_request)
  : squash (op_exists_Star (fun (mreq:M.key_update_request) -> pure (ku_q b4 req mreq))
            == L.is_valid_tls_message (L.LTlsKeyUpdate b4) (M.TlsKeyUpdate req))
  = _ by (Tac.norm [delta_only [`%L.is_valid_tls_message; `%ku_q]; iota]; Tac.trefl ())

let ku_iff (b4:U8.t) (req:M.key_update_request)
  (sq:squash (L.key_update_request_matches b4 req)) (mreq:M.key_update_request)
  : Lemma ((mreq == req) <==> ku_q b4 req mreq) = ()

let ku_equiv (b4:U8.t) (req:M.key_update_request)
  (sq:squash (L.key_update_request_matches b4 req))
  : Core.slprop_equiv (op_exists_Star (eqlam req))
                      (L.is_valid_tls_message (L.LTlsKeyUpdate b4) (M.TlsKeyUpdate req))
  = PE.mk_pure_exists_equiv req (ku_q b4 req)
      (L.is_valid_tls_message (L.LTlsKeyUpdate b4) (M.TlsKeyUpdate req))
      (ku_def_eq b4 req) (ku_iff b4 req sq)

ghost
fn intro_is_valid_key_update (b4:U8.t) (req:M.key_update_request)
  requires pure (L.key_update_request_matches b4 req)
  ensures L.is_valid_tls_message (L.LTlsKeyUpdate b4) (M.TlsKeyUpdate req)
{
  intro_exists (eqlam req) req;
  PE.core_rewrite (op_exists_Star (eqlam req))
    (L.is_valid_tls_message (L.LTlsKeyUpdate b4) (M.TlsKeyUpdate req))
    (ku_equiv b4 req ());
}

(* --- Handshake: eliminate the packed vmatch for the Finished arm. --------- *)

(* Given the packed read-result predicate for a [Body_finished_low x] handshake
   value, recover ownership of the underlying 32-byte verify-data Vec and the
   fact that the high-level handshake value is [Body_finished cm]. *)
(* --- Handshake: eliminate the packed vmatch for the Finished arm. --------- *)

(* Recover the tag-agreement fact buried in [handshake_vmatch] without naming
   its (large) payload match: unfold exposes the [pure] tag conjunct, fold
   re-packs the rest. *)
ghost
fn peek_handshake_tag (xl: GHS.handshake_low) (#vm: GHS.handshake_mid)
  requires GHS.handshake_vmatch xl vm
  ensures GHS.handshake_vmatch xl vm **
          pure (GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
{
  unfold (GHS.handshake_vmatch xl vm);
  fold (GHS.handshake_vmatch xl vm);
}

(* Tag agreement pins the mid constructor for a [Body_finished_low]. *)
let lemma_finished_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
    (requires GHS.Body_finished_low? xl /\
              GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
    (ensures GHS.Body_finished_mid? vm)
  = ()

(* Given the packed read-result predicate for a [Body_finished_low x] handshake
   value, recover ownership of the underlying 32-byte verify-data Vec and the
   fact that the high-level handshake value is [Body_finished cm]. *)
ghost
fn elim_vmatch_finished
  (x: PPBY.lvec U8.t)
  (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
             (GHS.Body_finished_low x) v
  ensures exists* (cm: Seq.seq U8.t).
            V.pts_to x.PPBY.lvec_vec cm **
            pure (V.is_full_vec x.PPBY.lvec_vec /\
                  Seq.length cm == 32 /\
                  v == GHS.Body_finished cm)
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_finished_low x) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_finished_low x) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_finished_low x);
  lemma_finished_constructor (GHS.Body_finished_low x) vm;
  let cm0 = GHS.Body_finished_mid?._0 vm;
  rewrite (GHS.handshake_vmatch (GHS.Body_finished_low x) vm)
       as (GHS.handshake_vmatch (GHS.Body_finished_low x) (GHS.Body_finished_mid cm0));
  unfold (GHS.handshake_vmatch (GHS.Body_finished_low x) (GHS.Body_finished_mid cm0));
  rewrite (GHS.handshake_body_finished_vmatch x cm0)
       as (LSeqB.vmatch_copy_seqbytes x cm0);
  unfold (LSeqB.vmatch_copy_seqbytes x cm0);
  V.pts_to_len x.PPBY.lvec_vec;
}

(* --- CertificateVerify: eliminate the packed vmatch. ---------------------- *)

(* Tag agreement pins the mid constructor for a [Body_certificate_verify_low]. *)
let lemma_cv_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
   (requires GHS.Body_certificate_verify_low? xl /\
             GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
   (ensures GHS.Body_certificate_verify_mid? vm)
  = ()

(* Unwind the CertificateVerify conv: a [Body_certificate_verify_mid cvm] whose
  conv is [Some v] forces [v] to be the obvious [Body_certificate_verify] value
  whose signature is the (<=65535-byte) mid sequence. *)
let lemma_cv_conv (cvm: GHS.handshake_body_certificate_verify_mid) (v: GHS.handshake)
  : Lemma
   (requires GHS.handshake_conv (GHS.Body_certificate_verify_mid cvm) == Some v)
   (ensures Seq.length (snd cvm) <= 65535 /\
            v == GHS.Body_certificate_verify
                   ({ GCV.algorithm = fst cvm;
                      GCV.signature = (snd cvm <: GCV.certificateVerify_signature) }))
  = ()

(* Recover the owned signature Vec and the high-level CertificateVerify shape
  from the packed read-result predicate for a [Body_certificate_verify_low]. *)
ghost
fn elim_vmatch_certificate_verify
  (xcv: GHS.handshake_body_certificate_verify_lowtype)
  (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_certificate_verify_low xcv) v
  ensures exists* (sig_seq: Seq.seq U8.t).
           V.pts_to (snd xcv).PPBY.lvec_vec sig_seq **
           pure (V.is_full_vec (snd xcv).PPBY.lvec_vec /\
                 Seq.length sig_seq == SZ.v (snd xcv).PPBY.lvec_len /\
                 Seq.length sig_seq <= 65535 /\
                 v == GHS.Body_certificate_verify
                        ({ GCV.algorithm = fst xcv;
                           GCV.signature = (sig_seq <: GCV.certificateVerify_signature) }))
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
   (GHS.Body_certificate_verify_low xcv) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv) vm **
                  pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_certificate_verify_low xcv);
  lemma_cv_constructor (GHS.Body_certificate_verify_low xcv) vm;
  let cvm0 = GHS.Body_certificate_verify_mid?._0 vm;
  rewrite (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv) vm)
      as (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv)
            (GHS.Body_certificate_verify_mid cvm0));
  unfold (GHS.handshake_vmatch (GHS.Body_certificate_verify_low xcv)
           (GHS.Body_certificate_verify_mid cvm0));
  rewrite (GHS.handshake_body_certificate_verify_vmatch xcv cvm0)
      as (LPC.vmatch_pair GSS.signatureScheme_vmatch
            GCV.certificateVerify_signature_vmatch xcv cvm0);
  unfold (LPC.vmatch_pair GSS.signatureScheme_vmatch
           GCV.certificateVerify_signature_vmatch xcv cvm0);
  rewrite (GSS.signatureScheme_vmatch (fst xcv) (fst cvm0))
      as (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst cvm0));
  unfold (LPS.eq_as_slprop GSS.signatureScheme (fst xcv) (fst cvm0));
  rewrite (GCV.certificateVerify_signature_vmatch (snd xcv) (snd cvm0))
      as (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd cvm0));
  unfold (LSeqB.vmatch_copy_seqbytes (snd xcv) (snd cvm0));
  V.pts_to_len (snd xcv).PPBY.lvec_vec;
  lemma_cv_conv cvm0 v;
}

(* Tag agreement pins the mid constructor for a [Body_key_update_low]. *)
let lemma_key_update_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
    (requires GHS.Body_key_update_low? xl /\
              GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
    (ensures GHS.Body_key_update_mid? vm)
  = ()

(* A [Body_key_update_mid] necessarily converts to a [Body_key_update]. *)
let lemma_key_update_conv (vm: GHS.handshake_mid) (v: GHS.handshake)
  : Lemma
    (requires GHS.Body_key_update_mid? vm /\ GHS.handshake_conv vm == Some v)
    (ensures GHS.Body_key_update? v)
  = ()

(* Recover (without consuming) the pure fact that the high-level handshake value
   behind a [Body_key_update_low] read-result is a [Body_key_update] (whose synth
   is [None], routing the record through the byte-level fallback). *)
ghost
fn peek_key_update_high (x: GHS.handshake_body_key_update_lowtype) (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
             (GHS.Body_key_update_low x) v
  ensures PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
             (GHS.Body_key_update_low x) v **
          pure (GHS.Body_key_update? v)
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_key_update_low x) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_key_update_low x) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_key_update_low x);
  lemma_key_update_constructor (GHS.Body_key_update_low x) vm;
  lemma_key_update_conv vm v;
  PPB.intro_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_key_update_low x) vm v;
}

(* --- ClientHello: pin the constructor (synth maps it to None) ------------- *)

(* Tag agreement pins the mid constructor for a [Body_client_hello_low]. *)
let lemma_client_hello_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
    (requires GHS.Body_client_hello_low? xl /\
              GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
    (ensures GHS.Body_client_hello_mid? vm)
  = ()

(* A [Body_client_hello_mid] necessarily converts to a [Body_client_hello]. *)
let lemma_client_hello_conv (vm: GHS.handshake_mid) (v: GHS.handshake)
  : Lemma
    (requires GHS.Body_client_hello_mid? vm /\ GHS.handshake_conv vm == Some v)
    (ensures GHS.Body_client_hello? v)
  = ()

(* Recover (without consuming) the pure fact that the high-level handshake value
   behind a [Body_client_hello_low] read-result is a [Body_client_hello] (whose
   synth is [None]: a client never receives a ClientHello). *)
ghost
fn peek_client_hello_high (x: GHS.handshake_body_client_hello_lowtype) (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
             (GHS.Body_client_hello_low x) v
  ensures PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
             (GHS.Body_client_hello_low x) v **
          pure (GHS.Body_client_hello? v)
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_client_hello_low x) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_client_hello_low x) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_client_hello_low x);
  lemma_client_hello_constructor (GHS.Body_client_hello_low x) vm;
  lemma_client_hello_conv vm v;
  PPB.intro_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_client_hello_low x) vm v;
}

(* --- EncryptedExtensions: eliminate / re-introduce the packed vmatch ------ *)

(* Tag agreement pins the mid constructor for a [Body_encrypted_extensions_low]. *)
let lemma_ee_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
   (requires GHS.Body_encrypted_extensions_low? xl /\
             GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
   (ensures GHS.Body_encrypted_extensions_mid? vm)
  = ()

(* Unwind the EncryptedExtensions conv: a [Body_encrypted_extensions_mid cm]
   whose conv is [Some v] forces [v] to be [Body_encrypted_extensions cm] and the
   list to fit the 65535-byte vldata bound. *)
let lemma_ee_conv (cm: GEE.encryptedExtensions_mid) (v: GHS.handshake)
  : Lemma
   (requires GHS.handshake_conv (GHS.Body_encrypted_extensions_mid cm) == Some v)
   (ensures GEE.encryptedExtensions_list_bytesize cm <= 65535 /\
            v == GHS.Body_encrypted_extensions
                   (cm <: GHS.handshake_body_encrypted_extensions))
  = ()

(* Expose the underlying vclist of extensions from the packed read result. *)
ghost
fn elim_vmatch_encrypted_extensions
  (xee: GHS.handshake_body_encrypted_extensions_lowtype)
  (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_encrypted_extensions_low xee) v
  ensures exists* (cee: GEE.encryptedExtensions_mid).
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee cee **
           pure (GEE.encryptedExtensions_list_bytesize cee <= 65535 /\
                 GHS.handshake_conv (GHS.Body_encrypted_extensions_mid cee) == Some v /\
                 v == GHS.Body_encrypted_extensions
                        (cee <: GHS.handshake_body_encrypted_extensions))
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
   (GHS.Body_encrypted_extensions_low xee) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_encrypted_extensions_low xee);
  lemma_ee_constructor (GHS.Body_encrypted_extensions_low xee) vm;
  let cm0 = GHS.Body_encrypted_extensions_mid?._0 vm;
  rewrite (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee) vm)
      as (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
            (GHS.Body_encrypted_extensions_mid cm0));
  unfold (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
           (GHS.Body_encrypted_extensions_mid cm0));
  rewrite (GHS.handshake_body_encrypted_extensions_vmatch xee cm0)
      as (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                             GEEE.extensionEncryptedExtensions_conv)
            xee cm0);
  lemma_ee_conv cm0 v;
}

(* Re-pack the extensions vclist back into the handshake read result so it can be
   freed by the generated [free_handshake]. *)
ghost
fn intro_vmatch_encrypted_extensions
  (xee: GHS.handshake_body_encrypted_extensions_lowtype)
  (cee: GEE.encryptedExtensions_mid)
  (#v: GHS.handshake)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee cee **
           pure (GHS.handshake_conv (GHS.Body_encrypted_extensions_mid cee) == Some v)
  ensures PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_encrypted_extensions_low xee) v
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee cee)
      as (GHS.handshake_body_encrypted_extensions_vmatch xee cee);
  fold (GHS.handshake_vmatch (GHS.Body_encrypted_extensions_low xee)
          (GHS.Body_encrypted_extensions_mid cee));
  PPB.intro_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_encrypted_extensions_low xee) (GHS.Body_encrypted_extensions_mid cee) v;
}

(* --- extEE element level: detect ALPN and dig into the protocol-name list -- *)

(* Recover the tag-agreement fact buried in an extension element's vmatch. *)
ghost
fn peek_ext_tag (xl: GEEE.extensionEncryptedExtensions_low)
               (#vm: GEEE.extensionEncryptedExtensions_mid)
  requires GEEE.extensionEncryptedExtensions_vmatch xl vm
  ensures GEEE.extensionEncryptedExtensions_vmatch xl vm **
          pure (GEEE.extensionEncryptedExtensions_low_tag xl ==
                GEEE.extensionEncryptedExtensions_mid_tag vm)
{
  unfold (GEEE.extensionEncryptedExtensions_vmatch xl vm);
  fold (GEEE.extensionEncryptedExtensions_vmatch xl vm);
}

(* Tag agreement + conv determine whether the high element is an ALPN extension. *)
let lemma_extEE_alpn_iff
  (xl: GEEE.extensionEncryptedExtensions_low)
  (vm: GEEE.extensionEncryptedExtensions_mid)
  (h:  GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires GEEE.extensionEncryptedExtensions_low_tag xl ==
                GEEE.extensionEncryptedExtensions_mid_tag vm /\
              GEEE.extensionEncryptedExtensions_conv vm == Some h)
    (ensures GEEE.Extension_data_application_layer_protocol_negotiation_low? xl <==>
             GEEE.Extension_data_application_layer_protocol_negotiation? h)
  = ()

(* Given a converted element vmatch, expose whether the high value is an ALPN
   extension (without consuming the resource), matching the runtime low tag. *)
ghost
fn elim_alpn_iff (elem: GEEE.extensionEncryptedExtensions_low)
                 (#h: GEEE.extensionEncryptedExtensions)
  requires PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
             GEEE.extensionEncryptedExtensions_conv elem h
  ensures PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
            GEEE.extensionEncryptedExtensions_conv elem h **
          pure (GEEE.Extension_data_application_layer_protocol_negotiation_low? elem <==>
                GEEE.Extension_data_application_layer_protocol_negotiation? h)
{
  PPB.elim_vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
    GEEE.extensionEncryptedExtensions_conv elem h;
  with vm. assert (GEEE.extensionEncryptedExtensions_vmatch elem vm **
                   pure (GEEE.extensionEncryptedExtensions_conv vm == Some h));
  peek_ext_tag elem;
  lemma_extEE_alpn_iff elem vm h;
  PPB.intro_vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
    GEEE.extensionEncryptedExtensions_conv elem vm h;
}

(* --- ALPN extension data level: expose the inner protocol-name vclist ------ *)

(* Tag agreement pins the mid constructor for an ALPN extension element. *)
let lemma_alpn_data_constructor (xl: GEEE.extensionEncryptedExtensions_low)
                                (vm: GEEE.extensionEncryptedExtensions_mid)
  : Lemma
    (requires GEEE.Extension_data_application_layer_protocol_negotiation_low? xl /\
              GEEE.extensionEncryptedExtensions_low_tag xl ==
                GEEE.extensionEncryptedExtensions_mid_tag vm)
    (ensures GEEE.Extension_data_application_layer_protocol_negotiation_mid? vm)
  = ()

(* The ALPN extension conv exposes the underlying protocol-name list verbatim. *)
let lemma_alpn_data_conv
  (cm: GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation_mid)
  (h:  GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires GEEE.extensionEncryptedExtensions_conv
                (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm) == Some h)
    (ensures GEEE.Extension_data_application_layer_protocol_negotiation? h /\
             (GEEE.Extension_data_application_layer_protocol_negotiation?._0 h
                <: list GPN.protocolName) == (cm <: list GPN.protocolName))
  = ()

(* Eliminate an ALPN extension element's vmatch down to the protocol-name vclist. *)
ghost
fn elim_vmatch_alpn_data
  (v0: GPNL.protocolNameList_lowtype)
  (elem: GEEE.extensionEncryptedExtensions_low)
  (#h: GEEE.extensionEncryptedExtensions)
  requires PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
             GEEE.extensionEncryptedExtensions_conv elem h **
           pure (elem == GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
  ensures exists* (cm: list GPN.protocolName).
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
           pure (GEEE.Extension_data_application_layer_protocol_negotiation? h /\
                 (GEEE.Extension_data_application_layer_protocol_negotiation?._0 h
                    <: list GPN.protocolName) == cm /\
                 GEEE.extensionEncryptedExtensions_conv
                   (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm) == Some h)
{
  PPB.elim_vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
    GEEE.extensionEncryptedExtensions_conv elem h;
  with vm. assert (GEEE.extensionEncryptedExtensions_vmatch elem vm **
                   pure (GEEE.extensionEncryptedExtensions_conv vm == Some h));
  peek_ext_tag elem;
  lemma_alpn_data_constructor elem vm;
  let cm0 = GEEE.Extension_data_application_layer_protocol_negotiation_mid?._0 vm;
  rewrite (GEEE.extensionEncryptedExtensions_vmatch elem vm)
      as (GEEE.extensionEncryptedExtensions_vmatch
            (GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
            (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm0));
  unfold (GEEE.extensionEncryptedExtensions_vmatch
            (GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
            (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm0));
  rewrite (GALPN.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation_vmatch v0 cm0)
      as (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm0);
  lemma_alpn_data_conv cm0 h;
}

(* Re-pack the protocol-name vclist back into an ALPN extension element. *)
ghost
fn intro_vmatch_alpn_data
  (v0: GPNL.protocolNameList_lowtype)
  (cm: list GPN.protocolName)
  (#h: GEEE.extensionEncryptedExtensions)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
           pure (GEEE.extensionEncryptedExtensions_conv
                   (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm) == Some h)
  ensures PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
            GEEE.extensionEncryptedExtensions_conv
            (GEEE.Extension_data_application_layer_protocol_negotiation_low v0) h
{
  rewrite (PPVCL.vmatch_vclist
             (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm)
      as (GALPN.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation_vmatch v0 cm);
  fold (GEEE.extensionEncryptedExtensions_vmatch
          (GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
          (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm));
  PPB.intro_vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
    GEEE.extensionEncryptedExtensions_conv
    (GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
    (GEEE.Extension_data_application_layer_protocol_negotiation_mid cm) h;
}

(* A successfully converted protocol name is <=255 bytes and equals its mid seq. *)
let lemma_protocolName_conv_some (sq: Seq.seq U8.t) (pn: GPN.protocolName)
  : Lemma
    (requires GPN.protocolName_conv sq == Some pn)
    (ensures Seq.length sq <= 255 /\ (pn <: Seq.seq U8.t) == sq)
  = ()

(* A parsed protocol-name list is non-empty (its wire bytesize is >= 2). *)
let lemma_protocolNameList_nonempty
  (pnl: GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : Lemma (ensures FStar.List.Tot.length (pnl <: list GPN.protocolName) > 0)
  = if FStar.List.Tot.length (pnl <: list GPN.protocolName) = 0
    then GPNL.protocolNameList_list_bytesize_nil
    else ()

(* Copy the first protocol name of a (non-empty) protocol-name list into a fresh
   [max_alpn_len]=255-byte Vec (zero-padded), restoring the input vclist.  The
   returned length is the real name length (<=255). *)
fn copy_first_protocol_name
  (v0: GPNL.protocolNameList_lowtype)
  (#cm: Ghost.erased (list GPN.protocolName))
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
           pure (FStar.List.Tot.length cm > 0)
  returns res: (V.vec U8.t & SZ.t)
  ensures PPVCL.vmatch_vclist
            (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
          (exists* bytes. V.pts_to (fst res) bytes **
            pure (V.is_full_vec (fst res) /\ V.length (fst res) == 255 /\
                  Seq.length bytes == 255 /\
                  FStar.List.Tot.length cm > 0 /\
                  SZ.v (snd res) <= 255 /\
                  Seq.equal (Seq.slice bytes 0 (SZ.v (snd res)))
                            (FStar.List.Tot.index cm 0 <: Seq.seq U8.t)))
{
  match v0 {
    None -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) None cm);
      assert (pure False);
      unreachable ()
    }
    Some nv -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm);
      with s. assert (V.pts_to (snd nv) s **
                      SM.seq_list_match s cm
                        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      V.pts_to_len (snd nv);
      SMU.seq_list_match_index_trade
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) s cm 0;
      let el0 = V.op_Array_Access (snd nv) 0sz;
      Trade.rewrite_with_trade
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           (Seq.index s 0) (FStar.List.Tot.index cm 0))
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0));
      Trade.trans
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0))
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           (Seq.index s 0) (FStar.List.Tot.index cm 0))
        (SM.seq_list_match s cm
           (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      PPB.elim_vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
        el0 (FStar.List.Tot.index cm 0);
      with sq. assert (GPN.protocolName_vmatch el0 sq **
                       pure (GPN.protocolName_conv sq == Some (FStar.List.Tot.index cm 0)));
      lemma_protocolName_conv_some sq (FStar.List.Tot.index cm 0);
      rewrite (GPN.protocolName_vmatch el0 sq)
          as (LSeqB.vmatch_copy_seqbytes el0 sq);
      unfold (LSeqB.vmatch_copy_seqbytes el0 sq);
      V.pts_to_len el0.PPBY.lvec_vec;
      let nm_len = el0.PPBY.lvec_len;
      let dst = alloc_copy_vec_prefix el0.PPBY.lvec_vec nm_len 255sz;
      fold (LSeqB.vmatch_copy_seqbytes el0 sq);
      rewrite (LSeqB.vmatch_copy_seqbytes el0 sq)
          as (GPN.protocolName_vmatch el0 sq);
      PPB.intro_vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
        el0 sq (FStar.List.Tot.index cm 0);
      Trade.elim
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0))
        (SM.seq_list_match s cm
           (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      fold (PPVCL.vmatch_vclist
              (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm);
      (dst, nm_len)
    }
  }
}

(* Copy the prefix [src[0..src_len)] of a (full) source Vec into the prefix of an
   existing 255-byte (full) destination Vec.  Used by the EncryptedExtensions ALPN
   scan to land the negotiated protocol name into a pre-allocated [max_alpn_len]
   buffer. *)
inline_for_extraction
fn copy_vec_prefix_into
  (dst: V.vec U8.t)
  (src: V.vec U8.t)
  (src_len: SZ.t)
  requires V.pts_to dst 'dst_bytes ** V.pts_to src 'src_bytes **
           pure (V.is_full_vec dst /\ V.length dst == 255 /\
                 V.is_full_vec src /\ V.length src == SZ.v src_len /\
                 SZ.v src_len <= 255)
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes2.
            V.pts_to dst dst_bytes2 **
            pure (V.is_full_vec dst /\
                  V.length dst == 255 /\
                  B.length dst_bytes2 == 255 /\
                  SZ.v src_len <= 255 /\
                  Seq.equal (Seq.slice dst_bytes2 0 (SZ.v src_len)) (Ghost.reveal 'src_bytes)))
{
  V.pts_to_len src;
  V.pts_to_len dst;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) src_len;
  let dst_slice = S.from_array (V.vec_to_array dst) 255sz;
  let dst_split = S.split dst_slice src_len;
  S.pts_to_len src_slice;
  S.pts_to_len (fst dst_split);
  S.copy (fst dst_split) src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.join (fst dst_split) (snd dst_split) dst_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.lemma_len_slice copied 0 (SZ.v src_len);
}

(* Overwrite a (full) 32-byte destination Vec with the entire content of a (full)
   32-byte source Vec.  Used by the ServerHello key_share scan to land the 32-byte
   x25519 key into a pre-allocated buffer. *)
inline_for_extraction
fn copy_vec_32_into
  (dst: V.vec U8.t)
  (src: V.vec U8.t)
  requires V.pts_to dst 'dst_bytes ** V.pts_to src 'src_bytes **
           pure (V.is_full_vec dst /\ V.length dst == 32 /\
                 V.is_full_vec src /\ V.length src == 32)
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes2.
            V.pts_to dst dst_bytes2 **
            pure (V.is_full_vec dst /\
                  V.length dst == 32 /\
                  Seq.length dst_bytes2 == 32 /\
                  Seq.equal dst_bytes2 (Ghost.reveal 'src_bytes)))
{
  V.pts_to_len src;
  V.pts_to_len dst;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) 32sz;
  let dst_slice = S.from_array (V.vec_to_array dst) 32sz;
  S.pts_to_len src_slice;
  S.pts_to_len dst_slice;
  S.copy dst_slice src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
}

(* Copy the first protocol name of a (non-empty) protocol-name list into the
   prefix of an existing 255-byte destination Vec (in place), restoring the input
   vclist.  Returns the real name length (<=255). *)
fn copy_first_protocol_name_into
  (dst: V.vec U8.t)
  (v0: GPNL.protocolNameList_lowtype)
  (#cm: Ghost.erased (list GPN.protocolName))
  requires V.pts_to dst 'dst_bytes **
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
           pure (V.is_full_vec dst /\ V.length dst == 255 /\
                 FStar.List.Tot.length cm > 0)
  returns nm_len: SZ.t
  ensures PPVCL.vmatch_vclist
            (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm **
          (exists* dst_bytes2. V.pts_to dst dst_bytes2 **
            pure (V.is_full_vec dst /\ V.length dst == 255 /\
                  Seq.length dst_bytes2 == 255 /\
                  FStar.List.Tot.length cm > 0 /\
                  SZ.v nm_len <= 255 /\
                  Seq.equal (Seq.slice dst_bytes2 0 (SZ.v nm_len))
                            (FStar.List.Tot.index cm 0 <: Seq.seq U8.t)))
{
  match v0 {
    None -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) None cm);
      assert (pure False);
      unreachable ()
    }
    Some nv -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm);
      with s. assert (V.pts_to (snd nv) s **
                      SM.seq_list_match s cm
                        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      V.pts_to_len (snd nv);
      SMU.seq_list_match_index_trade
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) s cm 0;
      let el0 = V.op_Array_Access (snd nv) 0sz;
      Trade.rewrite_with_trade
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           (Seq.index s 0) (FStar.List.Tot.index cm 0))
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0));
      Trade.trans
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0))
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           (Seq.index s 0) (FStar.List.Tot.index cm 0))
        (SM.seq_list_match s cm
           (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      PPB.elim_vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
        el0 (FStar.List.Tot.index cm 0);
      with sq. assert (GPN.protocolName_vmatch el0 sq **
                       pure (GPN.protocolName_conv sq == Some (FStar.List.Tot.index cm 0)));
      lemma_protocolName_conv_some sq (FStar.List.Tot.index cm 0);
      rewrite (GPN.protocolName_vmatch el0 sq)
          as (LSeqB.vmatch_copy_seqbytes el0 sq);
      unfold (LSeqB.vmatch_copy_seqbytes el0 sq);
      V.pts_to_len el0.PPBY.lvec_vec;
      let nm_len = el0.PPBY.lvec_len;
      copy_vec_prefix_into dst el0.PPBY.lvec_vec nm_len;
      fold (LSeqB.vmatch_copy_seqbytes el0 sq);
      rewrite (LSeqB.vmatch_copy_seqbytes el0 sq)
          as (GPN.protocolName_vmatch el0 sq);
      PPB.intro_vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
        el0 sq (FStar.List.Tot.index cm 0);
      Trade.elim
        (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv
           el0 (FStar.List.Tot.index cm 0))
        (SM.seq_list_match s cm
           (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv));
      fold (PPVCL.vmatch_vclist
              (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) (Some nv) cm)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm);
      nm_len
    }
  }
}

(* Scan the EncryptedExtensions extension list for the first ALPN extension,
   copying its first protocol name into a fresh [max_alpn_len]=255-byte Vec.
   Returns [(alpn_vec, alpn_len, has_alpn)] reflecting the spec scan
   [synth_encrypted_extensions]: when an ALPN extension is present [has_alpn] is
   set and the Vec prefix holds the negotiated protocol name; otherwise
   [has_alpn] is false (the scan reached the end of the list). *)
fn scan_ee_alpn
  (xee: GHS.handshake_body_encrypted_extensions_lowtype)
  (#cee: Ghost.erased GEE.encryptedExtensions_mid)
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv)
             xee cee
  returns res: (V.vec U8.t & SZ.t & bool)
  ensures PPVCL.vmatch_vclist
            (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                             GEEE.extensionEncryptedExtensions_conv)
            xee cee **
          (exists* bytes. V.pts_to (Mktuple3?._1 res) bytes **
            pure (
              V.is_full_vec (Mktuple3?._1 res) /\
              V.length (Mktuple3?._1 res) == L.max_alpn_len /\
              Seq.length bytes == L.max_alpn_len /\
              SZ.v (Mktuple3?._2 res) <= L.max_alpn_len /\
              Some? (RV.reveal_synth_encrypted_extensions cee) /\
              L.optional_byte_prefix_matches
                (Mktuple3?._3 res) bytes (Mktuple3?._2 res)
                (Some?.v (RV.reveal_synth_encrypted_extensions cee)).M.negotiated_alpn))
{
  let alpn_vec = V.alloc 0uy 255sz;
  match xee {
    None -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) None cee);
      RV.lemma_synth_ee_nil ();
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) None cee);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) None cee)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) xee cee);
      (alpn_vec, 0sz, false)
    }
    Some nv -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) (Some nv) cee);
      with s. assert (V.pts_to (snd nv) s **
                      SM.seq_list_match s cee
                        (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                         GEEE.extensionEncryptedExtensions_conv));
      V.pts_to_len (snd nv);
      let count = fst nv;
      let mut i = 0sz;
      let mut found = false;
      let mut alpn_len = 0sz;
      while (
        let f = !found;
        let iv = !i;
        (not f) && (iv `SZ.lt` count)
      )
      invariant exists* iv fnd al abytes.
        R.pts_to i iv **
        R.pts_to found fnd **
        R.pts_to alpn_len al **
        V.pts_to (snd nv) s **
        SM.seq_list_match s cee
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv) **
        V.pts_to alpn_vec abytes **
        pure (
          SZ.v iv <= SZ.v count /\
          SZ.v count == FStar.List.Tot.length cee /\
          Seq.length s == FStar.List.Tot.length cee /\
          V.is_full_vec (snd nv) /\
          FStar.List.Tot.length cee > 0 /\
          V.is_full_vec alpn_vec /\ V.length alpn_vec == 255 /\ Seq.length abytes == 255 /\
          SZ.v al <= 255 /\
          RV.reveal_synth_encrypted_extensions cee ==
            RV.reveal_synth_encrypted_extensions (RV.list_drop (SZ.v iv) cee) /\
          (fnd ==> (Some? (RV.reveal_synth_encrypted_extensions cee) /\
                    SZ.v al <= 255 /\
                    L.optional_byte_prefix_matches true abytes al
                      (Some?.v (RV.reveal_synth_encrypted_extensions cee)).M.negotiated_alpn)))
      {
        let iv = !i;
        assert (pure (SZ.v iv < FStar.List.Tot.length cee));
        let el = V.op_Array_Access (snd nv) iv;
        SMU.seq_list_match_index_trade
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv) s cee (SZ.v iv);
        Trade.rewrite_with_trade
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cee (SZ.v iv)))
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv
             el (FStar.List.Tot.index cee (SZ.v iv)));
        Trade.trans
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv
             el (FStar.List.Tot.index cee (SZ.v iv)))
          (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                           GEEE.extensionEncryptedExtensions_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cee (SZ.v iv)))
          (SM.seq_list_match s cee
             (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                              GEEE.extensionEncryptedExtensions_conv));
        elim_alpn_iff el;
        if (GEEE.Extension_data_application_layer_protocol_negotiation_low? el) {
            let v0 = GEEE.Extension_data_application_layer_protocol_negotiation_low?._0 el;
            elim_vmatch_alpn_data v0 el;
            with cm. assert (PPVCL.vmatch_vclist
                              (PPB.vmatch_conv GPN.protocolName_vmatch GPN.protocolName_conv) v0 cm);
            lemma_protocolNameList_nonempty
              (GEEE.Extension_data_application_layer_protocol_negotiation?._0
                 (FStar.List.Tot.index cee (SZ.v iv)));
            let name_len = copy_first_protocol_name_into alpn_vec v0;
            intro_vmatch_alpn_data v0 cm
              #(FStar.List.Tot.index cee (SZ.v iv));
            rewrite (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                     GEEE.extensionEncryptedExtensions_conv
                       (GEEE.Extension_data_application_layer_protocol_negotiation_low v0)
                       (FStar.List.Tot.index cee (SZ.v iv)))
                as (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                    GEEE.extensionEncryptedExtensions_conv
                       (Seq.index s (SZ.v iv))
                       (FStar.List.Tot.index cee (SZ.v iv)));
            Trade.elim
              (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                               GEEE.extensionEncryptedExtensions_conv
                 (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cee (SZ.v iv)))
              (SM.seq_list_match s cee
                 (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                  GEEE.extensionEncryptedExtensions_conv));
            RV.lemma_list_drop_index cee (SZ.v iv);
            RV.lemma_synth_ee_cons_alpn
              (GEEE.Extension_data_application_layer_protocol_negotiation?._0
                 (FStar.List.Tot.index cee (SZ.v iv)))
              (RV.list_drop (SZ.v iv + 1) cee);
            RV.lemma_alpn_first_name_index0
              (GEEE.Extension_data_application_layer_protocol_negotiation?._0
                 (FStar.List.Tot.index cee (SZ.v iv)));
            alpn_len := name_len;
            found := true;
        } else {
            RV.lemma_list_drop_index cee (SZ.v iv);
            RV.lemma_synth_ee_cons_non_alpn
              (FStar.List.Tot.index cee (SZ.v iv))
              (RV.list_drop (SZ.v iv + 1) cee);
            Trade.elim
              (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                               GEEE.extensionEncryptedExtensions_conv
                 el (FStar.List.Tot.index cee (SZ.v iv)))
              (SM.seq_list_match s cee
                 (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                  GEEE.extensionEncryptedExtensions_conv));
            SZ.fits_lte (SZ.v iv + 1) (SZ.v count);
            i := iv `SZ.add` 1sz;
        }
      };
      let fnd = !found;
      let al = !alpn_len;
      let iv = !i;
      RV.lemma_list_drop_length cee;
      RV.lemma_synth_ee_nil ();
      assert (pure ((not fnd) ==> SZ.v iv == FStar.List.Tot.length cee));
      assert (pure ((not fnd) ==>
                    RV.list_drop (SZ.v iv) cee == RV.list_drop (FStar.List.Tot.length cee) cee));
      assert (pure ((not fnd) ==>
                    RV.reveal_synth_encrypted_extensions cee ==
                    Some ({ M.negotiated_alpn = None; M.body = B.empty })));
      assert (pure (Some? (RV.reveal_synth_encrypted_extensions cee)));
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) (Some nv) cee);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) (Some nv) cee)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                 GEEE.extensionEncryptedExtensions_conv) xee cee);
      (alpn_vec, al, fnd)
    }
  }
}

(* Byte-level handshake fallbacks (key_update / ignored-post-handshake).  These
   are the spec-defined formats *outside* the QuackyDucky handshake grammar that
   [parse_tls_message] routes a Handshake record through when [parse_handshake]
   fails (validator failure, or a parsed handshake value whose synth is None,
   e.g. key_update / new_session_ticket).  We mirror the spec functions exactly,
   reading only the few fixed envelope bytes, bridged by Reveal lemmas. *)
fn handshake_fallback
  (content_type: U8.t)
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\ content_type == 0x16uy /\
                 SZ.v input_len <= L.max_record_fragment_len /\
                 WS.parse_handshake (Ghost.reveal 'input_bytes) == None)
  returns r: option L.tls_message
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             (exists* m.
               L.is_valid_tls_message l m **
               pure (CT.parsed_message_wire_success_for
                 content_type (Ghost.reveal 'input_bytes) l m)) **
             pure (exists ct m.
               L.content_type_matches content_type ct /\
               WS.parse_tls_message ct 'input_bytes == Some m) **
             pure (CT.parsed_message_wire_success
               content_type (Ghost.reveal 'input_bytes) l)
           | None ->
             pure (forall (ct:T.content_type).
               L.content_type_matches content_type ct ==>
               WS.parse_tls_message ct 'input_bytes == None))
{
  Arr.pts_to_len input;
  RV.lemma_ptm_handshake_fallback (Ghost.reveal 'input_bytes);
  RV.lemma_parse_key_update_def (Ghost.reveal 'input_bytes);
  RV.lemma_parse_ignored_post_handshake_def (Ghost.reveal 'input_bytes);
  if (SZ.lte 4sz input_len) {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let b2 = input.(2sz);
    let b3 = input.(3sz);
    if (input_len = 5sz && b0 = 24uy && b1 = 0uy && b2 = 0uy && b3 = 1uy) {
      let b4 = input.(4sz);
      if (b4 = 0uy || b4 = 1uy) {
        let req = (if b4 = 0uy then M.UpdateNotRequested else M.UpdateRequested);
        intro_is_valid_key_update b4 req;
        lemma_wire_exists content_type T.Handshake (M.TlsKeyUpdate req) 'input_bytes;
        Some (L.LTlsKeyUpdate b4)
      } else {
        (* key_update prefix but invalid request byte: both fallbacks None. *)
        None #L.tls_message
      }
    } else {
      (* not a key_update envelope: parse_key_update is None.  Try ignored. *)
      let body_len_sz = input_len `SZ.sub` 4sz;
      let body_small = (u8_to_sz b2 `SZ.mul` 256sz) `SZ.add` (u8_to_sz b3);
      assert (pure (SZ.v body_small == U8.v b2 * 256 + U8.v b3));
      assert (pure (SZ.v body_len_sz == SZ.v input_len - 4));
      let sizes_eq = SZ.eq body_small body_len_sz;
      if (b0 = 4uy && b1 = 0uy && sizes_eq) {
        assert (pure (SZ.v body_small == SZ.v body_len_sz));
        assert (pure ((U8.v b1 * 65536 + U8.v b2 * 256 + U8.v b3) + 4 == SZ.v input_len));
        let buf = alloc_copy_suffix input 4sz input_len 16640sz;
        let lignored = ({ L.application_data_bytes = buf;
                          L.application_data_len = body_len_sz });
        with dst_bytes. assert (V.pts_to buf dst_bytes);
        rewrite (V.pts_to buf dst_bytes)
             as (V.pts_to lignored.L.application_data_bytes dst_bytes);
        fold (L.is_valid_application_data lignored
                (Seq.slice (Ghost.reveal 'input_bytes) 4 (SZ.v input_len)));
        fold (L.is_valid_tls_message (L.LTlsIgnoredPostHandshake lignored)
                (M.TlsIgnoredPostHandshake
                  (Seq.slice (Ghost.reveal 'input_bytes) 4 (SZ.v input_len))));
        lemma_wire_exists content_type T.Handshake
          (M.TlsIgnoredPostHandshake
            (Seq.slice (Ghost.reveal 'input_bytes) 4 (SZ.v input_len))) 'input_bytes;
        Some (L.LTlsIgnoredPostHandshake lignored)
      } else {
        (* neither key_update nor ignored: both fallbacks None. *)
        assert (pure (~(U8.v b0 == 4 /\
                        (U8.v b1 * 65536 + U8.v b2 * 256 + U8.v b3) + 4 == SZ.v input_len)));
        None #L.tls_message
      }
    }
  } else {
    (* length < 4: parse_key_update None (length <> 5) and ignored None. *)
    None #L.tls_message
  }
}

(* ======================================================================== *)
(* ServerHello arm helpers                                                  *)
(* ======================================================================== *)

(* Tag agreement pins the mid constructor for a [Body_server_hello_low]. *)
let lemma_sh_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
   (requires GHS.Body_server_hello_low? xl /\
             GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
   (ensures GHS.Body_server_hello_mid? vm)
  = ()

(* A [Body_server_hello_mid cm] whose handshake conv is [Some v] forces [v] to be
   the [Body_server_hello] of the (Some-) converted serverHello mid. *)
let lemma_sh_conv (cm: GSH.serverHello_mid) (v: GHS.handshake)
  : Lemma
   (requires GHS.handshake_conv (GHS.Body_server_hello_mid cm) == Some v)
   (ensures Some? (GSH.serverHello_conv cm) /\
            v == GHS.Body_server_hello (Some?.v (GSH.serverHello_conv cm)))
  = ()

(* Expose the underlying serverHello vmatch from the packed read result. *)
ghost
fn elim_vmatch_server_hello
  (xsh: GHS.handshake_body_server_hello_lowtype)
  (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_server_hello_low xsh) v
  ensures exists* (cm: GSH.serverHello_mid).
           GSH.serverHello_vmatch xsh cm **
           pure (Some? (GSH.serverHello_conv cm) /\
                 v == GHS.Body_server_hello (Some?.v (GSH.serverHello_conv cm)) /\
                 GHS.handshake_conv (GHS.Body_server_hello_mid cm) == Some v)
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
   (GHS.Body_server_hello_low xsh) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_server_hello_low xsh);
  lemma_sh_constructor (GHS.Body_server_hello_low xsh) vm;
  let cm0 = GHS.Body_server_hello_mid?._0 vm;
  rewrite (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh) vm)
      as (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh)
            (GHS.Body_server_hello_mid cm0));
  unfold (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh)
           (GHS.Body_server_hello_mid cm0));
  rewrite (GHS.handshake_body_server_hello_vmatch xsh cm0)
      as (GSH.serverHello_vmatch xsh cm0);
  lemma_sh_conv cm0 v;
}

(* Re-pack the serverHello vmatch into the handshake read result so it can be
   freed by the generated [free_handshake]. *)
ghost
fn intro_vmatch_server_hello
  (xsh: GHS.handshake_body_server_hello_lowtype)
  (cm: GSH.serverHello_mid)
  (#v: GHS.handshake)
  requires GSH.serverHello_vmatch xsh cm **
           pure (GHS.handshake_conv (GHS.Body_server_hello_mid cm) == Some v)
  ensures PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_server_hello_low xsh) v
{
  rewrite (GSH.serverHello_vmatch xsh cm)
      as (GHS.handshake_body_server_hello_vmatch xsh cm);
  fold (GHS.handshake_vmatch (GHS.Body_server_hello_low xsh)
          (GHS.Body_server_hello_mid cm));
  PPB.intro_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_server_hello_low xsh) (GHS.Body_server_hello_mid cm) v;
}

(* ---- ServerHello conv-structure facts (pure, transparent unfolding) ---- *)

(* The serverHello conv preserves the legacy_version field verbatim. *)
let lemma_sh_conv_version (cm: GSH.serverHello_mid) (cse: GSH.serverHello)
  : Lemma (requires GSH.serverHello_conv cm == Some cse)
          (ensures cse.GSH.legacy_version == fst cm)
  = ()

(* The serverHello_body ite conv: the random tag is 32 bytes, and the branch
   discriminant [dfst (snd (snd cm))] selects HelloRetryRequest (true) vs the
   normal ServerHello_body_false (false).  On the normal branch the tag equals
   the random mid and the payload conv yields [sf.value]. *)
let lemma_sh_conv_body (cm: GSH.serverHello_mid) (cse: GSH.serverHello)
  : Lemma (requires GSH.serverHello_conv cm == Some cse)
          (ensures
            Seq.length (fst (snd cm)) == 32 /\
            (dfst (snd (snd cm)) == true ==> GSHB.HelloRetryRequest? cse.GSH.body) /\
            (dfst (snd (snd cm)) == false ==>
               (GSHB.ServerHello_body_false? cse.GSH.body /\
                (GSHB.ServerHello_body_false?._0 cse.GSH.body).GSHB.tag == fst (snd cm) /\
                GSHBody.serverHelloBody_conv (dsnd (snd (snd cm))) ==
                  Some (GSHB.ServerHello_body_false?._0 cse.GSH.body).GSHB.value)))
  = ()

(* The serverHelloBody conv preserves the compression byte and extension list. *)
let lemma_shbody_conv (m: GSHBody.serverHelloBody_mid) (h: GSHBody.serverHelloBody)
  : Lemma (requires GSHBody.serverHelloBody_conv m == Some h)
          (ensures
            h.GSHBody.legacy_compression_method == fst (snd m) /\
            (h.GSHBody.extensions <: list GESH.extensionServerHello) == snd (snd m))
  = ()

(* The key_share extension conv exposes the underlying keyShareEntry verbatim:
   group equals the namedGroup mid and the key_exchange bytes equal the mid. *)
let lemma_extSH_ks_conv (cm_ks: GESH.extensionServerHello_extension_data_key_share_mid)
                        (y: GESH.extensionServerHello_extension_data_key_share)
  : Lemma (requires GESH.extensionServerHello_extension_data_key_share_conv cm_ks == Some y)
          (ensures (y <: GKSE.keyShareEntry).GKSE.group == fst cm_ks /\
                   ((y <: GKSE.keyShareEntry).GKSE.key_exchange <: B.bytes) == snd cm_ks)
  = ()

(* ---- extensionServerHello element-level navigation (mirrors extEE) ---- *)

(* Tag agreement makes the low/high supported_versions constructors coincide. *)
let lemma_extSH_sv_iff
  (xl: GESH.extensionServerHello_low) (vm: GESH.extensionServerHello_mid)
  (h: GESH.extensionServerHello)
  : Lemma
    (requires GESH.extensionServerHello_low_tag xl == GESH.extensionServerHello_mid_tag vm /\
              GESH.extensionServerHello_conv vm == Some h)
    (ensures GESH.Extension_data_supported_versions_low? xl <==>
             GESH.Extension_data_supported_versions? h)
  = ()

(* Tag agreement makes the low/high key_share constructors coincide. *)
let lemma_extSH_ks_iff
  (xl: GESH.extensionServerHello_low) (vm: GESH.extensionServerHello_mid)
  (h: GESH.extensionServerHello)
  : Lemma
    (requires GESH.extensionServerHello_low_tag xl == GESH.extensionServerHello_mid_tag vm /\
              GESH.extensionServerHello_conv vm == Some h)
    (ensures GESH.Extension_data_key_share_low? xl <==>
             GESH.Extension_data_key_share? h)
  = ()

(* Tag agreement pins the mid constructor for a supported_versions element. *)
let lemma_extSH_sv_constructor
  (xl: GESH.extensionServerHello_low) (vm: GESH.extensionServerHello_mid)
  : Lemma
    (requires GESH.Extension_data_supported_versions_low? xl /\
              GESH.extensionServerHello_low_tag xl == GESH.extensionServerHello_mid_tag vm)
    (ensures GESH.Extension_data_supported_versions_mid? vm)
  = ()

(* Tag agreement pins the mid constructor for a key_share element. *)
let lemma_extSH_ks_constructor
  (xl: GESH.extensionServerHello_low) (vm: GESH.extensionServerHello_mid)
  : Lemma
    (requires GESH.Extension_data_key_share_low? xl /\
              GESH.extensionServerHello_low_tag xl == GESH.extensionServerHello_mid_tag vm)
    (ensures GESH.Extension_data_key_share_mid? vm)
  = ()

(* The supported_versions extension conv exposes its protocolVersion verbatim. *)
let lemma_extSH_sv_data_conv
  (cm: GESH.extensionServerHello_extension_data_supported_versions_mid)
  (h: GESH.extensionServerHello)
  : Lemma
    (requires GESH.extensionServerHello_conv (GESH.Extension_data_supported_versions_mid cm) == Some h)
    (ensures GESH.Extension_data_supported_versions? h /\
             (GESH.Extension_data_supported_versions?._0 h <: GPV.protocolVersion) == cm)
  = ()

(* The key_share extension conv exposes the underlying keyShareEntry mid. *)
let lemma_extSH_ks_data_conv
  (cm: GESH.extensionServerHello_extension_data_key_share_mid)
  (h: GESH.extensionServerHello)
  : Lemma
    (requires GESH.extensionServerHello_conv (GESH.Extension_data_key_share_mid cm) == Some h)
    (ensures GESH.Extension_data_key_share? h /\
             GESH.extensionServerHello_extension_data_key_share_conv cm ==
               Some (GESH.Extension_data_key_share?._0 h))
  = ()

(* Recover the tag-agreement fact buried in an element's vmatch. *)
ghost
fn peek_extSH_tag (xl: GESH.extensionServerHello_low)
               (#vm: GESH.extensionServerHello_mid)
  requires GESH.extensionServerHello_vmatch xl vm
  ensures GESH.extensionServerHello_vmatch xl vm **
          pure (GESH.extensionServerHello_low_tag xl ==
                GESH.extensionServerHello_mid_tag vm)
{
  unfold (GESH.extensionServerHello_vmatch xl vm);
  fold (GESH.extensionServerHello_vmatch xl vm);
}

(* Expose, without consuming the resource, whether the high element is a
   supported_versions / key_share extension (matching the runtime low tag). *)
ghost
fn elim_extSH_iffs (elem: GESH.extensionServerHello_low)
                   (#h: GESH.extensionServerHello)
  requires PPB.vmatch_conv GESH.extensionServerHello_vmatch
             GESH.extensionServerHello_conv elem h
  ensures PPB.vmatch_conv GESH.extensionServerHello_vmatch
            GESH.extensionServerHello_conv elem h **
          pure ((GESH.Extension_data_supported_versions_low? elem <==>
                 GESH.Extension_data_supported_versions? h) /\
                (GESH.Extension_data_key_share_low? elem <==>
                 GESH.Extension_data_key_share? h))
{
  PPB.elim_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv elem h;
  with vm. assert (GESH.extensionServerHello_vmatch elem vm **
                   pure (GESH.extensionServerHello_conv vm == Some h));
  peek_extSH_tag elem;
  lemma_extSH_sv_iff elem vm h;
  lemma_extSH_ks_iff elem vm h;
  PPB.intro_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv elem vm h;
}

(* Given a supported_versions element, expose its protocolVersion value (equal to
   the low value carried by the runtime constructor). *)
ghost
fn elim_extSH_sv (v: GSV.supportedVersionsServerHello_lowtype)
                 (elem: GESH.extensionServerHello_low)
                 (#h: GESH.extensionServerHello)
  requires PPB.vmatch_conv GESH.extensionServerHello_vmatch
             GESH.extensionServerHello_conv elem h **
           pure (elem == GESH.Extension_data_supported_versions_low v)
  ensures PPB.vmatch_conv GESH.extensionServerHello_vmatch
            GESH.extensionServerHello_conv elem h **
          pure (GESH.Extension_data_supported_versions? h /\
                (GESH.Extension_data_supported_versions?._0 h <: GPV.protocolVersion) == v)
{
  PPB.elim_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv elem h;
  with vm. assert (GESH.extensionServerHello_vmatch elem vm **
                   pure (GESH.extensionServerHello_conv vm == Some h));
  peek_extSH_tag elem;
  lemma_extSH_sv_constructor elem vm;
  let cm0 = GESH.Extension_data_supported_versions_mid?._0 vm;
  rewrite (GESH.extensionServerHello_vmatch elem vm)
      as (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_supported_versions_low v)
            (GESH.Extension_data_supported_versions_mid cm0));
  unfold (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_supported_versions_low v)
            (GESH.Extension_data_supported_versions_mid cm0));
  rewrite (GESH.extensionServerHello_extension_data_supported_versions_vmatch v cm0)
      as (LPS.eq_as_slprop GPV.protocolVersion v cm0);
  unfold (LPS.eq_as_slprop GPV.protocolVersion v cm0);
  fold (LPS.eq_as_slprop GPV.protocolVersion v cm0);
  rewrite (LPS.eq_as_slprop GPV.protocolVersion v cm0)
      as (GESH.extensionServerHello_extension_data_supported_versions_vmatch v cm0);
  fold (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_supported_versions_low v)
            (GESH.Extension_data_supported_versions_mid cm0));
  rewrite (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_supported_versions_low v)
            (GESH.Extension_data_supported_versions_mid cm0))
      as (GESH.extensionServerHello_vmatch elem vm);
  lemma_extSH_sv_data_conv cm0 h;
  PPB.intro_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv elem vm h;
}

(* Eliminate a key_share element's vmatch down to the keyShareEntry vmatch_pair. *)
ghost
fn elim_vmatch_extSH_key_share
  (v0: GESH.extensionServerHello_extension_data_key_share_lowtype)
  (elem: GESH.extensionServerHello_low)
  (#h: GESH.extensionServerHello)
  requires PPB.vmatch_conv GESH.extensionServerHello_vmatch
             GESH.extensionServerHello_conv elem h **
           pure (elem == GESH.Extension_data_key_share_low v0)
  ensures exists* (cm: GESH.extensionServerHello_extension_data_key_share_mid).
           GKSE.keyShareEntry_vmatch v0 cm **
           pure (GESH.Extension_data_key_share? h /\
                 GESH.extensionServerHello_extension_data_key_share_conv cm ==
                   Some (GESH.Extension_data_key_share?._0 h) /\
                 GESH.extensionServerHello_conv
                   (GESH.Extension_data_key_share_mid cm) == Some h)
{
  PPB.elim_vmatch_conv GESH.extensionServerHello_vmatch
    GESH.extensionServerHello_conv elem h;
  with vm. assert (GESH.extensionServerHello_vmatch elem vm **
                   pure (GESH.extensionServerHello_conv vm == Some h));
  peek_extSH_tag elem;
  lemma_extSH_ks_constructor elem vm;
  let cm0 = GESH.Extension_data_key_share_mid?._0 vm;
  rewrite (GESH.extensionServerHello_vmatch elem vm)
      as (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_key_share_low v0)
            (GESH.Extension_data_key_share_mid cm0));
  unfold (GESH.extensionServerHello_vmatch
            (GESH.Extension_data_key_share_low v0)
            (GESH.Extension_data_key_share_mid cm0));
  rewrite (GESH.extensionServerHello_extension_data_key_share_vmatch v0 cm0)
      as (GKSE.keyShareEntry_vmatch v0 cm0);
  lemma_extSH_ks_data_conv cm0 h;
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

(* Expose the protocolVersion (legacy_version) equality, the random tag lvec, and
   the ite payload of the serverHello read result. *)
ghost
fn elim_serverHello_body (xsh: GSH.serverHello_lowtype) (#cm: GSH.serverHello_mid)
  requires GSH.serverHello_vmatch xsh cm
  ensures
    LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)) **
    LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
      (snd (snd xsh)) (snd (snd cm)) **
    pure (fst xsh == fst cm /\
          (match GSHB.serverHello_body_random_conv (fst (snd cm)) with
           | Some t -> GSHB.serverHello_body_cond t == dfst (snd (snd cm))
           | None -> True))
{
  rewrite (GSH.serverHello_vmatch xsh cm)
      as (LPC.vmatch_pair GPV.protocolVersion_vmatch GSHB.serverHello_body_vmatch xsh cm);
  unfold (LPC.vmatch_pair GPV.protocolVersion_vmatch GSHB.serverHello_body_vmatch xsh cm);
  rewrite (GPV.protocolVersion_vmatch (fst xsh) (fst cm))
      as (LPS.eq_as_slprop GPV.protocolVersion (fst xsh) (fst cm));
  unfold (LPS.eq_as_slprop GPV.protocolVersion (fst xsh) (fst cm));
  rewrite (GSHB.serverHello_body_vmatch (snd xsh) (snd cm))
      as (LPITE.vmatch_ite GSHB.serverHello_body_random_vmatch GSHB.serverHello_body_cond
            GSHB.serverHello_body_random_conv GSHB.serverHello_body_payload_vmatch
            (snd xsh) (snd cm));
  unfold (LPITE.vmatch_ite GSHB.serverHello_body_random_vmatch GSHB.serverHello_body_cond
            GSHB.serverHello_body_random_conv GSHB.serverHello_body_payload_vmatch
            (snd xsh) (snd cm));
  rewrite (GSHB.serverHello_body_random_vmatch (fst (snd xsh)) (fst (snd cm)))
      as (LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)));
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

(* Decompose the serverHelloBody read result into the session-id-echo lvec, the
   extensions vclist, and the (pure) cipher_suite and compression equalities. *)
ghost
fn elim_serverHelloBody (shl: GSHBody.serverHelloBody_lowtype)
                        (#shm: GSHBody.serverHelloBody_mid)
  requires GSHBody.serverHelloBody_vmatch shl shm
  ensures
    GSHBody.serverHelloBody_legacy_session_id_echo_vmatch (fst (fst shl)) (fst (fst shm)) **
    PPVCL.vmatch_vclist
      (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
      (snd (snd shl)) (snd (snd shm)) **
    pure (snd (fst shl) == snd (fst shm) /\ fst (snd shl) == fst (snd shm))
{
  rewrite (GSHBody.serverHelloBody_vmatch shl shm)
      as (LPC.vmatch_pair
            (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch)
            (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch)
            shl shm);
  unfold (LPC.vmatch_pair
            (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch)
            (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch)
            shl shm);
  unfold (LPC.vmatch_pair GSHBody.serverHelloBody_legacy_session_id_echo_vmatch GCS.cipherSuite_vmatch
            (fst shl) (fst shm));
  rewrite (GCS.cipherSuite_vmatch (snd (fst shl)) (snd (fst shm)))
      as (LPS.eq_as_slprop GCS.cipherSuite (snd (fst shl)) (snd (fst shm)));
  unfold (LPS.eq_as_slprop GCS.cipherSuite (snd (fst shl)) (snd (fst shm)));
  unfold (LPC.vmatch_pair (LPS.eq_as_slprop U8.t) GSHBody.serverHelloBody_extensions_vmatch
            (snd shl) (snd shm));
  unfold (LPS.eq_as_slprop U8.t (fst (snd shl)) (fst (snd shm)));
  rewrite (GSHBody.serverHelloBody_extensions_vmatch (snd (snd shl)) (snd (snd shm)))
      as (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
            (snd (snd shl)) (snd (snd shm)));
}

(* Re-pack the session-id-echo lvec and extensions vclist into the serverHelloBody
   read result so it can be freed by the generated [free_serverHelloBody]. *)
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

(* Reshape the serverHello_body ite payload (given the concrete branch
   discriminant [b] read from the low value) into the underlying
   [serverHelloBody_vmatch] (the payload is a [serverHelloBody] on BOTH the HRR
   and the normal branch; only the random tag distinguishes them). *)
ghost
fn elim_sh_ite_payload (xsh: GSH.serverHello_lowtype) (b: bool) (#cm: GSH.serverHello_mid)
  requires LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (snd (snd xsh)) (snd (snd cm)) **
           pure (b == dfst (snd (snd xsh)))
  ensures GSHBody.serverHelloBody_vmatch (dsnd (snd (snd xsh))) (dsnd (snd (snd cm))) **
          pure (b == dfst (snd (snd cm)))
{
  rewrite (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (snd (snd xsh)) (snd (snd cm)))
      as (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (| b, dsnd (snd (snd xsh)) |) (snd (snd cm)));
  LPITE.vmatch_ite_payload_branch_eq GSHB.serverHello_body_payload_vmatch
    b (dsnd (snd (snd xsh))) (snd (snd cm));
  rewrite (LPITE.vmatch_ite_payload GSHB.serverHello_body_payload_vmatch
             (| b, dsnd (snd (snd xsh)) |) (snd (snd cm)))
      as (GSHBody.serverHelloBody_vmatch (dsnd (snd (snd xsh))) (dsnd (snd (snd cm))));
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

(* Inspect a keyShareEntry: if it is an X25519 entry with a 32-byte key, copy the
   32 key bytes into [key_vec] and return true; otherwise leave [key_vec]
   unchanged and return false.  Mirrors the spec test
   [X25519? group && key_exchange_to_key32 = Some _] used by [sh_key_share]. *)
fn try_copy_x25519_key
  (key_vec: V.vec U8.t)
  (v0: GKSE.keyShareEntry_lowtype)
  (#cm: Ghost.erased GKSE.keyShareEntry_mid)
  requires V.pts_to key_vec 'kv ** GKSE.keyShareEntry_vmatch v0 cm **
           pure (V.is_full_vec key_vec /\ V.length key_vec == 32)
  returns ok: bool
  ensures GKSE.keyShareEntry_vmatch v0 cm **
          (exists* kbytes. V.pts_to key_vec kbytes **
            pure (V.is_full_vec key_vec /\ V.length key_vec == 32 /\
                  Seq.length kbytes == 32 /\
                  (ok <==> (GNG.X25519? (fst (Ghost.reveal cm)) /\
                            Seq.length (snd (Ghost.reveal cm)) == 32)) /\
                  (ok ==> Seq.equal kbytes (snd (Ghost.reveal cm))) /\
                  ((not ok) ==> Seq.equal kbytes (Ghost.reveal 'kv))))
{
  V.pts_to_len key_vec;
  rewrite (GKSE.keyShareEntry_vmatch v0 cm)
      as (LPC.vmatch_pair GNG.namedGroup_vmatch GKSE.keyShareEntry_key_exchange_vmatch v0 cm);
  unfold (LPC.vmatch_pair GNG.namedGroup_vmatch GKSE.keyShareEntry_key_exchange_vmatch v0 cm);
  rewrite (GNG.namedGroup_vmatch (fst v0) (fst cm))
      as (LPS.eq_as_slprop GNG.namedGroup (fst v0) (fst cm));
  unfold (LPS.eq_as_slprop GNG.namedGroup (fst v0) (fst cm));
  rewrite (GKSE.keyShareEntry_key_exchange_vmatch (snd v0) (snd cm))
      as (LSeqB.vmatch_copy_seqbytes (snd v0) (snd cm));
  unfold (LSeqB.vmatch_copy_seqbytes (snd v0) (snd cm));
  V.pts_to_len (snd v0).PPBY.lvec_vec;
  let group_lo = fst v0;
  let key_len = (snd v0).PPBY.lvec_len;
  let is_x = GNG.X25519? group_lo;
  let len_ok = SZ.eq key_len 32sz;
  if (is_x && len_ok) {
    copy_vec_32_into key_vec (snd v0).PPBY.lvec_vec;
    repack_kse v0;
    true
  } else {
    repack_kse v0;
    false
  }
}

(* Scan the ServerHello extension list for the x25519 key_share, mirroring the
   spec [sh_key_share ext false None].  Tracks a [saw_supported_versions] flag and
   a copied 32-byte key in [key_vec].  Returns [(key_vec, found)] where [found]
   reflects whether the scan yields [Some key] (i.e. a TLS_1p3 supported_versions
   AND an x25519/32-byte key_share, with no rejecting extension in between). *)
fn scan_sh_key_share
  (ext_lo: GSHBody.serverHelloBody_extensions_lowtype)
  (#cext: Ghost.erased (list GESH.extensionServerHello))
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
             ext_lo cext
  returns res: (V.vec U8.t & bool)
  ensures PPVCL.vmatch_vclist
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
            ext_lo cext **
          (exists* kbytes. V.pts_to (fst res) kbytes **
            pure (V.is_full_vec (fst res) /\ V.length (fst res) == 32 /\
                  Seq.length kbytes == 32 /\
                  (match RV.reveal_sh_key_share cext false None with
                   | Some k -> (snd res) == true /\ Seq.equal kbytes (Ghost.reveal k <: Seq.seq U8.t)
                   | None -> (snd res) == false)))
{
  let key_vec = V.alloc 0uy 32sz;
  match ext_lo {
    None -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                None cext);
      RV.lemma_sh_key_share_nil false None;
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                None cext);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                None cext)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                ext_lo cext);
      (key_vec, false)
    }
    Some nv -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                (Some nv) cext);
      with s. assert (V.pts_to (snd nv) s **
                      SM.seq_list_match s cext
                        (PPB.vmatch_conv GESH.extensionServerHello_vmatch
                                         GESH.extensionServerHello_conv));
      V.pts_to_len (snd nv);
      let count = fst nv;
      let mut i = 0sz;
      let mut failed = false;
      let mut saw_sv = false;
      let mut have_key = false;
      let kacc_ref = GR.alloc (None #(B.bytes_of_len 32));
      while (
        let f = !failed;
        let iv = !i;
        (not f) && (iv `SZ.lt` count)
      )
      invariant exists* iv fl svb hkb kacc kbytes.
        R.pts_to i iv **
        R.pts_to failed fl **
        R.pts_to saw_sv svb **
        R.pts_to have_key hkb **
        GR.pts_to kacc_ref kacc **
        V.pts_to (snd nv) s **
        SM.seq_list_match s cext
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv) **
        V.pts_to key_vec kbytes **
        pure (
          SZ.v iv <= SZ.v count /\
          SZ.v count == FStar.List.Tot.length cext /\
          Seq.length s == FStar.List.Tot.length cext /\
          V.is_full_vec (snd nv) /\
          V.is_full_vec key_vec /\ V.length key_vec == 32 /\ Seq.length kbytes == 32 /\
          (hkb <==> Some? kacc) /\
          (Some? kacc ==> Seq.equal kbytes (Ghost.reveal (Some?.v kacc) <: Seq.seq U8.t)) /\
          (fl ==> RV.reveal_sh_key_share cext false None == None) /\
          ((not fl) ==>
            RV.reveal_sh_key_share cext false None ==
            RV.reveal_sh_key_share (RV.list_drop (SZ.v iv) cext) svb kacc)
        )
      {
        let iv = !i;
        assert (pure (SZ.v iv < FStar.List.Tot.length cext));
        let el = V.op_Array_Access (snd nv) iv;
        SMU.seq_list_match_index_trade
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
          s cext (SZ.v iv);
        Trade.rewrite_with_trade
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cext (SZ.v iv)))
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             el (FStar.List.Tot.index cext (SZ.v iv)));
        Trade.trans
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             el (FStar.List.Tot.index cext (SZ.v iv)))
          (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cext (SZ.v iv)))
          (SM.seq_list_match s cext
             (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
        elim_extSH_iffs el;
        let svb0 = !saw_sv;
        let kacc_g = GR.read kacc_ref;
        RV.lemma_list_drop_index cext (SZ.v iv);
        RV.lemma_sh_key_share_cons
          (FStar.List.Tot.index cext (SZ.v iv))
          (RV.list_drop (SZ.v iv + 1) cext)
          svb0 (Ghost.reveal kacc_g);
        if (GESH.Extension_data_supported_versions_low? el) {
          let v = GESH.Extension_data_supported_versions_low?._0 el;
          elim_extSH_sv v el;
          Trade.elim
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
               el (FStar.List.Tot.index cext (SZ.v iv)))
            (SM.seq_list_match s cext
               (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
          if (GPV.TLS_1p3? v) {
            saw_sv := true;
            SZ.fits_lte (SZ.v iv + 1) (SZ.v count);
            i := iv `SZ.add` 1sz;
          } else {
            failed := true;
          }
        } else if (GESH.Extension_data_key_share_low? el) {
          let v0 = GESH.Extension_data_key_share_low?._0 el;
          elim_vmatch_extSH_key_share v0 el #(FStar.List.Tot.index cext (SZ.v iv));
          with cm_ks. assert (GKSE.keyShareEntry_vmatch v0 cm_ks);
          lemma_extSH_ks_conv cm_ks
            (GESH.Extension_data_key_share?._0 (FStar.List.Tot.index cext (SZ.v iv)));
          RV.lemma_reveal_key_exchange_to_key32
            ((GESH.Extension_data_key_share?._0 (FStar.List.Tot.index cext (SZ.v iv))
                <: GKSE.keyShareEntry).GKSE.key_exchange);
          let ok = try_copy_x25519_key key_vec v0 #cm_ks;
          intro_vmatch_extSH_key_share v0 cm_ks #(FStar.List.Tot.index cext (SZ.v iv));
          rewrite (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
                     (GESH.Extension_data_key_share_low v0) (FStar.List.Tot.index cext (SZ.v iv)))
              as (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
                     el (FStar.List.Tot.index cext (SZ.v iv)));
          Trade.elim
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
               el (FStar.List.Tot.index cext (SZ.v iv)))
            (SM.seq_list_match s cext
               (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
          if ok {
            GR.write kacc_ref
              (Ghost.hide (RV.reveal_key_exchange_to_key32
                ((GESH.Extension_data_key_share?._0 (FStar.List.Tot.index cext (SZ.v iv))
                    <: GKSE.keyShareEntry).GKSE.key_exchange)));
            have_key := true;
            SZ.fits_lte (SZ.v iv + 1) (SZ.v count);
            i := iv `SZ.add` 1sz;
          } else {
            failed := true;
          }
        } else {
          Trade.elim
            (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv
               el (FStar.List.Tot.index cext (SZ.v iv)))
            (SM.seq_list_match s cext
               (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv));
          SZ.fits_lte (SZ.v iv + 1) (SZ.v count);
          i := iv `SZ.add` 1sz;
        }
      };
      let fl = !failed;
      let svb0 = !saw_sv;
      let hkb0 = !have_key;
      let iv = !i;
      RV.lemma_list_drop_length cext;
      let kacc_final = GR.read kacc_ref;
      RV.lemma_sh_key_share_nil svb0 (Ghost.reveal kacc_final);
      assert (pure ((not fl) ==> SZ.v iv == FStar.List.Tot.length cext));
      let found = (not fl) && svb0 && hkb0;
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                (Some nv) cext);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                (Some nv) cext)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GESH.extensionServerHello_vmatch GESH.extensionServerHello_conv)
                ext_lo cext);
      GR.free kacc_ref;
      (key_vec, found)
    }
  }
}

(* --- Certificate: eliminate / re-introduce the packed vmatch --------------- *)

(* Tag agreement pins the mid constructor for a [Body_certificate_low]. *)
let lemma_cert_constructor (xl: GHS.handshake_low) (vm: GHS.handshake_mid)
  : Lemma
   (requires GHS.Body_certificate_low? xl /\
             GHS.handshake_low_tag xl == GHS.handshake_mid_tag vm)
   (ensures GHS.Body_certificate_mid? vm)
  = ()

(* A [Body_certificate_mid cm] whose conv is [Some v] forces [v] to be a
   [Body_certificate] whose high-level certificate_list is the (refined) mid list
   [snd cm]. *)
let lemma_cert_conv (cm: GHS.handshake_body_certificate_mid) (v: GHS.handshake)
  : Lemma
   (requires GHS.handshake_conv (GHS.Body_certificate_mid cm) == Some v)
   (ensures GHS.Body_certificate? v /\
            ((GHS.Body_certificate?._0 v).GCert.certificate_list <: list GCE.certificateEntry)
              == (snd cm <: list GCE.certificateEntry))
  = ()

(* A [certificateEntry_conv em == Some h] forces [h.cert_data] to be the mid
   cert_data seq [fst em], whose length fits the DER bounds. *)
let lemma_certEntry_conv (em: GCE.certificateEntry_mid) (h: GCE.certificateEntry)
  : Lemma
   (requires GCE.certificateEntry_conv em == Some h)
   (ensures (h.GCE.cert_data <: Seq.seq U8.t) == (fst em <: Seq.seq U8.t) /\
            1 <= Seq.length (fst em <: Seq.seq U8.t) /\
            Seq.length (fst em <: Seq.seq U8.t) <= 16777215)
  = ()

(* Expose the underlying request-context lvec and certificate-list vclist from the
   packed Certificate read result. *)
ghost
fn elim_vmatch_certificate
  (xcert: GHS.handshake_body_certificate_lowtype)
  (#v: GHS.handshake)
  requires PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_certificate_low xcert) v
  ensures exists* (cm: GHS.handshake_body_certificate_mid).
           LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm) **
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
             (snd xcert) (snd cm) **
           pure (GHS.handshake_conv (GHS.Body_certificate_mid cm) == Some v /\
                 GHS.Body_certificate? v /\
                 ((GHS.Body_certificate?._0 v).GCert.certificate_list <: list GCE.certificateEntry)
                   == (snd cm <: list GCE.certificateEntry))
{
  PPB.elim_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
   (GHS.Body_certificate_low xcert) v;
  with vm. assert (GHS.handshake_vmatch (GHS.Body_certificate_low xcert) vm **
                   pure (GHS.handshake_conv vm == Some v));
  peek_handshake_tag (GHS.Body_certificate_low xcert);
  lemma_cert_constructor (GHS.Body_certificate_low xcert) vm;
  let cm0 = GHS.Body_certificate_mid?._0 vm;
  rewrite (GHS.handshake_vmatch (GHS.Body_certificate_low xcert) vm)
      as (GHS.handshake_vmatch (GHS.Body_certificate_low xcert)
            (GHS.Body_certificate_mid cm0));
  unfold (GHS.handshake_vmatch (GHS.Body_certificate_low xcert)
           (GHS.Body_certificate_mid cm0));
  rewrite (GHS.handshake_body_certificate_vmatch xcert cm0)
      as (LPC.vmatch_pair GCert.certificate_certificate_request_context_vmatch
            GCert.certificate_certificate_list_vmatch xcert cm0);
  unfold (LPC.vmatch_pair GCert.certificate_certificate_request_context_vmatch
            GCert.certificate_certificate_list_vmatch xcert cm0);
  rewrite (GCert.certificate_certificate_request_context_vmatch (fst xcert) (fst cm0))
      as (LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm0));
  rewrite (GCert.certificate_certificate_list_vmatch (snd xcert) (snd cm0))
      as (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
            (snd xcert) (snd cm0));
  lemma_cert_conv cm0 v;
}

(* Re-pack the request-context lvec and certificate-list vclist back into the
   handshake read result so it can be freed by the generated [free_handshake]. *)
ghost
fn intro_vmatch_certificate
  (xcert: GHS.handshake_body_certificate_lowtype)
  (cm: GHS.handshake_body_certificate_mid)
  (#v: GHS.handshake)
  requires LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm) **
           PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
             (snd xcert) (snd cm) **
           pure (GHS.handshake_conv (GHS.Body_certificate_mid cm) == Some v)
  ensures PPB.vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            (GHS.Body_certificate_low xcert) v
{
  rewrite (PPVCL.vmatch_vclist
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
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
  PPB.intro_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
    (GHS.Body_certificate_low xcert) (GHS.Body_certificate_mid cm) v;
}

(* Copy the prefix [src[0..src_len)] of a (full) source Vec into the sub-region
   [dst[off..off+src_len)] of an existing 32768-byte (full) destination Vec,
   preserving the already-written prefix [dst[0..off)].  Used by the Certificate
   chain copy loop to lay out each cert's DER blob at the running offset. *)
inline_for_extraction
fn copy_vec_into_at
  (dst: V.vec U8.t)
  (off: SZ.t)
  (src: V.vec U8.t)
  (src_len: SZ.t)
  requires V.pts_to dst 'dst_bytes ** V.pts_to src 'src_bytes **
           pure (V.is_full_vec dst /\ V.length dst == 32768 /\
                 V.is_full_vec src /\ V.length src == SZ.v src_len /\
                 SZ.v off + SZ.v src_len <= 32768)
  ensures V.pts_to src 'src_bytes **
          (exists* dst_bytes2.
            V.pts_to dst dst_bytes2 **
            pure (V.is_full_vec dst /\ V.length dst == 32768 /\
                  SZ.v off + SZ.v src_len <= 32768 /\
                  Seq.length dst_bytes2 == 32768 /\
                  Seq.length (Ghost.reveal 'dst_bytes) == 32768 /\
                  Seq.equal (Seq.slice dst_bytes2 0 (SZ.v off))
                            (Seq.slice (Ghost.reveal 'dst_bytes) 0 (SZ.v off)) /\
                  Seq.equal (Seq.slice dst_bytes2 (SZ.v off) (SZ.v off + SZ.v src_len))
                            (Ghost.reveal 'src_bytes)))
{
  V.pts_to_len src;
  V.pts_to_len dst;
  V.to_array_pts_to dst;
  V.to_array_pts_to src;
  let src_slice = S.from_array (V.vec_to_array src) src_len;
  let dst_slice = S.from_array (V.vec_to_array dst) 32768sz;
  let sp1 = S.split dst_slice off;
  S.pts_to_len (snd sp1);
  let sp2 = S.split (snd sp1) src_len;
  S.pts_to_len src_slice;
  S.pts_to_len (fst sp2);
  S.copy (fst sp2) src_slice;
  S.to_array src_slice;
  V.to_vec_pts_to src;
  S.join (fst sp2) (snd sp2) (snd sp1);
  S.join (fst sp1) (snd sp1) dst_slice;
  S.to_array dst_slice;
  V.to_vec_pts_to dst;
  with copied. assert (V.pts_to dst copied);
  Seq.lemma_len_slice (Ghost.reveal 'dst_bytes) 0 (SZ.v off);
  Seq.lemma_len_slice copied 0 (SZ.v off);
  Seq.lemma_len_slice copied (SZ.v off) (SZ.v off + SZ.v src_len);
}

(* --- Certificate: navigate one certificateEntry --------------------------- *)

(* Decompose a certificateEntry read result into its cert_data lvec (the DER
   blob) and its (ignored) extensions vclist. *)
ghost
fn elim_cert_entry (el: GCE.certificateEntry_lowtype) (#em: GCE.certificateEntry_mid)
  requires GCE.certificateEntry_vmatch el em
  ensures LSeqB.vmatch_copy_seqbytes (fst el) (fst em) **
          GCE.certificateEntry_extensions_vmatch (snd el) (snd em)
{
  rewrite (GCE.certificateEntry_vmatch el em)
      as (LPC.vmatch_pair GCE.certificateEntry_cert_data_vmatch
            GCE.certificateEntry_extensions_vmatch el em);
  unfold (LPC.vmatch_pair GCE.certificateEntry_cert_data_vmatch
            GCE.certificateEntry_extensions_vmatch el em);
  rewrite (GCE.certificateEntry_cert_data_vmatch (fst el) (fst em))
      as (LSeqB.vmatch_copy_seqbytes (fst el) (fst em));
}

(* Re-pack a certificateEntry's cert_data lvec and extensions vclist into the
   read result so it can be freed by the generated [free_handshake]. *)
ghost
fn intro_cert_entry (el: GCE.certificateEntry_lowtype) (#em: GCE.certificateEntry_mid)
  requires LSeqB.vmatch_copy_seqbytes (fst el) (fst em) **
           GCE.certificateEntry_extensions_vmatch (snd el) (snd em)
  ensures GCE.certificateEntry_vmatch el em
{
  rewrite (LSeqB.vmatch_copy_seqbytes (fst el) (fst em))
      as (GCE.certificateEntry_cert_data_vmatch (fst el) (fst em));
  fold (LPC.vmatch_pair GCE.certificateEntry_cert_data_vmatch
          GCE.certificateEntry_extensions_vmatch el em);
  rewrite (LPC.vmatch_pair GCE.certificateEntry_cert_data_vmatch
            GCE.certificateEntry_extensions_vmatch el em)
      as (GCE.certificateEntry_vmatch el em);
}

(* Pure case-analysis lemma for the chain-doesn't-fit path: from "either the
   running entry count already reached 8, or the running byte total plus this
   blob exceeds 32768" derive that the full synthesised chain violates the
   fixed-size bound — exactly the [None] condition of [synth_handshake_msg_of]. *)
let lemma_cert_chain_nofit
  (cm: list GCE.certificateEntry)
  (iv cntv offv cert_len: nat)
  (processed: list B.bytes)
  : Lemma
    (requires (
       cntv == iv /\ cntv <= 8 /\ iv < FStar.List.Tot.length cm /\
       RV.reveal_cert_chain_total_bytes processed == offv /\
       FStar.List.Tot.append processed
         (RV.reveal_synth_cert_chain (RV.list_drop iv cm))
         == RV.reveal_synth_cert_chain cm /\
       cert_len == B.length ((FStar.List.Tot.index cm iv).GCE.cert_data <: B.bytes) /\
       (cntv >= 8 \/ offv + cert_len > 32768)))
    (ensures (
       FStar.List.Tot.length (RV.reveal_synth_cert_chain cm) > 8 \/
       RV.reveal_cert_chain_total_bytes (RV.reveal_synth_cert_chain cm) > 32768))
  = RV.lemma_synth_cert_chain_length cm;
    RV.lemma_list_drop_index cm iv;
    RV.lemma_synth_cert_chain_cons (FStar.List.Tot.index cm iv) (RV.list_drop (iv + 1) cm);
    RV.lemma_cert_chain_total_bytes_prefix_le processed
      ((FStar.List.Tot.index cm iv).GCE.cert_data <: B.bytes)
      (RV.reveal_synth_cert_chain (RV.list_drop (iv + 1) cm))

(* Walk the certificate_list vclist, copying each entry's DER blob into a fresh
   fixed-size [max_certificate_chain_bytes]=32768 chain buffer and recording the
   running [(offset, length)] pairs in fresh [max_certificate_chain_entries]=8
   Vecs.  Returns [(chain_bytes, offsets, lens, chain_bytes_len, count, failed)].
   On the [failed] path the chain does not fit the fixed-size representation (too
   many entries or too many bytes) — soundly mirroring the Decision-1 [None] of
   [synth_handshake_msg_of].  Otherwise [certificate_chain_matches] holds for the
   synthesised chain. *)
fn scan_certificate_chain
  (xlist: GCert.certificate_certificate_list_lowtype)
  (#cm: Ghost.erased (list GCE.certificateEntry))
  requires PPVCL.vmatch_vclist
             (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
             xlist cm
  returns res: (V.vec U8.t & V.vec SZ.t & V.vec SZ.t & SZ.t & SZ.t & bool)
  ensures PPVCL.vmatch_vclist
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
            xlist cm **
          (exists* cb offs lns.
            V.pts_to (Mktuple6?._1 res) cb **
            V.pts_to (Mktuple6?._2 res) offs **
            V.pts_to (Mktuple6?._3 res) lns **
            pure (
              V.is_full_vec (Mktuple6?._1 res) /\
              V.length (Mktuple6?._1 res) == 32768 /\ Seq.length cb == 32768 /\
              V.is_full_vec (Mktuple6?._2 res) /\
              V.length (Mktuple6?._2 res) == 8 /\ Seq.length offs == 8 /\
              V.is_full_vec (Mktuple6?._3 res) /\
              V.length (Mktuple6?._3 res) == 8 /\ Seq.length lns == 8 /\
              (if (Mktuple6?._6 res)
               then (FStar.List.Tot.length (RV.reveal_synth_cert_chain cm) > 8 \/
                     RV.reveal_cert_chain_total_bytes (RV.reveal_synth_cert_chain cm) > 32768)
               else (SZ.v (Mktuple6?._5 res) <= 8 /\
                     SZ.v (Mktuple6?._4 res) <= 32768 /\
                     SZ.v (Mktuple6?._5 res) <= Seq.length offs /\
                     SZ.v (Mktuple6?._5 res) <= Seq.length lns /\
                     FStar.List.Tot.length (RV.reveal_synth_cert_chain cm)
                       == SZ.v (Mktuple6?._5 res) /\
                     RV.reveal_cert_chain_total_bytes (RV.reveal_synth_cert_chain cm)
                       == SZ.v (Mktuple6?._4 res) /\
                     L.certificate_chain_matches cb (SZ.v (Mktuple6?._4 res)) offs lns
                       (SZ.v (Mktuple6?._5 res)) (RV.reveal_synth_cert_chain cm)))))
{
  let chain_bytes = V.alloc 0uy 32768sz;
  let offsets = V.alloc 0sz 8sz;
  let lens = V.alloc 0sz 8sz;
  match xlist {
    None -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                None cm);
      RV.lemma_synth_cert_chain_nil ();
      RV.lemma_cert_chain_total_bytes_nil ();
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                None cm);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                None cm)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                xlist cm);
      (chain_bytes, offsets, lens, 0sz, 0sz, false)
    }
    Some nv -> {
      unfold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                (Some nv) cm);
      with s. assert (V.pts_to (snd nv) s **
                      SM.seq_list_match s cm
                        (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv));
      V.pts_to_len (snd nv);
      let count = fst nv;
      let mut i = 0sz;
      let mut failed = false;
      let mut off_ref = 0sz;
      let mut cnt_ref = 0sz;
      let proc_ref = GR.alloc (Nil #B.bytes);
      RV.lemma_synth_cert_chain_nil ();
      RV.lemma_cert_chain_total_bytes_nil ();
      while (
        let f = !failed;
        let iv = !i;
        (not f) && (iv `SZ.lt` count)
      )
      invariant exists* iv fl offv cntv processed cb offs lns.
        R.pts_to i iv **
        R.pts_to failed fl **
        R.pts_to off_ref offv **
        R.pts_to cnt_ref cntv **
        GR.pts_to proc_ref processed **
        V.pts_to (snd nv) s **
        SM.seq_list_match s cm
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv) **
        V.pts_to chain_bytes cb **
        V.pts_to offsets offs **
        V.pts_to lens lns **
        pure (
          SZ.v iv <= SZ.v count /\
          SZ.v count == FStar.List.Tot.length cm /\
          Seq.length s == FStar.List.Tot.length cm /\
          V.is_full_vec (snd nv) /\
          FStar.List.Tot.length cm > 0 /\
          V.is_full_vec chain_bytes /\ V.length chain_bytes == 32768 /\ Seq.length cb == 32768 /\
          V.is_full_vec offsets /\ V.length offsets == 8 /\ Seq.length offs == 8 /\
          V.is_full_vec lens /\ V.length lens == 8 /\ Seq.length lns == 8 /\
          (fl ==> (FStar.List.Tot.length (RV.reveal_synth_cert_chain cm) > 8 \/
                   RV.reveal_cert_chain_total_bytes (RV.reveal_synth_cert_chain cm) > 32768)) /\
          ((not fl) ==> (
             SZ.v iv == SZ.v cntv /\
             SZ.v cntv <= 8 /\
             SZ.v offv <= 32768 /\
             FStar.List.Tot.length processed == SZ.v cntv /\
             RV.reveal_cert_chain_total_bytes processed == SZ.v offv /\
             L.certificate_chain_matches cb (SZ.v offv) offs lns (SZ.v cntv) processed /\
             (FStar.List.Tot.append processed
                (RV.reveal_synth_cert_chain (RV.list_drop (SZ.v iv) cm))
                == RV.reveal_synth_cert_chain cm)))
        )
      {
        let iv = !i;
        let cntv = !cnt_ref;
        let offv = !off_ref;
        with offs0 lns0 cb0 processed0. assert (
          V.pts_to chain_bytes cb0 ** V.pts_to offsets offs0 **
          V.pts_to lens lns0 ** GR.pts_to proc_ref processed0);
        assert (pure (SZ.v iv < FStar.List.Tot.length cm));
        let el = V.op_Array_Access (snd nv) iv;
        SMU.seq_list_match_index_trade
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
          s cm (SZ.v iv);
        Trade.rewrite_with_trade
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cm (SZ.v iv)))
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
             el (FStar.List.Tot.index cm (SZ.v iv)));
        Trade.trans
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
             el (FStar.List.Tot.index cm (SZ.v iv)))
          (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
             (Seq.index s (SZ.v iv)) (FStar.List.Tot.index cm (SZ.v iv)))
          (SM.seq_list_match s cm
             (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv));
        PPB.elim_vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
          el (FStar.List.Tot.index cm (SZ.v iv));
        with em. assert (GCE.certificateEntry_vmatch el em **
                         pure (GCE.certificateEntry_conv em ==
                               Some (FStar.List.Tot.index cm (SZ.v iv))));
        lemma_certEntry_conv em (FStar.List.Tot.index cm (SZ.v iv));
        elim_cert_entry el;
        unfold (LSeqB.vmatch_copy_seqbytes (fst el) (fst em));
        V.pts_to_len (fst el).PPBY.lvec_vec;
        let cert_len = (fst el).PPBY.lvec_len;
        let fits1 = cntv `SZ.lt` 8sz;
        let room = 32768sz `SZ.sub` offv;
        let fits2 = cert_len `SZ.lte` room;
        (* the cert blob being added at this step *)
        RV.lemma_list_drop_index cm (SZ.v iv);
        RV.lemma_synth_cert_chain_cons
          (FStar.List.Tot.index cm (SZ.v iv))
          (RV.list_drop (SZ.v iv + 1) cm);
        if (fits1 && fits2) {
          V.op_Array_Assignment offsets cntv offv;
          V.op_Array_Assignment lens cntv cert_len;
          assert (pure (SZ.v offv + SZ.v cert_len <= 32768));
          copy_vec_into_at chain_bytes offv (fst el).PPBY.lvec_vec cert_len;
          with cbN. assert (V.pts_to chain_bytes cbN);
          CC.certificate_chain_matches_extend
            cb0 cbN offs0 lns0 (Seq.upd offs0 (SZ.v cntv) offv)
            (Seq.upd lns0 (SZ.v cntv) cert_len)
            (SZ.v cntv) processed0 (SZ.v offv);
          let cd : Ghost.erased B.bytes =
            Ghost.hide ((FStar.List.Tot.index cm (SZ.v iv)).GCE.cert_data <: B.bytes);
          Seq.lemma_eq_elim (Seq.slice cbN (SZ.v offv) (SZ.v offv + SZ.v cert_len))
                            (Ghost.reveal cd <: Seq.seq U8.t);
          RV.lemma_cert_chain_total_bytes_snoc (Ghost.reveal processed0) (Ghost.reveal cd);
          CC.lemma_append_cons (Ghost.reveal processed0) (Ghost.reveal cd)
            (RV.reveal_synth_cert_chain (RV.list_drop (SZ.v iv + 1) cm));
          let proc_new : Ghost.erased (list B.bytes) =
            Ghost.hide (FStar.List.Tot.append (Ghost.reveal processed0) [Ghost.reveal cd]);
          GR.write proc_ref proc_new;
          fold (LSeqB.vmatch_copy_seqbytes (fst el) (fst em));
          intro_cert_entry el;
          PPB.intro_vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
            el em (FStar.List.Tot.index cm (SZ.v iv));
          Trade.elim
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
               el (FStar.List.Tot.index cm (SZ.v iv)))
            (SM.seq_list_match s cm
               (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv));
          off_ref := offv `SZ.add` cert_len;
          cnt_ref := cntv `SZ.add` 1sz;
          SZ.fits_lte (SZ.v iv + 1) (SZ.v count);
          i := iv `SZ.add` 1sz;
          FStar.List.Tot.append_length (Ghost.reveal processed0) [Ghost.reveal cd];
          assert (pure (FStar.List.Tot.length (Ghost.reveal proc_new) == SZ.v cntv + 1));
          assert (pure (RV.reveal_cert_chain_total_bytes (Ghost.reveal proc_new)
                        == SZ.v offv + SZ.v cert_len));
          assert (pure (Seq.slice cbN (SZ.v offv) (SZ.v offv + SZ.v cert_len)
                        == (Ghost.reveal cd <: Seq.seq U8.t)));
          assert (pure (L.certificate_chain_matches cbN (SZ.v offv + SZ.v cert_len)
                          (Seq.upd offs0 (SZ.v cntv) offv)
                          (Seq.upd lns0 (SZ.v cntv) cert_len)
                          (SZ.v cntv + 1) (Ghost.reveal proc_new)));
          assert (pure (FStar.List.Tot.append (Ghost.reveal proc_new)
                          (RV.reveal_synth_cert_chain (RV.list_drop (SZ.v iv + 1) cm))
                          == RV.reveal_synth_cert_chain cm));
        } else {
          (* The chain does not fit: prove the negation of [cert_chain_fits]
             via the pure case-analysis lemma (avoids an in-Pulse [if] whose
             branches would carry mismatched ghost postconditions). *)
          lemma_cert_chain_nofit cm (SZ.v iv) (SZ.v cntv) (SZ.v offv) (SZ.v cert_len)
            (Ghost.reveal processed0);
          fold (LSeqB.vmatch_copy_seqbytes (fst el) (fst em));
          intro_cert_entry el;
          PPB.intro_vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
            el em (FStar.List.Tot.index cm (SZ.v iv));
          Trade.elim
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv
               el (FStar.List.Tot.index cm (SZ.v iv)))
            (SM.seq_list_match s cm
               (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv));
          failed := true;
        }
      };
      let fl = !failed;
      let offv = !off_ref;
      let cntv = !cnt_ref;
      let iv = !i;
      let proc_final = GR.read proc_ref;
      RV.lemma_list_drop_length cm;
      RV.lemma_synth_cert_chain_nil ();
      assert (pure ((not fl) ==> SZ.v iv == FStar.List.Tot.length cm));
      assert (pure ((not fl) ==>
                    RV.list_drop (SZ.v iv) cm == RV.list_drop (FStar.List.Tot.length cm) cm));
      assert (pure ((not fl) ==> RV.list_drop (SZ.v iv) cm == []));
      assert (pure ((not fl) ==>
                    RV.reveal_synth_cert_chain (RV.list_drop (SZ.v iv) cm) == []));
      FStar.List.Tot.append_l_nil (Ghost.reveal proc_final);
      assert (pure ((not fl) ==>
                    Ghost.reveal proc_final == RV.reveal_synth_cert_chain cm));
      fold (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                (Some nv) cm);
      rewrite (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                (Some nv) cm)
          as (PPVCL.vmatch_vclist
                (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
                xlist cm);
      GR.free proc_ref;
      (chain_bytes, offsets, lens, offv, cntv, fl)
    }
  }
}

(* Full handshake (content-type 0x16) arm.  Parses the handshake message
   structure exclusively through the QuackyDucky-generated validator + copyful
   reader; ServerHello, Finished and CertificateVerify sub-arms are proven. *)
fn parse_handshake_message
  (content_type: U8.t)
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\ content_type == 0x16uy /\
                 SZ.v input_len <= L.max_record_fragment_len)
  returns r: option L.tls_message
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             (exists* m.
               L.is_valid_tls_message l m **
               pure (CT.parsed_message_wire_success_for
                 content_type (Ghost.reveal 'input_bytes) l m)) **
             pure (exists ct m.
               L.content_type_matches content_type ct /\
               WS.parse_tls_message ct 'input_bytes == Some m) **
             pure (CT.parsed_message_wire_success
               content_type (Ghost.reveal 'input_bytes) l)
           | None ->
             pure (forall (ct:T.content_type).
               L.content_type_matches content_type ct ==>
               WS.parse_tls_message ct 'input_bytes == None))
{
  Arr.pts_to_len input;
  let s = S.from_array input input_len;
  S.pts_to_len s;
  let mut poffset = 0sz;
  let valid = LPS.validate GHS.handshake_validator s poffset;
  let off = !poffset;
  let exact = SZ.eq off input_len;
  if (valid && exact) {
    assert (pure (Seq.equal (Seq.slice (Ghost.reveal 'input_bytes) 0 (SZ.v input_len))
                            (Ghost.reveal 'input_bytes)));
    assert (pure (Some? (LP.parse GHS.handshake_parser 'input_bytes)));
    let gv = Ghost.hide (fst (Some?.v (LP.parse GHS.handshake_parser (Ghost.reveal 'input_bytes))));
    assert (pure (LP.parse GHS.handshake_parser 'input_bytes ==
                  Some (Ghost.reveal gv, SZ.v input_len)));
    PPB.pts_to_parsed_intro GHS.handshake_parser s gv;
    let res = GHS.read_handshake s;
    match res {
      GHS.Body_finished_low xfin -> {
        elim_vmatch_finished xfin;
        with cm. assert (V.pts_to xfin.PPBY.lvec_vec cm);
        V.pts_to_len xfin.PPBY.lvec_vec;
        Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                   (S.pts_to s 'input_bytes);
        S.to_array s;
        RV.lemma_handshake_synth_finished (cm <: GHS.handshake_body_finished);
        RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
          (M.Finished ({ M.verify_data = (cm <: B.bytes_of_len 32) }));
        let lfin = ({ L.finished_verify_data = xfin.PPBY.lvec_vec });
        rewrite (V.pts_to xfin.PPBY.lvec_vec cm)
             as (V.pts_to lfin.L.finished_verify_data cm);
        fold (L.is_valid_finished lfin ({ M.verify_data = (cm <: B.bytes_of_len 32) }));
        fold (L.is_valid_handshake_msg (L.LFinished lfin)
                (M.Finished ({ M.verify_data = (cm <: B.bytes_of_len 32) })));
        fold (L.is_valid_tls_message
                (L.LTlsHandshake (L.LFinished lfin))
                (M.TlsHandshake (M.Finished ({ M.verify_data = (cm <: B.bytes_of_len 32) }))));
        lemma_wire_exists content_type T.Handshake
          (M.TlsHandshake (M.Finished ({ M.verify_data = (cm <: B.bytes_of_len 32) }))) 'input_bytes;
        Some (L.LTlsHandshake (L.LFinished lfin))
      }
      GHS.Body_key_update_low xku -> {
        peek_key_update_high xku;
        PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
          GHS.free_handshake (GHS.Body_key_update_low xku);
        Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                   (S.pts_to s 'input_bytes);
        S.to_array s;
        RV.lemma_handshake_synth_key_update (GHS.Body_key_update?._0 (Ghost.reveal gv));
        RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
          (Ghost.reveal gv) (SZ.v input_len);
        handshake_fallback content_type input input_len
      }
      GHS.Body_new_session_ticket_low sqf -> {
        (* The validator never accepts NewSessionTicket (its payload parser is
           [parse_false]); this arm is statically unreachable. *)
        unreachable sqf;
        None #L.tls_message
      }
      GHS.Body_certificate_verify_low xcv -> {
        let sig_len = (snd xcv).PPBY.lvec_len;
        elim_vmatch_certificate_verify xcv;
        with sig_seq. assert (V.pts_to (snd xcv).PPBY.lvec_vec sig_seq);
        RV.lemma_handshake_synth_certificate_verify
          ({ GCV.algorithm = fst xcv;
             GCV.signature = (sig_seq <: GCV.certificateVerify_signature) });
        if (SZ.lte sig_len 4096sz) {
          (* signature fits: synth is [Some]; land it in the 4096-byte storage. *)
          let sig_vec = alloc_copy_vec_prefix (snd xcv).PPBY.lvec_vec sig_len 4096sz;
          with stored. assert (V.pts_to sig_vec stored);
          V.free (snd xcv).PPBY.lvec_vec;
          Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                     (S.pts_to s 'input_bytes);
          S.to_array s;
          RV.lemma_synth_signature_scheme (fst xcv);
          let scheme_u16 = (match (fst xcv) with
            | GSS.Ecdsa_secp256r1_sha256 -> 1027us
            | GSS.Rsa_pss_rsae_sha256 -> 2052us
            | GSS.Ed25519 -> 2055us
            | GSS.Unknown_signatureScheme v -> v);
          RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
            (Some?.v (RV.handshake_synth (Ghost.reveal gv)));
          WS.lemma_parse_tls_message_round_trip T.Handshake (Ghost.reveal 'input_bytes);
          let lcv = ({ L.certificate_verify_scheme = scheme_u16;
                       L.certificate_verify_signature = sig_vec;
                       L.certificate_verify_signature_len = sig_len });
          rewrite (V.pts_to sig_vec stored)
               as (V.pts_to lcv.L.certificate_verify_signature stored);
          fold (L.is_valid_certificate_verify lcv
                  (M.CertificateVerify?._0 (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
          fold (L.is_valid_handshake_msg (L.LCertificateVerify lcv)
                  (Some?.v (RV.handshake_synth (Ghost.reveal gv))));
          fold (L.is_valid_tls_message
                  (L.LTlsHandshake (L.LCertificateVerify lcv))
                  (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
          lemma_wire_exists content_type T.Handshake
            (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))) 'input_bytes;
          Some (L.LTlsHandshake (L.LCertificateVerify lcv))
        } else {
          (* signature exceeds [max_signature_len]: synth is [None]; fall back. *)
          V.free (snd xcv).PPBY.lvec_vec;
          Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                     (S.pts_to s 'input_bytes);
          S.to_array s;
          RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
            (Ghost.reveal gv) (SZ.v input_len);
          handshake_fallback content_type input input_len
        }
      }
      GHS.Body_encrypted_extensions_low xee -> {
        elim_vmatch_encrypted_extensions xee;
        with cee. assert (PPVCL.vmatch_vclist
                            (PPB.vmatch_conv GEEE.extensionEncryptedExtensions_vmatch
                                             GEEE.extensionEncryptedExtensions_conv)
                            xee cee);
        let res = scan_ee_alpn xee;
        with abytes. assert (V.pts_to (Mktuple3?._1 res) abytes);
        intro_vmatch_encrypted_extensions xee cee #(Ghost.reveal gv);
        PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
          GHS.free_handshake (GHS.Body_encrypted_extensions_low xee);
        Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                   (S.pts_to s 'input_bytes);
        S.to_array s;
        RV.lemma_handshake_synth_encrypted_extensions
          (cee <: GHS.handshake_body_encrypted_extensions);
        RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
          (Some?.v (RV.handshake_synth (Ghost.reveal gv)));
        WS.lemma_parse_tls_message_round_trip T.Handshake (Ghost.reveal 'input_bytes);
        let lee = ({ L.encrypted_extensions_alpn = Mktuple3?._1 res;
                     L.encrypted_extensions_alpn_len = Mktuple3?._2 res;
                     L.encrypted_extensions_has_alpn = Mktuple3?._3 res });
        rewrite (V.pts_to (Mktuple3?._1 res) abytes)
             as (V.pts_to lee.L.encrypted_extensions_alpn abytes);
        fold (L.is_valid_encrypted_extensions lee
                (M.EncryptedExtensions?._0 (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
        fold (L.is_valid_handshake_msg (L.LEncryptedExtensions lee)
                (Some?.v (RV.handshake_synth (Ghost.reveal gv))));
        fold (L.is_valid_tls_message
                (L.LTlsHandshake (L.LEncryptedExtensions lee))
                (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
        lemma_wire_exists content_type T.Handshake
          (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))) 'input_bytes;
        Some (L.LTlsHandshake (L.LEncryptedExtensions lee))
      }
      GHS.Body_server_hello_low xsh -> {
        elim_vmatch_server_hello xsh;
        with cm. assert (GSH.serverHello_vmatch xsh cm **
                         pure (Some? (GSH.serverHello_conv cm) /\
                               Ghost.reveal gv ==
                                 GHS.Body_server_hello (Some?.v (GSH.serverHello_conv cm)) /\
                               GHS.handshake_conv (GHS.Body_server_hello_mid cm) ==
                                 Some (Ghost.reveal gv)));
        let cse : Ghost.erased GSH.serverHello = Some?.v (GSH.serverHello_conv cm);
        elim_serverHello_body xsh;
        lemma_sh_conv_version cm (Ghost.reveal cse);
        let lv = fst xsh;
        if (not (GPV.TLS_1p2? lv)) {
          (* Bad legacy_version: synth lands [None]; fall back. *)
          intro_serverHello_body xsh;
          intro_vmatch_server_hello xsh cm #(Ghost.reveal gv);
          PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            GHS.free_handshake (GHS.Body_server_hello_low xsh);
          Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                     (S.pts_to s 'input_bytes);
          S.to_array s;
          RV.lemma_handshake_synth_server_hello_bad_version (Ghost.reveal cse <: GHS.handshake_body_server_hello);
          RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
            (Ghost.reveal gv) (SZ.v input_len);
          handshake_fallback content_type input input_len
        } else {
          let b = dfst (snd (snd xsh));
          elim_sh_ite_payload xsh b;
          lemma_sh_conv_body cm (Ghost.reveal cse);
          if b {
            (* HelloRetryRequest (magic random tag): synth maps to [M.HelloRetryRequest]. *)
            intro_sh_ite_payload xsh b;
            intro_serverHello_body xsh;
            intro_vmatch_server_hello xsh cm #(Ghost.reveal gv);
            PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
              GHS.free_handshake (GHS.Body_server_hello_low xsh);
            Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                       (S.pts_to s 'input_bytes);
            S.to_array s;
            RV.lemma_handshake_synth_server_hello_hrr (Ghost.reveal cse <: GHS.handshake_body_server_hello)
              (GSHB.HelloRetryRequest?._0 (Ghost.reveal cse).GSH.body);
            RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
              M.HelloRetryRequest;
            fold (L.is_valid_handshake_msg L.LHelloRetryRequest M.HelloRetryRequest);
            fold (L.is_valid_tls_message
                    (L.LTlsHandshake L.LHelloRetryRequest)
                    (M.TlsHandshake M.HelloRetryRequest));
            lemma_wire_exists content_type T.Handshake
              (M.TlsHandshake M.HelloRetryRequest) 'input_bytes;
            Some (L.LTlsHandshake L.LHelloRetryRequest)
          } else {
            (* Normal ServerHello_body_false. *)
            let sf : Ghost.erased GSHB.serverHello_body_false =
              GSHB.ServerHello_body_false?._0 (Ghost.reveal cse).GSH.body;
            elim_serverHelloBody (dsnd (snd (snd xsh)));
            lemma_shbody_conv (dsnd (snd (snd cm))) (Ghost.reveal sf).GSHB.value;
            let comp = fst (snd (dsnd (snd (snd xsh))));
            if (comp <> 0uy) {
              (* legacy_compression_method != 0: synth lands [None]; fall back. *)
              intro_serverHelloBody (dsnd (snd (snd xsh)));
              intro_sh_ite_payload xsh b;
              intro_serverHello_body xsh;
              intro_vmatch_server_hello xsh cm #(Ghost.reveal gv);
              PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
                GHS.free_handshake (GHS.Body_server_hello_low xsh);
              Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                         (S.pts_to s 'input_bytes);
              S.to_array s;
              RV.lemma_handshake_synth_server_hello_sh (Ghost.reveal cse <: GHS.handshake_body_server_hello) (Ghost.reveal sf);
              RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
                (Ghost.reveal gv) (SZ.v input_len);
              handshake_fallback content_type input input_len
            } else {
              let res = scan_sh_key_share (snd (snd (dsnd (snd (snd xsh)))));
              with kbytes. assert (V.pts_to (fst res) kbytes);
              let randvec = V.alloc 0uy 32sz;
              unfold (LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)));
              V.pts_to_len (fst (snd xsh)).PPBY.lvec_vec;
              copy_vec_32_into randvec (fst (snd xsh)).PPBY.lvec_vec;
              with rbytes. assert (V.pts_to randvec rbytes);
              fold (LSeqB.vmatch_copy_seqbytes (fst (snd xsh)) (fst (snd cm)));
              intro_serverHelloBody (dsnd (snd (snd xsh)));
              intro_sh_ite_payload xsh b;
              intro_serverHello_body xsh;
              intro_vmatch_server_hello xsh cm #(Ghost.reveal gv);
              PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
                GHS.free_handshake (GHS.Body_server_hello_low xsh);
              Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                         (S.pts_to s 'input_bytes);
              S.to_array s;
              LP.parsed_data_is_serialize GHS.handshake_serializer (Ghost.reveal 'input_bytes);
              Seq.lemma_eq_elim
                (LP.serialize GHS.handshake_serializer (Ghost.reveal gv) `Seq.append`
                 Seq.slice (Ghost.reveal 'input_bytes) (SZ.v input_len)
                   (Seq.length (Ghost.reveal 'input_bytes)))
                (Ghost.reveal 'input_bytes);
              Seq.lemma_len_append
                (LP.serialize GHS.handshake_serializer (Ghost.reveal gv))
                (Seq.slice (Ghost.reveal 'input_bytes) (SZ.v input_len)
                   (Seq.length (Ghost.reveal 'input_bytes)));
              assert (pure (Seq.length
                (LP.serialize GHS.handshake_serializer (Ghost.reveal gv)) == SZ.v input_len));
              RV.lemma_handshake_synth_server_hello_sh (Ghost.reveal cse <: GHS.handshake_body_server_hello) (Ghost.reveal sf);
              assert (pure (B.length
                (LP.serialize GHS.handshake_serializer
                  (GHS.Body_server_hello (Ghost.reveal cse <: GHS.handshake_body_server_hello)))
                  == SZ.v input_len));
              let found = snd res;
              let fits = SZ.lte input_len 4096sz;
              if (found && fits) {
                RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
                  (Some?.v (RV.handshake_synth (Ghost.reveal gv)));
                WS.lemma_parse_tls_message_round_trip T.Handshake (Ghost.reveal 'input_bytes);
                let lsh = ({ L.server_hello_random = randvec;
                             L.server_hello_key_share = fst res;
                             L.server_hello_cipher_suite = 0x1303us });
                rewrite (V.pts_to randvec rbytes)
                     as (V.pts_to lsh.L.server_hello_random rbytes);
                rewrite (V.pts_to (fst res) kbytes)
                     as (V.pts_to lsh.L.server_hello_key_share kbytes);
                fold (L.is_valid_server_hello lsh
                        (M.ServerHello?._0 (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
                fold (L.is_valid_handshake_msg (L.LServerHello lsh)
                        (Some?.v (RV.handshake_synth (Ghost.reveal gv))));
                fold (L.is_valid_tls_message
                        (L.LTlsHandshake (L.LServerHello lsh))
                        (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
                lemma_wire_exists content_type T.Handshake
                  (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))) 'input_bytes;
                Some (L.LTlsHandshake (L.LServerHello lsh))
              } else {
                (* key_share scan found nothing, or the body exceeds
                   server_hello_max_len: synth is [None]; fall back. *)
                V.free randvec;
                V.free (fst res);
                RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
                  (Ghost.reveal gv) (SZ.v input_len);
                handshake_fallback content_type input input_len
              }
            }
          }
        }
      }
      GHS.Body_certificate_low xcert -> {
        elim_vmatch_certificate xcert;
        with cm0. assert (
          LSeqB.vmatch_copy_seqbytes (fst xcert) (fst cm0) **
          PPVCL.vmatch_vclist
            (PPB.vmatch_conv GCE.certificateEntry_vmatch GCE.certificateEntry_conv)
            (snd xcert) (snd cm0) **
          pure (GHS.handshake_conv (GHS.Body_certificate_mid cm0) == Some (Ghost.reveal gv) /\
                GHS.Body_certificate? (Ghost.reveal gv) /\
                ((GHS.Body_certificate?._0 (Ghost.reveal gv)).GCert.certificate_list
                  <: list GCE.certificateEntry)
                  == (snd cm0 <: list GCE.certificateEntry)));
        let cert_body : Ghost.erased GHS.handshake_body_certificate =
          Ghost.hide (GHS.Body_certificate?._0 (Ghost.reveal gv));
        let res = scan_certificate_chain (snd xcert) #(snd cm0);
        with cb offs lns. assert (
          V.pts_to (Mktuple6?._1 res) cb **
          V.pts_to (Mktuple6?._2 res) offs **
          V.pts_to (Mktuple6?._3 res) lns);
        let cbv = Mktuple6?._1 res;
        let ofv = Mktuple6?._2 res;
        let lnv = Mktuple6?._3 res;
        let cblen = Mktuple6?._4 res;
        let cnt = Mktuple6?._5 res;
        let failed = Mktuple6?._6 res;
        (* [reveal_synth_cert_chain (snd cm0)] is the synthesised chain. *)
        RV.lemma_handshake_synth_certificate (Ghost.reveal cert_body <: GHS.handshake_body_certificate);
        if failed {
          (* The chain does not fit the fixed-size representation: synth lands
             [None]; free the owned Vecs, re-pack and free the parsed structure,
             and fall back. *)
          rewrite (V.pts_to (Mktuple6?._1 res) cb) as (V.pts_to cbv cb);
          rewrite (V.pts_to (Mktuple6?._2 res) offs) as (V.pts_to ofv offs);
          rewrite (V.pts_to (Mktuple6?._3 res) lns) as (V.pts_to lnv lns);
          V.free cbv;
          V.free ofv;
          V.free lnv;
          intro_vmatch_certificate xcert (Ghost.reveal cm0) #(Ghost.reveal gv);
          PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            GHS.free_handshake (GHS.Body_certificate_low xcert);
          Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                     (S.pts_to s 'input_bytes);
          S.to_array s;
          RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
            (Ghost.reveal gv) (SZ.v input_len);
          handshake_fallback content_type input input_len
        } else {
          (* The chain fits: synth is [Some (M.Certificate {chain; body})].
             Build the L representation from the owned Vecs and discharge. *)
          intro_vmatch_certificate xcert (Ghost.reveal cm0) #(Ghost.reveal gv);
          PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
            GHS.free_handshake (GHS.Body_certificate_low xcert);
          Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                     (S.pts_to s 'input_bytes);
          S.to_array s;
          RV.lemma_ptm_handshake_some (Ghost.reveal 'input_bytes) (Ghost.reveal gv)
            (Some?.v (RV.handshake_synth (Ghost.reveal gv)));
          WS.lemma_parse_tls_message_round_trip T.Handshake (Ghost.reveal 'input_bytes);
          let lcert = ({ L.certificate_msg_chain_bytes = cbv;
                         L.certificate_msg_chain_bytes_len = cblen;
                         L.certificate_msg_cert_offsets = ofv;
                         L.certificate_msg_cert_lens = lnv;
                         L.certificate_msg_cert_count = cnt });
          rewrite (V.pts_to (Mktuple6?._1 res) cb)
               as (V.pts_to lcert.L.certificate_msg_chain_bytes cb);
          rewrite (V.pts_to (Mktuple6?._2 res) offs)
               as (V.pts_to lcert.L.certificate_msg_cert_offsets offs);
          rewrite (V.pts_to (Mktuple6?._3 res) lns)
               as (V.pts_to lcert.L.certificate_msg_cert_lens lns);
          fold (L.is_valid_certificate_msg lcert
                  (M.Certificate?._0 (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
          fold (L.is_valid_handshake_msg (L.LCertificate lcert)
                  (Some?.v (RV.handshake_synth (Ghost.reveal gv))));
          fold (L.is_valid_tls_message
                  (L.LTlsHandshake (L.LCertificate lcert))
                  (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))));
          lemma_wire_exists content_type T.Handshake
            (M.TlsHandshake (Some?.v (RV.handshake_synth (Ghost.reveal gv)))) 'input_bytes;
          Some (L.LTlsHandshake (L.LCertificate lcert))
        }
      }
      GHS.Body_client_hello_low xch -> {
        (* A TLS client never legitimately receives a ClientHello; synth maps it
           to None (see WS.synth_handshake_msg_of / RV.lemma_handshake_synth_client_hello),
           so parse_tls_message is None here and we reject via the fallback (which,
           for a ClientHello msg_type, also yields None).  Free the read result. *)
        peek_client_hello_high xch;
        PPB.free_vmatch_conv GHS.handshake_vmatch GHS.handshake_conv
          GHS.free_handshake (GHS.Body_client_hello_low xch);
        Trade.elim (PPB.pts_to_parsed GHS.handshake_parser s #(1.0R /. 2.0R) (Ghost.reveal gv))
                   (S.pts_to s 'input_bytes);
        S.to_array s;
        RV.lemma_handshake_synth_client_hello (GHS.Body_client_hello?._0 (Ghost.reveal gv));
        RV.lemma_parse_handshake_none_of_synth_none (Ghost.reveal 'input_bytes)
          (Ghost.reveal gv) (SZ.v input_len);
        handshake_fallback content_type input input_len
      }
    }
  } else {
    (* Validator failure OR non-exact consumption.  [pts_to s] is intact here
       (we never called [pts_to_parsed_intro] on this branch). *)
    S.to_array s;
    if (valid) {
      (* Non-exact consumption: the QuackyDucky parser succeeded but did not
         consume the whole fragment, so [parse_tls_message] of the Handshake is
         [None] (NewSessionTicket is uninhabited in the generated grammar). *)
      assert (pure (Seq.equal (Seq.slice (Ghost.reveal 'input_bytes) 0 (SZ.v input_len))
                              (Ghost.reveal 'input_bytes)));
      let gv = Ghost.hide (fst (Some?.v (LP.parse GHS.handshake_parser (Ghost.reveal 'input_bytes))));
      assert (pure (LP.parse GHS.handshake_parser 'input_bytes ==
                    Some (Ghost.reveal gv, SZ.v off)));
      RVN.lemma_ptm_handshake_nonexact_none (Ghost.reveal 'input_bytes)
        (Ghost.reveal gv) (SZ.v off);
      None #L.tls_message
    } else {
      (* Validator failure: the QuackyDucky parser rejected the fragment, so
         [parse_handshake] is [None]; route through the byte-level fallback
         ([parse_key_update] / [parse_ignored_post_handshake]). *)
      RV.lemma_parse_handshake_none_of_lp_none (Ghost.reveal 'input_bytes);
      handshake_fallback content_type input input_len
    }
  }
}


fn parse_tls_message
  (content_type: U8.t)
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 SZ.v input_len <= L.max_record_fragment_len)
  returns r: option L.tls_message
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             (exists* m.
               L.is_valid_tls_message l m **
               pure (CT.parsed_message_wire_success_for
                 content_type
                 (Ghost.reveal 'input_bytes)
                 l
                 m)) **
             pure (exists ct m.
               L.content_type_matches content_type ct /\
               WS.parse_tls_message ct 'input_bytes == Some m) **
             pure (CT.parsed_message_wire_success
               content_type
               (Ghost.reveal 'input_bytes)
               l)
           | None ->
             pure (forall (ct:T.content_type).
               L.content_type_matches content_type ct ==>
               WS.parse_tls_message ct 'input_bytes == None))
{
  Arr.pts_to_len input;
  if (content_type = 0x14uy) {
    (* ChangeCipherSpec: spec accepts exactly the single byte 0x01. *)
    RV.lemma_ptm_change_cipher_spec 'input_bytes;
    if (input_len = 1sz) {
      let b0 = input.(0sz);
      if (b0 = 1uy) {
        fold (L.is_valid_tls_message L.LTlsChangeCipherSpec M.TlsChangeCipherSpec);
        lemma_wire_exists content_type T.ChangeCipherSpec M.TlsChangeCipherSpec 'input_bytes;
        Some L.LTlsChangeCipherSpec
      } else {
        None #L.tls_message
      }
    } else {
      None #L.tls_message
    }
  } else if (content_type = 0x15uy) {
    (* Alert: spec accepts exactly a 2-byte fragment whose second byte is a
       recognised alert description. *)
    RV.lemma_ptm_alert 'input_bytes;
    if (input_len = 2sz) {
      let b1 = input.(1sz);
      if (b1 = 0uy || b1 = 10uy || b1 = 20uy || b1 = 40uy || b1 = 46uy ||
          b1 = 47uy || b1 = 50uy || b1 = 51uy || b1 = 70uy || b1 = 110uy) {
        let a = L.alert_description_of_wire_or_unexpected b1;
        lemma_alert_recognized b1;
        lemma_alert_arm 'input_bytes b1;
        lemma_alert_wire_success 'input_bytes b1;
        intro_is_valid_alert b1 a;
        lemma_wire_exists content_type T.Alert (M.TlsAlert a) 'input_bytes;
        Some (L.LTlsAlert b1)
      } else {
        None #L.tls_message
      }
    } else {
      None #L.tls_message
    }
  } else if (content_type = 0x16uy) {
    parse_handshake_message content_type input input_len
  } else if (content_type = 0x17uy) {
    (* ApplicationData: spec always returns Some (TlsApplicationData fragment).
       The L value carries a fixed-size (max_record_fragment_len) copy. *)
    RV.lemma_ptm_application_data 'input_bytes;
    (* Decision 2: the .fsti precondition guarantees input_len <= 16640, so the
       fixed-size copy always succeeds and the spec value (always Some) is met. *)
    let buf = alloc_copy_prefix input input_len 16640sz;
    fold (L.is_valid_application_data
            ({ L.application_data_bytes = buf; L.application_data_len = input_len })
            (Ghost.reveal 'input_bytes));
    fold (L.is_valid_tls_message
            (L.LTlsApplicationData
              ({ L.application_data_bytes = buf; L.application_data_len = input_len }))
            (M.TlsApplicationData 'input_bytes));
    assert (pure (L.content_type_matches content_type T.ApplicationData /\
                  WS.parse_tls_message T.ApplicationData 'input_bytes ==
                  Some (M.TlsApplicationData 'input_bytes)));
    lemma_wire_exists content_type T.ApplicationData
      (M.TlsApplicationData 'input_bytes) 'input_bytes;
    Some (L.LTlsApplicationData
            ({ L.application_data_bytes = buf; L.application_data_len = input_len }))
  } else {
    (* Unknown content type: no T.content_type matches, so the spec parser is
       vacuously None for every matching content type. *)
    None #L.tls_message
  }
}

(* ----------------------------------------------------------------------- *)
(* decode_network_record / decode_network_buffer                           *)
(* ----------------------------------------------------------------------- *)

(* Strip the TLSInnerPlaintext trailer from a decrypted ApplicationData record.
   The spec [WS.parse_plaintext] takes the LAST byte as the real content type
   (no trailing zero-padding is stripped); the payload is the prefix.  We mirror
   that exactly: require the last byte to be a recognised content type
   (0x14..0x17) and return an owned copy of the prefix as the inner fragment.
   Records that carry zero padding (last byte 0x00) are therefore rejected
   (returns None), which is sound w.r.t. [WS.parse_plaintext] returning None. *)

(* A recovered (content_type, owned fragment, length) triple.  We use a named
   record rather than a tuple so that the Pulse prover, after a shallow
   [match _ { Some r -> ... }], can frame the [match] slprop directly (field
   projections of the bound [r] are already in normal form — a tuple pattern
   would be a "deep pattern", which Pulse rejects). *)
noeq
type decoded_fragment = {
  df_ct: U8.t;
  df_payload: V.vec U8.t;
  df_len: SZ.t;
}

fn decode_inner_plaintext
  (out: array U8.t)
  (opened_len: SZ.t)
  requires pts_to out 'opened_bytes **
           pure (B.length 'opened_bytes == SZ.v opened_len)
  returns r: option decoded_fragment
  ensures pts_to out 'opened_bytes **
          (match r with
           | None -> emp
           | Some df ->
             exists* payload_bytes.
               V.pts_to df.df_payload payload_bytes **
               pure (V.is_full_vec df.df_payload /\
                     V.length df.df_payload == SZ.v df.df_len /\
                     B.length payload_bytes == SZ.v df.df_len /\
                     SZ.v df.df_len + 1 == SZ.v opened_len /\
                     (U8.v df.df_ct == 0x14 \/ U8.v df.df_ct == 0x15 \/
                      U8.v df.df_ct == 0x16 \/ U8.v df.df_ct == 0x17) /\
                     (exists pt.
                       WS.parse_plaintext (Ghost.reveal 'opened_bytes) == Some pt /\
                       L.content_type_matches df.df_ct pt.M.content_type /\
                       Seq.equal payload_bytes pt.M.fragment)))
{
  Arr.pts_to_len out;
  if (SZ.lt 0sz opened_len) {
    let last_idx = opened_len `SZ.sub` 1sz;
    let last = out.(last_idx);
    if (last = 0x14uy || last = 0x15uy || last = 0x16uy || last = 0x17uy) {
      let payload = alloc_copy_slice out opened_len 0sz last_idx;
      RVD.lemma_parse_plaintext_some 'opened_bytes;
      Some ({ df_ct = last; df_payload = payload; df_len = last_idx })
    } else {
      None #decoded_fragment
    }
  } else {
    None #decoded_fragment
  }
}

(* Decrypt an ApplicationData (protected) record and strip the inner-plaintext
   trailer.  Reaches the read record-key state from the connection, calls the
   record-layer [peek_open_application] (which does NOT mutate the connection),
   re-folds the connection unchanged, then strips the TLSInnerPlaintext trailer.
   On success returns the inner content-type byte, an owned copy of the inner
   payload, its length, and (in [pure]) the [protected_decoder_fragment_relation]
   that ties the payload to [WS.parse_record]/[R.open_record]/[WS.parse_plaintext].
   Frees all scratch buffers (aad, cipher, opened) on every path. *)
fn peek_decrypt_record
  (c: CR.connection_state)
  (raw: array U8.t)
  (raw_len: SZ.t)
  (flen: SZ.t)
  (#st0: Ghost.erased CS.connection_state)
  (#raw_bytes: Ghost.erased B.bytes)
  requires
    CR.connection_exactly c st0 **
    pts_to raw raw_bytes **
    pure (
      B.length (Ghost.reveal raw_bytes) == SZ.v raw_len /\
      SZ.v raw_len == 5 + SZ.v flen /\
      SZ.v flen <= 16640 /\
      WS.parse_record (Ghost.reveal raw_bytes) ==
        Some (T.ApplicationData,
              Seq.slice (Ghost.reveal raw_bytes) 5 (5 + SZ.v flen),
              SZ.v raw_len))
  returns r: option decoded_fragment
  ensures
    CR.connection_exactly c st0 **
    pts_to raw raw_bytes **
    (match r with
     | None -> emp
     | Some df ->
       exists* payload_bytes.
         V.pts_to df.df_payload payload_bytes **
         pure (
           V.is_full_vec df.df_payload /\
           V.length df.df_payload == SZ.v df.df_len /\
           B.length payload_bytes == SZ.v df.df_len /\
           SZ.v df.df_len <= 16640 /\
           CT.protected_decoder_fragment_relation
             (Ghost.reveal st0) df.df_ct payload_bytes (Ghost.reveal raw_bytes)))
{
  Arr.pts_to_len raw;
  if (SZ.lt flen 16sz) {
    (* fragment too short to contain an AEAD tag — reject *)
    None #decoded_fragment
  } else {
    let out_len = SZ.sub flen 16sz;
    let aad_vec = alloc_copy_slice raw raw_len 0sz 5sz;
    let cipher_vec = alloc_copy_slice raw raw_len 5sz flen;
    let out_vec = V.alloc 0uy out_len;
    with aad_bytes. assert (V.pts_to aad_vec aad_bytes);
    with cipher_bytes. assert (V.pts_to cipher_vec cipher_bytes);
    assert (pure (Seq.equal aad_bytes (CT.record_header_aad (Ghost.reveal raw_bytes))));
    assert (pure (Seq.equal cipher_bytes
      (Seq.slice (Ghost.reveal raw_bytes) 5 (5 + SZ.v flen))));
    V.to_array_pts_to aad_vec;
    V.to_array_pts_to cipher_vec;
    V.to_array_pts_to out_vec;
    (* Reach the read record-key state inside the connection. *)
    unfold (CR.connection_exactly c st0);
    unfold (CR.connection_model_exactly c st0.CS.cs_model);
    unfold (CR.record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    let ok = Rec.peek_open_application c.records.read
               (V.vec_to_array aad_vec) 5sz
               (V.vec_to_array cipher_vec) flen
               (V.vec_to_array out_vec);
    (* peek does not mutate the connection: re-fold unchanged. *)
    fold (CR.record_layer_exactly c.records st0.CS.cs_model.CS.model_record);
    fold (CR.connection_model_exactly c st0.CS.cs_model);
    fold (CR.connection_exactly c st0);
    V.to_vec_pts_to aad_vec;
    V.to_vec_pts_to cipher_vec;
    V.to_vec_pts_to out_vec;
    if ok {
      with out_bytes. assert (V.pts_to out_vec out_bytes);
      V.free aad_vec;
      V.free cipher_vec;
      V.to_array_pts_to out_vec;
      let inner = decode_inner_plaintext (V.vec_to_array out_vec) out_len;
      V.to_vec_pts_to out_vec;
      match inner {
        None -> {
          V.free out_vec;
          None #decoded_fragment
        }
        Some df -> {
          with payload_bytes. assert (V.pts_to df.df_payload payload_bytes);
          (* opened == out_bytes; plaintext == Some?.v (parse_plaintext out_bytes). *)
          DW.lemma_mk_protected_decoder_fragment_relation
            (reveal st0) df.df_ct payload_bytes (Ghost.reveal raw_bytes)
            (Seq.slice (Ghost.reveal raw_bytes) 5 (5 + SZ.v flen))
            (Ghost.reveal out_bytes)
            (Some?.v (WS.parse_plaintext (Ghost.reveal out_bytes)));
          V.free out_vec;
          Some df
        }
      }
    } else {
      V.free aad_vec;
      V.free cipher_vec;
      V.free out_vec;
      None #decoded_fragment
    }
  }
}

(* Construction helper: package an already-validated fragment + parse result
   into a [NetworkRecordOk].  The trivial body just builds the record literal;
   the value is that all the [decoded.decoded_record_*] projections reduce on a
   record built from variable fields, so the Pulse prover can frame the
   per-arm [match decoded.decoded_record_parsed with ...] slprop directly
   against the [match parsed with ...] slprop supplied by the caller.  All the
   semantic obligations (network_input_wf, parse_record, the per-arm parse
   facts) are discharged by the caller and threaded through as preconditions. *)
fn build_decoded_record_ok
  (content_type: U8.t)
  (fragment_vec: V.vec U8.t)
  (fragment_len: SZ.t)
  (parsed: option L.tls_message)
  (st0: Ghost.erased CS.connection_state)
  (raw_bytes: Ghost.erased B.bytes)
  (#fragment_bytes: Ghost.erased B.bytes)
  requires
    V.pts_to fragment_vec fragment_bytes **
    (match parsed with
     | Some l ->
       (exists* m.
         L.is_valid_tls_message l m **
         pure (CT.parsed_message_wire_success_for
           content_type (Ghost.reveal fragment_bytes) l m)) **
       pure (
         exists ct msg.
           L.content_type_matches content_type ct /\
           WS.parse_tls_message ct (Ghost.reveal fragment_bytes) == Some msg) **
       pure (CT.parsed_message_wire_success
         content_type (Ghost.reveal fragment_bytes) l)
     | None ->
       pure (forall (ct:T.content_type).
         L.content_type_matches content_type ct ==>
         WS.parse_tls_message ct (Ghost.reveal fragment_bytes) == None)) **
    pure (
      V.is_full_vec fragment_vec /\
      V.length fragment_vec == SZ.v fragment_len /\
      B.length (Ghost.reveal fragment_bytes) == SZ.v fragment_len /\
      (exists outer_ct outer_fragment.
         WS.parse_record (Ghost.reveal raw_bytes) ==
           Some (outer_ct, outer_fragment, B.length (Ghost.reveal raw_bytes))) /\
      CT.network_input_wf
        (Ghost.reveal st0) content_type
        (Ghost.reveal fragment_bytes) (Ghost.reveal raw_bytes))
  returns r: L.decoded_network_record_result
  ensures
    (match r with
     | L.NetworkRecordNeedMoreInput -> emp
     | L.NetworkRecordDecodeError -> emp
     | L.NetworkRecordOk decoded ->
      exists* fragment_bytes2.
        V.pts_to decoded.L.decoded_record_fragment fragment_bytes2 **
        (match decoded.L.decoded_record_parsed with
         | Some l ->
           (exists* m.
             L.is_valid_tls_message l m **
             pure (CT.parsed_message_wire_success_for
               decoded.L.decoded_record_content_type
               fragment_bytes2
               l
               m)) **
           pure (
             exists ct msg.
               L.content_type_matches
                 decoded.L.decoded_record_content_type
                 ct /\
               WS.parse_tls_message ct fragment_bytes2 == Some msg) **
           pure (CT.parsed_message_wire_success
             decoded.L.decoded_record_content_type
             (Ghost.reveal fragment_bytes2)
             l)
         | None ->
           pure (forall (ct:T.content_type).
             L.content_type_matches
               decoded.L.decoded_record_content_type
               ct ==>
             WS.parse_tls_message ct fragment_bytes2 == None)) **
        pure (
          V.is_full_vec decoded.L.decoded_record_fragment /\
          V.length decoded.L.decoded_record_fragment ==
            SZ.v decoded.L.decoded_record_fragment_len /\
          B.length fragment_bytes2 ==
            SZ.v decoded.L.decoded_record_fragment_len /\
          (exists outer_ct outer_fragment.
             WS.parse_record (Ghost.reveal raw_bytes) ==
               Some (outer_ct, outer_fragment, B.length (Ghost.reveal raw_bytes))) /\
          CT.network_input_wf
            (Ghost.reveal st0)
            decoded.L.decoded_record_content_type
            fragment_bytes2
            (Ghost.reveal raw_bytes)))
{
  L.NetworkRecordOk
    { L.decoded_record_content_type = content_type;
      L.decoded_record_fragment = fragment_vec;
      L.decoded_record_fragment_len = fragment_len;
      L.decoded_record_parsed = parsed }
}

fn decode_network_record
  (c:CR.connection_state)
  (raw: array U8.t)
  (raw_len: SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_len)
  returns r: L.decoded_network_record_result
  ensures CR.connection_exactly c 'st0 **
          pts_to raw 'raw_bytes **
          (match r with
           | L.NetworkRecordNeedMoreInput -> emp
           | L.NetworkRecordDecodeError -> emp
           | L.NetworkRecordOk decoded ->
            exists* fragment_bytes.
              V.pts_to decoded.L.decoded_record_fragment fragment_bytes **
              (match decoded.L.decoded_record_parsed with
               | Some l ->
                 (exists* m.
                   L.is_valid_tls_message l m **
                   pure (CT.parsed_message_wire_success_for
                     decoded.L.decoded_record_content_type
                     fragment_bytes
                     l
                     m)) **
                 pure (
                   exists ct msg.
                     L.content_type_matches
                       decoded.L.decoded_record_content_type
                       ct /\
                     WS.parse_tls_message ct fragment_bytes == Some msg) **
                 pure (CT.parsed_message_wire_success
                   decoded.L.decoded_record_content_type
                   (Ghost.reveal fragment_bytes)
                   l)
               | None ->
                 pure (forall (ct:T.content_type).
                   L.content_type_matches
                     decoded.L.decoded_record_content_type
                     ct ==>
                   WS.parse_tls_message ct fragment_bytes == None)) **
              pure (
                V.is_full_vec decoded.L.decoded_record_fragment /\
                V.length decoded.L.decoded_record_fragment ==
                  SZ.v decoded.L.decoded_record_fragment_len /\
                B.length fragment_bytes ==
                  SZ.v decoded.L.decoded_record_fragment_len /\
                (exists outer_ct outer_fragment.
                   WS.parse_record (Ghost.reveal 'raw_bytes) ==
                     Some (outer_ct, outer_fragment, B.length (Ghost.reveal 'raw_bytes))) /\
                CT.network_input_wf
                  'st0
                  decoded.L.decoded_record_content_type
                  fragment_bytes
                  (Ghost.reveal 'raw_bytes)))
{
  Arr.pts_to_len raw;
  if (SZ.lt raw_len 5sz) {
    L.NetworkRecordNeedMoreInput
  } else {
    let b0 = raw.(0sz);
    let b1 = raw.(1sz);
    let b2 = raw.(2sz);
    let b3 = raw.(3sz);
    let b4 = raw.(4sz);
    let flen = SZ.add (SZ.mul (u8_to_sz b3) 256sz) (u8_to_sz b4);
    if (b1 = 0x03uy && b2 = 0x03uy && SZ.lte flen 16640sz &&
        (b0 = 0x14uy || b0 = 0x15uy || b0 = 0x16uy || b0 = 0x17uy)) {
      (* flen <= 16640, so flen + 5 fits in SizeT; require EXACT consumption. *)
      let rec_len = SZ.add flen 5sz;
      if (raw_len = rec_len) {
      RVD.lemma_parse_record_from_header 'raw_bytes;
      let outer_ct : T.content_type =
        (if b0 = 0x14uy then T.ChangeCipherSpec
         else if b0 = 0x15uy then T.Alert
         else if b0 = 0x16uy then T.Handshake
         else T.ApplicationData);
      if (b0 = 0x17uy) {
        (* PROTECTED path (ApplicationData): decrypt + strip inner plaintext. *)
        let inner = peek_decrypt_record c raw raw_len flen;
        match inner {
          None -> {
            L.NetworkRecordDecodeError
          }
          Some df -> {
            with payload_bytes. assert (V.pts_to df.df_payload payload_bytes);
            V.to_array_pts_to df.df_payload;
            let parsed = parse_tls_message df.df_ct (V.vec_to_array df.df_payload) df.df_len;
            V.to_vec_pts_to df.df_payload;
            match parsed {
              None -> {
                DW.lemma_mk_protected_network_input_wf_none
                  (reveal 'st0) df.df_ct payload_bytes (Ghost.reveal 'raw_bytes);
                build_decoded_record_ok df.df_ct df.df_payload df.df_len None 'st0 'raw_bytes
              }
              Some l -> {
                if (not (DW.l_is_received_cleartext l)) {
                  with m. assert (L.is_valid_tls_message l m);
                  DW.lemma_mk_protected_network_input_wf
                    (reveal 'st0) df.df_ct payload_bytes (Ghost.reveal 'raw_bytes)
                    (Seq.slice (Ghost.reveal 'raw_bytes) 5 (5 + SZ.v flen)) l m;
                  build_decoded_record_ok df.df_ct df.df_payload df.df_len (Some l) 'st0 'raw_bytes
                } else {
                  L.free_tls_message l;
                  V.free df.df_payload;
                  L.NetworkRecordDecodeError
                }
              }
            }
          }
        }
      } else {
        (* CLEARTEXT path: the outer fragment is the dispatcher fragment. *)
        let fragment_vec = alloc_copy_slice raw raw_len 5sz flen;
        with fragment_bytes. assert (V.pts_to fragment_vec fragment_bytes);
        assert (pure (B.length fragment_bytes == SZ.v flen));
        V.to_array_pts_to fragment_vec;
        let parsed = parse_tls_message b0 (V.vec_to_array fragment_vec) flen;
        V.to_vec_pts_to fragment_vec;
        match parsed {
          None -> {
            DW.lemma_mk_cleartext_network_input_wf_none
              (reveal 'st0) b0 outer_ct fragment_bytes (Ghost.reveal 'raw_bytes);
            build_decoded_record_ok b0 fragment_vec flen None 'st0 'raw_bytes
          }
          Some l -> {
            if (DW.cleartext_consistent b0 l) {
              with m. assert (L.is_valid_tls_message l m);
              DW.lemma_mk_cleartext_network_input_wf_consistent
                (reveal 'st0) b0 outer_ct fragment_bytes (Ghost.reveal 'raw_bytes) l m;
              build_decoded_record_ok b0 fragment_vec flen (Some l) 'st0 'raw_bytes
            } else {
              L.free_tls_message l;
              V.free fragment_vec;
              L.NetworkRecordDecodeError
            }
          }
        }
      }
      } else {
        L.NetworkRecordDecodeError
      }
    } else {
      L.NetworkRecordDecodeError
    }
  }
}

(* Construction helper for [decode_network_buffer], analogous to
   [build_decoded_record_ok]: it packages the owned raw-record prefix + decoded
   fragment + parse result into a [NetworkBufferOk].  All semantic obligations
   (the [Seq.slice] relation between the prefix and the input buffer, the
   [WS.parse_record] fact on the prefix, and [network_input_wf] computed against
   the prefix) are discharged by the caller and threaded through. *)
fn build_decoded_buffer_ok
  (content_type: U8.t)
  (raw_record_vec: V.vec U8.t)
  (consumed_len: SZ.t)
  (fragment_vec: V.vec U8.t)
  (fragment_len: SZ.t)
  (parsed: option L.tls_message)
  (st0: Ghost.erased CS.connection_state)
  (raw_bytes: Ghost.erased B.bytes)
  (#raw_record_bytes: Ghost.erased B.bytes)
  (#fragment_bytes: Ghost.erased B.bytes)
  requires
    V.pts_to raw_record_vec raw_record_bytes **
    V.pts_to fragment_vec fragment_bytes **
    (match parsed with
     | Some l ->
       (exists* m.
         L.is_valid_tls_message l m **
         pure (CT.parsed_message_wire_success_for
           content_type (Ghost.reveal fragment_bytes) l m)) **
       pure (
         exists ct msg.
           L.content_type_matches content_type ct /\
           WS.parse_tls_message ct (Ghost.reveal fragment_bytes) == Some msg) **
       pure (CT.parsed_message_wire_success
         content_type (Ghost.reveal fragment_bytes) l)
     | None ->
       pure (forall (ct:T.content_type).
         L.content_type_matches content_type ct ==>
         WS.parse_tls_message ct (Ghost.reveal fragment_bytes) == None)) **
    pure (
      V.is_full_vec raw_record_vec /\
      V.length raw_record_vec == SZ.v consumed_len /\
      B.length (Ghost.reveal raw_record_bytes) == SZ.v consumed_len /\
      SZ.v consumed_len <= B.length (Ghost.reveal raw_bytes) /\
      Seq.equal (Ghost.reveal raw_record_bytes)
                (Seq.slice (Ghost.reveal raw_bytes) 0 (SZ.v consumed_len)) /\
      (exists outer_ct outer_fragment.
         WS.parse_record (Ghost.reveal raw_record_bytes) ==
           Some (outer_ct, outer_fragment, B.length (Ghost.reveal raw_record_bytes))) /\
      V.is_full_vec fragment_vec /\
      V.length fragment_vec == SZ.v fragment_len /\
      B.length (Ghost.reveal fragment_bytes) == SZ.v fragment_len /\
      CT.network_input_wf
        (Ghost.reveal st0) content_type
        (Ghost.reveal fragment_bytes) (Ghost.reveal raw_record_bytes))
  returns r: L.decoded_network_buffer_result
  ensures
    (match r with
     | L.NetworkBufferNeedMoreInput -> emp
     | L.NetworkBufferDecodeError -> emp
     | L.NetworkBufferOk decoded ->
      exists* raw_record_bytes2 fragment_bytes2.
        V.pts_to decoded.L.decoded_buffer_raw_record raw_record_bytes2 **
        V.pts_to decoded.L.decoded_buffer_fragment fragment_bytes2 **
        (match decoded.L.decoded_buffer_parsed with
         | Some l ->
           (exists* m.
            L.is_valid_tls_message l m **
            pure (CT.parsed_message_wire_success_for
              decoded.L.decoded_buffer_content_type
              fragment_bytes2
              l
              m)) **
           pure (
            exists ct msg.
              L.content_type_matches
                decoded.L.decoded_buffer_content_type
                ct /\
              WS.parse_tls_message ct fragment_bytes2 == Some msg) **
           pure (CT.parsed_message_wire_success
            decoded.L.decoded_buffer_content_type
            (Ghost.reveal fragment_bytes2)
            l)
         | None ->
           pure (forall (ct:T.content_type).
            L.content_type_matches
              decoded.L.decoded_buffer_content_type
              ct ==>
            WS.parse_tls_message ct fragment_bytes2 == None)) **
        pure (
          V.is_full_vec decoded.L.decoded_buffer_raw_record /\
          V.length decoded.L.decoded_buffer_raw_record ==
            SZ.v decoded.L.decoded_buffer_raw_record_len /\
          B.length raw_record_bytes2 ==
            SZ.v decoded.L.decoded_buffer_raw_record_len /\
          decoded.L.decoded_buffer_raw_record_len ==
            decoded.L.decoded_buffer_consumed_len /\
          SZ.v decoded.L.decoded_buffer_consumed_len <=
            B.length (Ghost.reveal raw_bytes) /\
          Seq.equal
            raw_record_bytes2
            (Seq.slice
             (Ghost.reveal raw_bytes)
             0
             (SZ.v decoded.L.decoded_buffer_consumed_len)) /\
          (exists outer_ct outer_fragment.
             WS.parse_record raw_record_bytes2 ==
               Some (outer_ct, outer_fragment, B.length raw_record_bytes2)) /\
          V.is_full_vec decoded.L.decoded_buffer_fragment /\
          V.length decoded.L.decoded_buffer_fragment ==
            SZ.v decoded.L.decoded_buffer_fragment_len /\
          B.length fragment_bytes2 ==
            SZ.v decoded.L.decoded_buffer_fragment_len /\
          CT.network_input_wf
            (Ghost.reveal st0)
            decoded.L.decoded_buffer_content_type
            fragment_bytes2
            raw_record_bytes2))
{
  L.NetworkBufferOk
    { L.decoded_buffer_raw_record = raw_record_vec;
      L.decoded_buffer_raw_record_len = consumed_len;
      L.decoded_buffer_consumed_len = consumed_len;
      L.decoded_buffer_content_type = content_type;
      L.decoded_buffer_fragment = fragment_vec;
      L.decoded_buffer_fragment_len = fragment_len;
      L.decoded_buffer_parsed = parsed }
}

fn decode_network_buffer
  (c:CR.connection_state)
  (raw: array U8.t)
  (raw_len: SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_len)
  returns r: L.decoded_network_buffer_result
  ensures CR.connection_exactly c 'st0 **
          pts_to raw 'raw_bytes **
          (match r with
           | L.NetworkBufferNeedMoreInput -> emp
           | L.NetworkBufferDecodeError -> emp
           | L.NetworkBufferOk decoded ->
            exists* raw_record_bytes fragment_bytes.
              V.pts_to decoded.L.decoded_buffer_raw_record raw_record_bytes **
              V.pts_to decoded.L.decoded_buffer_fragment fragment_bytes **
              (match decoded.L.decoded_buffer_parsed with
               | Some l ->
                 (exists* m.
                  L.is_valid_tls_message l m **
                  pure (CT.parsed_message_wire_success_for
                    decoded.L.decoded_buffer_content_type
                    fragment_bytes
                    l
                    m)) **
                 pure (
                  exists ct msg.
                    L.content_type_matches
                      decoded.L.decoded_buffer_content_type
                      ct /\
                    WS.parse_tls_message ct fragment_bytes == Some msg) **
                 pure (CT.parsed_message_wire_success
                  decoded.L.decoded_buffer_content_type
                  (Ghost.reveal fragment_bytes)
                  l)
               | None ->
                 pure (forall (ct:T.content_type).
                  L.content_type_matches
                    decoded.L.decoded_buffer_content_type
                    ct ==>
                  WS.parse_tls_message ct fragment_bytes == None)) **
              pure (
                V.is_full_vec decoded.L.decoded_buffer_raw_record /\
                V.length decoded.L.decoded_buffer_raw_record ==
                  SZ.v decoded.L.decoded_buffer_raw_record_len /\
                B.length raw_record_bytes ==
                  SZ.v decoded.L.decoded_buffer_raw_record_len /\
                decoded.L.decoded_buffer_raw_record_len ==
                  decoded.L.decoded_buffer_consumed_len /\
                SZ.v decoded.L.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes) /\
                Seq.equal
                  raw_record_bytes
                  (Seq.slice
                   (Ghost.reveal 'raw_bytes)
                   0
                   (SZ.v decoded.L.decoded_buffer_consumed_len)) /\
                (exists outer_ct outer_fragment.
                   WS.parse_record raw_record_bytes ==
                     Some (outer_ct, outer_fragment, B.length raw_record_bytes)) /\
                V.is_full_vec decoded.L.decoded_buffer_fragment /\
                V.length decoded.L.decoded_buffer_fragment ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                B.length fragment_bytes ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                CT.network_input_wf
                  'st0
                  decoded.L.decoded_buffer_content_type
                  fragment_bytes
                  raw_record_bytes))
{
  Arr.pts_to_len raw;
  if (SZ.lt raw_len 5sz) {
    (* not even a full record header yet *)
    L.NetworkBufferNeedMoreInput
  } else {
    let b0 = raw.(0sz);
    let b1 = raw.(1sz);
    let b2 = raw.(2sz);
    let b3 = raw.(3sz);
    let b4 = raw.(4sz);
    let flen = SZ.add (SZ.mul (u8_to_sz b3) 256sz) (u8_to_sz b4);
    if (b1 = 0x03uy && b2 = 0x03uy && SZ.lte flen 16640sz &&
        (b0 = 0x14uy || b0 = 0x15uy || b0 = 0x16uy || b0 = 0x17uy)) {
      (* flen <= 16640, so flen + 5 fits in SizeT. *)
      let consumed_len = SZ.add flen 5sz;
      if (SZ.lte consumed_len raw_len) {
        (* enough bytes for the first record; trailing bytes are allowed. *)
        let raw_record_vec = alloc_copy_slice raw raw_len 0sz consumed_len;
        with raw_record_bytes. assert (V.pts_to raw_record_vec raw_record_bytes);
        DW.lemma_parse_record_buffer_prefix (Ghost.reveal 'raw_bytes)
          (Ghost.reveal raw_record_bytes) (SZ.v flen);
        let outer_ct : T.content_type =
          (if b0 = 0x14uy then T.ChangeCipherSpec
           else if b0 = 0x15uy then T.Alert
           else if b0 = 0x16uy then T.Handshake
           else T.ApplicationData);
        if (b0 = 0x17uy) {
          (* PROTECTED path: decrypt the prefix + strip inner plaintext. *)
          V.to_array_pts_to raw_record_vec;
          let inner = peek_decrypt_record c (V.vec_to_array raw_record_vec) consumed_len flen;
          V.to_vec_pts_to raw_record_vec;
          match inner {
            None -> {
              V.free raw_record_vec;
              L.NetworkBufferDecodeError
            }
            Some df -> {
              with payload_bytes. assert (V.pts_to df.df_payload payload_bytes);
              V.to_array_pts_to df.df_payload;
              let parsed = parse_tls_message df.df_ct (V.vec_to_array df.df_payload) df.df_len;
              V.to_vec_pts_to df.df_payload;
              match parsed {
                None -> {
                  DW.lemma_mk_protected_network_input_wf_none
                    (reveal 'st0) df.df_ct payload_bytes (Ghost.reveal raw_record_bytes);
                  build_decoded_buffer_ok df.df_ct raw_record_vec consumed_len
                    df.df_payload df.df_len None 'st0 'raw_bytes
                }
                Some l -> {
                  if (not (DW.l_is_received_cleartext l)) {
                    with m. assert (L.is_valid_tls_message l m);
                    DW.lemma_mk_protected_network_input_wf
                      (reveal 'st0) df.df_ct payload_bytes (Ghost.reveal raw_record_bytes)
                      (Seq.slice (Ghost.reveal raw_record_bytes) 5 (5 + SZ.v flen)) l m;
                    build_decoded_buffer_ok df.df_ct raw_record_vec consumed_len
                      df.df_payload df.df_len (Some l) 'st0 'raw_bytes
                  } else {
                    L.free_tls_message l;
                    V.free df.df_payload;
                    V.free raw_record_vec;
                    L.NetworkBufferDecodeError
                  }
                }
              }
            }
          }
        } else {
          (* CLEARTEXT path: the outer fragment is the dispatcher fragment. *)
          V.to_array_pts_to raw_record_vec;
          let fragment_vec =
            alloc_copy_slice (V.vec_to_array raw_record_vec) consumed_len 5sz flen;
          with fragment_bytes. assert (V.pts_to fragment_vec fragment_bytes);
          V.to_vec_pts_to raw_record_vec;
          V.to_array_pts_to fragment_vec;
          let parsed = parse_tls_message b0 (V.vec_to_array fragment_vec) flen;
          V.to_vec_pts_to fragment_vec;
          match parsed {
            None -> {
              DW.lemma_mk_cleartext_network_input_wf_none
                (reveal 'st0) b0 outer_ct fragment_bytes (Ghost.reveal raw_record_bytes);
              build_decoded_buffer_ok b0 raw_record_vec consumed_len
                fragment_vec flen None 'st0 'raw_bytes
            }
            Some l -> {
              if (DW.cleartext_consistent b0 l) {
                with m. assert (L.is_valid_tls_message l m);
                DW.lemma_mk_cleartext_network_input_wf_consistent
                  (reveal 'st0) b0 outer_ct fragment_bytes (Ghost.reveal raw_record_bytes) l m;
                build_decoded_buffer_ok b0 raw_record_vec consumed_len
                  fragment_vec flen (Some l) 'st0 'raw_bytes
              } else {
                L.free_tls_message l;
                V.free fragment_vec;
                V.free raw_record_vec;
                L.NetworkBufferDecodeError
              }
            }
          }
        }
      } else {
        (* header parsed but the full fragment has not arrived yet *)
        L.NetworkBufferNeedMoreInput
      }
    } else {
      L.NetworkBufferDecodeError
    }
  }
}
