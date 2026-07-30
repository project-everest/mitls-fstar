module TLS13.Impl.Serializer.Handshake

#lang-pulse

(* Interface for the build-direction (serialize) handshake-message serializers.

   Exposes:
   - the six runtime POC serializers (extractable Pulse [fn]s);
   - the canonical spec constructors [poc_canonical_sh/cert/ch] and the five
     shared ClientHello extension high values [ch_*_high];
   - the five ClientHello [Sem] accessor lemmas.

   The [poc_canonical_*] and [ch_*_high] spec constructors are kept TRANSPARENT
   here on purpose: downstream bridging lemmas (e.g. in
   TLS13.Impl.Server.Send: [lemma_mk_server_hello_witness_eq_poc],
   [lemma_mk_cert_witness_eq_poc]) prove [mk_*_witness == poc_canonical_*] by
   definitional unfolding ([= ()]), so their bodies must remain visible through
   this interface.  They are ghost specs, marked [noextract], and do not reach
   extraction.

   NB: the [val]/[fn] declarations below are ordered to match the definition
   order of the implementation (F* requires the two orders to agree). *)

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module GCert = TLS13.Wire.Generated.Certificate
module GCertE = TLS13.Wire.Generated.CertificateEntry
module GCH = TLS13.Wire.Generated.ClientHello
module GCL = TLS13.Wire.Generated.Certificate_certificate_list
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GEX = TLS13.Wire.Generated.CertificateEntry_extensions
module GFin = TLS13.Wire.Generated.Finished
module GHN = TLS13.Wire.Generated.HostName
module GKSCH = TLS13.Wire.Generated.KeyShareClientHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSN = TLS13.Wire.Generated.ServerName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GSS = TLS13.Wire.Generated.SignatureScheme
module L = TLS13.Impl.Messages
module LL = FStar.List.Tot
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(* ===================================================================== *)
(* Canonical spec constructors (TRANSPARENT: downstream bridging lemmas   *)
(* unfold these definitionally; kept [noextract] as ghost specs).         *)
(* ===================================================================== *)

(* ---- canonical ServerHello record (transparent copy of the non-HRR branch
   of TLS13.Impl.Server.Send.mk_server_hello_witness) ---- *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
noextract
let poc_canonical_sh (rnd ks sid: B.bytes) (cs: GCS.cipherSuite)
  : Pure GSH.serverHello
    (requires Seq.length rnd == 32 /\ (rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\ Seq.length ks == 32 /\ Seq.length sid == 32)
    (ensures fun _ -> True)
  = let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    let ksesh : GESH.extensionServerHello_extension_data_key_share = kse in
    let ks_ext : GESH.extensionServerHello = GESH.Extension_data_key_share ksesh in
    let sv_ext : GESH.extensionServerHello =
      GESH.Extension_data_supported_versions
        (GPV.TLS_1p3 <: GESH.extensionServerHello_extension_data_supported_versions) in
    GSHBody.serverHelloBody_extensions_list_bytesize_nil;
    GSHBody.serverHelloBody_extensions_list_bytesize_cons sv_ext [];
    GSHBody.serverHelloBody_extensions_list_bytesize_cons ks_ext [sv_ext];
    GPV.protocolVersion_bytesize_eq GPV.TLS_1p3;
    let exts : GSHBody.serverHelloBody_extensions = [ks_ext; sv_ext] in
    let sid_echo : GSHBody.serverHelloBody_legacy_session_id_echo = sid in
    let body : GSHBody.serverHelloBody = {
      GSHBody.legacy_session_id_echo = sid_echo;
      GSHBody.cipher_suite = cs;
      GSHBody.legacy_compression_method = 0uy;
      GSHBody.extensions = exts;
    } in
    let r32 : Seq.lseq U8.t 32 = rnd in
    let bf : GSHB.serverHello_body_false = { GSHB.tag = r32; GSHB.value = body } in
    { GSH.legacy_version = GPV.TLS_1p2; GSH.body = GSHB.ServerHello_body_false bf }
#pop-options

(* ---- canonical Certificate record (transparent copy of mk_cert_witness) ---- *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
noextract
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

(* ---- shared canonical ClientHello extension high values (each discharges
   its own refinement) ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
noextract
let ch_sn_high (sni: B.bytes { 1 <= Seq.length sni /\ Seq.length sni <= 65461 })
  : GECH.extensionClientHello
  = let hn : GHN.hostName = sni in
    let sn : GSN.serverName = GSN.Name_host_name hn in
    GSNL.serverNameList_list_bytesize_nil;
    GSNL.serverNameList_list_bytesize_cons sn [];
    GSN.serverName_bytesize_eqn_host_name hn;
    GHN.hostName_bytesize_eqn hn;
    GECH.Extension_data_server_name ([sn] <: GECH.extensionClientHello_extension_data_server_name)

noextract
let ch_sg_high : GECH.extensionClientHello
  = GECH.Extension_data_supported_groups ([GNG.X25519] <: GECH.extensionClientHello_extension_data_supported_groups)

noextract
let ch_sa_high (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : GECH.extensionClientHello
  = GECH.Extension_data_signature_algorithms sa

noextract
let ch_ks_high (ks: B.bytes { Seq.length ks == 32 })
  : GECH.extensionClientHello
  = let ke : GKSE.keyShareEntry_key_exchange = ks in
    let kse : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = ke } in
    GKSCH.keyShareClientHello_list_bytesize_nil;
    GKSCH.keyShareClientHello_list_bytesize_cons kse [];
    GKSE.keyShareEntry_bytesize_eqn kse;
    GNG.namedGroup_bytesize_eq GNG.X25519;
    GKSE.keyShareEntry_key_exchange_bytesize_eqn ke;
    GECH.Extension_data_key_share ([kse] <: GECH.extensionClientHello_extension_data_key_share)

noextract
let ch_sv_high : GECH.extensionClientHello
  = GECH.Extension_data_supported_versions ([GPV.TLS_1p3] <: GECH.extensionClientHello_extension_data_supported_versions)
#pop-options

(* ---- canonical ClientHello record ---- *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 200"
noextract
let poc_canonical_ch (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Pure GCH.clientHello
    (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
              1 <= Seq.length sni /\ Seq.length sni <= 255 /\
              LL.length cs <= 16 /\ LL.length sa <= 16)
    (ensures fun _ -> True)
  = let r32 : Seq.lseq U8.t 32 = rnd in
    let sn_ext = ch_sn_high sni in
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
    let exts : GCH.clientHello_extensions = [sn_ext; sg_ext; sa_ext; ks_ext; sv_ext] in
    let comp : GCH.clientHello_legacy_compression_methods = Seq.create 1 0uy in
    let sid_f : GCH.clientHello_legacy_session_id = sid in
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = r32;
      GCH.legacy_session_id = sid_f;
      GCH.cipher_suites = cs;
      GCH.legacy_compression_methods = comp;
      GCH.extensions = exts; }
#pop-options

(* ===================================================================== *)
(* Runtime POC serializers (extractable) -- part 1.                       *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* ClientHello [Sem] accessor lemmas (canonical pins each field).         *)
(* Proofs stay in the implementation.                                     *)
(* ===================================================================== *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 120"
val lemma_ch_random (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_random (poc_canonical_ch rnd sni ks sid cs sa) == (rnd <: Seq.lseq U8.t 32))

val lemma_ch_server_name (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_server_name (poc_canonical_ch rnd sni ks sid cs sa) == Some (sni <: Seq.seq U8.t))

val lemma_ch_key_share (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_key_share_x25519 (poc_canonical_ch rnd sni ks sid cs sa) == Some (ks <: Seq.seq U8.t))

val lemma_ch_cipher_suites (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_cipher_suites (poc_canonical_ch rnd sni ks sid cs sa) == (cs <: list GCS.cipherSuite))

val lemma_ch_sig_algs (rnd sni ks sid: B.bytes)
  (cs: GCH.clientHello_cipher_suites)
  (sa: GECH.extensionClientHello_extension_data_signature_algorithms)
  : Lemma (requires Seq.length rnd == 32 /\ Seq.length ks == 32 /\ Seq.length sid == 32 /\
                    1 <= Seq.length sni /\ Seq.length sni <= 255 /\
                    LL.length cs <= 16 /\ LL.length sa <= 16)
          (ensures Sem.clientHello_sig_algs (poc_canonical_ch rnd sni ks sid cs sa) == Some (sa <: list GSS.signatureScheme))
#pop-options

(* ===================================================================== *)
(* Runtime POC serializers (extractable) -- part 2 (ClientHello).         *)
(* ===================================================================== *)

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
