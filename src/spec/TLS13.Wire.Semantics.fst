module TLS13.Wire.Semantics

(* Phase 3a of the QuackyDucky migration.

   A layer of TOTAL, PURE semantic accessor functions over the
   QuackyDucky-generated TLS 1.3 wire record types.  These let downstream code
   read the profile-relevant fields of a parsed wire record without
   re-parsing the wire bytes, mirroring the hand-written projection records of
   TLS13.Messages (M.client_hello, M.server_hello, ...).

   Every function here is total (Tot) and verifies without admits/assumes.
   The vlbytes payload types (host names, key shares, signatures, protocol
   names) are refinements of [Seq.seq U8.t] (= LowParse.Bytes.bytes), so we
   coerce them to plain byte sequences with [<:] ascriptions; downstream code
   performs any length checks. *)

module U8  = FStar.UInt8
module Seq = FStar.Seq

module GCH     = TLS13.Wire.Generated.ClientHello
module GECH    = TLS13.Wire.Generated.ExtensionClientHello
module GKCH    = TLS13.Wire.Generated.KeyShareClientHello
module GKE     = TLS13.Wire.Generated.KeyShareEntry
module GSN     = TLS13.Wire.Generated.ServerName
module GSNL    = TLS13.Wire.Generated.ServerNameList
module GSSL    = TLS13.Wire.Generated.SignatureSchemeList
module GSS     = TLS13.Wire.Generated.SignatureScheme
module GCS     = TLS13.Wire.Generated.CipherSuite
module GNG     = TLS13.Wire.Generated.NamedGroup
module GSH     = TLS13.Wire.Generated.ServerHello
module GSHbody = TLS13.Wire.Generated.ServerHello_body
module GSHB    = TLS13.Wire.Generated.ServerHelloBody
module GESH    = TLS13.Wire.Generated.ExtensionServerHello
module GPV     = TLS13.Wire.Generated.ProtocolVersion
module GEE     = TLS13.Wire.Generated.EncryptedExtensions
module GEEE    = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN     = TLS13.Wire.Generated.ProtocolName
module GCV     = TLS13.Wire.Generated.CertificateVerify
module GFin    = TLS13.Wire.Generated.Finished

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1"

(* ------------------------------------------------------------------ *)
(* ClientHello                                                         *)
(* ------------------------------------------------------------------ *)

/// The 32-byte ClientHello random.
let clientHello_random (ch: GCH.clientHello) : Seq.lseq U8.t 32 =
  ch.GCH.random

/// The offered cipher suites (the length refinement is dropped).
let clientHello_cipher_suites (ch: GCH.clientHello) : list GCS.cipherSuite =
  ch.GCH.cipher_suites <: list GCS.cipherSuite

/// Walk the ClientHello extensions for the first server_name extension and
/// return the bytes of the first host name it carries, if any.
let rec ch_find_server_name (l: list GECH.extensionClientHello)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | GECH.Extension_data_server_name sn :: _ ->
      (match (sn <: list GSN.serverName) with
       | [] -> None
       | GSN.Name_host_name h :: _ -> Some (h <: Seq.seq U8.t))
    | _ :: tl -> ch_find_server_name tl

let clientHello_server_name (ch: GCH.clientHello) : option (Seq.seq U8.t) =
  ch_find_server_name (ch.GCH.extensions <: list GECH.extensionClientHello)

/// Find the first X25519 key-share entry's raw key_exchange bytes.
let rec kse_list_find_x25519 (l: list GKE.keyShareEntry)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | entry :: tl ->
      if GNG.X25519? entry.GKE.group
      then Some (entry.GKE.key_exchange <: Seq.seq U8.t)
      else kse_list_find_x25519 tl

/// Walk the ClientHello extensions for the first key_share extension and, in
/// it, the first X25519 entry's raw bytes (no length enforced here).
let rec ch_find_key_share (l: list GECH.extensionClientHello)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | GECH.Extension_data_key_share ks :: _ ->
      kse_list_find_x25519 (ks <: list GKE.keyShareEntry)
    | _ :: tl -> ch_find_key_share tl

let clientHello_key_share_x25519 (ch: GCH.clientHello) : option (Seq.seq U8.t) =
  ch_find_key_share (ch.GCH.extensions <: list GECH.extensionClientHello)

/// Walk the ClientHello extensions for the first signature_algorithms ext.
let rec ch_find_sig_algs (l: list GECH.extensionClientHello)
  : Tot (option (list GSS.signatureScheme)) (decreases l)
  = match l with
    | [] -> None
    | GECH.Extension_data_signature_algorithms sa :: _ ->
      Some (sa <: list GSS.signatureScheme)
    | _ :: tl -> ch_find_sig_algs tl

let clientHello_sig_algs (ch: GCH.clientHello) : option (list GSS.signatureScheme) =
  ch_find_sig_algs (ch.GCH.extensions <: list GECH.extensionClientHello)

(* ------------------------------------------------------------------ *)
(* ServerHello                                                         *)
(* ------------------------------------------------------------------ *)

/// True iff the ServerHello is a HelloRetryRequest.
let serverHello_is_hrr (sh: GSH.serverHello) : bool =
  GSHbody.HelloRetryRequest? sh.GSH.body

/// The 32-byte ServerHello random for an ordinary ServerHello (HRR has no
/// plain random, so None).
let serverHello_random (sh: GSH.serverHello) : option (Seq.lseq U8.t 32) =
  match sh.GSH.body with
  | GSHbody.HelloRetryRequest _ -> None
  | GSHbody.ServerHello_body_false r -> Some (r.GSHbody.tag <: Seq.lseq U8.t 32)

/// The ServerHelloBody carried by either arm of a ServerHello.
let serverHello_body (sh: GSH.serverHello) : option GSHB.serverHelloBody =
  match sh.GSH.body with
  | GSHbody.HelloRetryRequest b -> Some b
  | GSHbody.ServerHello_body_false r -> Some r.GSHbody.value

/// The negotiated cipher suite (from the ServerHelloBody).
let serverHello_cipher_suite (sh: GSH.serverHello) : option GCS.cipherSuite =
  match serverHello_body sh with
  | None -> None
  | Some body -> Some body.GSHB.cipher_suite

/// Find the X25519 key-share in the ServerHello extensions, if present.
let rec sh_find_key_share (l: list GESH.extensionServerHello)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | GESH.Extension_data_key_share kse :: _ ->
      if GNG.X25519? (kse <: GKE.keyShareEntry).GKE.group
      then Some ((kse <: GKE.keyShareEntry).GKE.key_exchange <: Seq.seq U8.t)
      else None
    | _ :: tl -> sh_find_key_share tl

let serverHello_key_share_x25519 (sh: GSH.serverHello) : option (Seq.seq U8.t) =
  match serverHello_body sh with
  | None -> None
  | Some body -> sh_find_key_share (body.GSHB.extensions <: list GESH.extensionServerHello)

/// The selected protocol version from the ServerHello supported_versions ext.
let rec sh_find_selected_version (l: list GESH.extensionServerHello)
  : Tot (option GPV.protocolVersion) (decreases l)
  = match l with
    | [] -> None
    | GESH.Extension_data_supported_versions sv :: _ ->
      Some (sv <: GPV.protocolVersion)
    | _ :: tl -> sh_find_selected_version tl

let serverHello_selected_version (sh: GSH.serverHello) : option GPV.protocolVersion =
  match serverHello_body sh with
  | None -> None
  | Some body -> sh_find_selected_version (body.GSHB.extensions <: list GESH.extensionServerHello)

(* ------------------------------------------------------------------ *)
(* EncryptedExtensions                                                 *)
(* ------------------------------------------------------------------ *)

/// Walk the EncryptedExtensions for the first ALPN extension and return the
/// bytes of its first protocol name, if any.
let rec ee_find_alpn (l: list GEEE.extensionEncryptedExtensions)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | GEEE.Extension_data_application_layer_protocol_negotiation a :: _ ->
      (match (a <: list GPN.protocolName) with
       | [] -> None
       | p :: _ -> Some (p <: Seq.seq U8.t))
    | _ :: tl -> ee_find_alpn tl

let encryptedExtensions_alpn (ee: GEE.encryptedExtensions) : option (Seq.seq U8.t) =
  ee_find_alpn (ee <: list GEEE.extensionEncryptedExtensions)

(* ------------------------------------------------------------------ *)
(* CertificateVerify                                                   *)
(* ------------------------------------------------------------------ *)

/// The signature scheme of a CertificateVerify.
let certificateVerify_scheme (cv: GCV.certificateVerify) : GSS.signatureScheme =
  cv.GCV.algorithm

/// The raw signature bytes of a CertificateVerify.
let certificateVerify_signature_bytes (cv: GCV.certificateVerify) : Seq.seq U8.t =
  cv.GCV.signature <: Seq.seq U8.t

(* ------------------------------------------------------------------ *)
(* Finished                                                            *)
(* ------------------------------------------------------------------ *)

/// The 32-byte verify_data of a Finished message (identity).
let finished_verify_data (f: GFin.finished) : Seq.lseq U8.t 32 =
  f
