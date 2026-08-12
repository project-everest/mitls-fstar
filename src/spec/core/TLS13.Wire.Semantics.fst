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
module C   = TLS13.Crypto.Spec

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
module GCert   = TLS13.Wire.Generated.Certificate
module GCertE  = TLS13.Wire.Generated.CertificateEntry

#set-options "--z3rlimit 5 --fuel 1 --ifuel 1"

(* ------------------------------------------------------------------ *)
(* ClientHello                                                         *)
(* ------------------------------------------------------------------ *)

/// The 32-byte ClientHello random.
let clientHello_random (ch: GCH.clientHello) : Seq.lseq U8.t 32 =
  ch.GCH.random

/// The legacy_session_id the client offered.  TLS 1.3 ignores it semantically,
/// but a server running in middlebox-compatibility mode (RFC 8446 D.4) MUST
/// echo it verbatim in its ServerHello, so it has to be readable here.
let clientHello_legacy_session_id (ch: GCH.clientHello) : Seq.seq U8.t =
  ch.GCH.legacy_session_id <: Seq.seq U8.t

/// The legacy_session_id, normalised to exactly 32 bytes.
///
/// RFC 8446 D.4 (middlebox compatibility) clients -- i.e. every browser and
/// curl -- always send a 32-byte legacy_session_id, and the implementation
/// fixes the width at 32 so the whole ClientHello/ServerHello wire image stays
/// a constant size.  A ClientHello carrying a different session-id length is
/// still parsed (it is legal TLS), but is normalised to all-zeros here, so the
/// ServerHello echoes zeros and such a client will reject the handshake.
let session_id_32 (s: Seq.seq U8.t) : (r:Seq.seq U8.t { Seq.length r == 32 }) =
  if Seq.length s = 32 then s else Seq.create 32 0uy

let clientHello_session_id_32 (ch: GCH.clientHello) : (r:Seq.seq U8.t { Seq.length r == 32 }) =
  session_id_32 (clientHello_legacy_session_id ch)

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

/// The secp256r1 entry of the ClientHello key_share extension.  A ClientHello
/// may offer several groups, so this walks the same list looking for a
/// different tag; offering both leaves `clientHello_key_share_x25519` intact.
let rec kse_list_find_secp256r1 (l: list GKE.keyShareEntry)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | entry :: tl ->
      if GNG.Secp256r1? entry.GKE.group
      then Some (entry.GKE.key_exchange <: Seq.seq U8.t)
      else kse_list_find_secp256r1 tl

let rec ch_find_key_share_secp256r1 (l: list GECH.extensionClientHello)
  : Tot (option (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> None
    | GECH.Extension_data_key_share ks :: _ ->
      kse_list_find_secp256r1 (ks <: list GKE.keyShareEntry)
    | _ :: tl -> ch_find_key_share_secp256r1 tl

let clientHello_key_share_secp256r1 (ch: GCH.clientHello) : option (Seq.seq U8.t) =
  ch_find_key_share_secp256r1 (ch.GCH.extensions <: list GECH.extensionClientHello)

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

/// The session id the server echoed back (RFC 8446 D.4 middlebox compat).
let serverHello_legacy_session_id_echo (sh: GSH.serverHello) : option (Seq.seq U8.t) =
  match serverHello_body sh with
  | None -> None
  | Some body -> Some (body.GSHB.legacy_session_id_echo <: Seq.seq U8.t)

/// The echoed legacy_session_id, normalised to exactly 32 bytes (see
/// [clientHello_session_id_32]).
let serverHello_session_id_echo_32 (sh: GSH.serverHello)
  : (r:Seq.seq U8.t { Seq.length r == 32 }) =
  match serverHello_legacy_session_id_echo sh with
  | None -> Seq.create 32 0uy
  | Some s -> session_id_32 s

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

/// The group the server named in its key_share extension, and the share it
/// paired with that group.  The group is read off the wire rather than guessed
/// from the share's length: a `KeyShareEntry` is a `NamedGroup` together with
/// an opaque `key_exchange`, and the server's choice is exactly that tag.
let rec sh_find_key_share_entry (l: list GESH.extensionServerHello)
  : Tot (option GKE.keyShareEntry) (decreases l)
  = match l with
    | [] -> None
    | GESH.Extension_data_key_share kse :: _ -> Some (kse <: GKE.keyShareEntry)
    | _ :: tl -> sh_find_key_share_entry tl

let serverHello_key_share_group (sh: GSH.serverHello) : option GNG.namedGroup =
  match serverHello_body sh with
  | None -> None
  | Some body ->
    (match sh_find_key_share_entry (body.GSHB.extensions <: list GESH.extensionServerHello) with
     | None -> None
     | Some kse -> Some kse.GKE.group)

let serverHello_key_share_bytes (sh: GSH.serverHello) : option (Seq.seq U8.t) =
  match serverHello_body sh with
  | None -> None
  | Some body ->
    (match sh_find_key_share_entry (body.GSHB.extensions <: list GESH.extensionServerHello) with
     | None -> None
     | Some kse -> Some (kse.GKE.key_exchange <: Seq.seq U8.t))

/// The secp256r1 share, when that is what the server picked.
let serverHello_key_share_secp256r1 (sh: GSH.serverHello) : option (Seq.seq U8.t) =
  match serverHello_key_share_group sh, serverHello_key_share_bytes sh with
  | Some GNG.Secp256r1, Some k -> Some k
  | _, _ -> None

/// The share length ATLAS requires of each group it offers.  This is a
/// *validation* rule -- "an X25519 entry must carry 32 bytes" -- not a way of
/// recovering the group: the group always comes from the entry's `NamedGroup`.
let named_group_share_len (g: GNG.namedGroup) : nat =
  match g with
  | GNG.X25519 -> 32
  | GNG.Secp256r1 -> 65
  | _ -> 0

/// A share ATLAS can hold in its 65-byte key-share buffers: exactly the widths
/// of the two groups it offers, so that `C.pad_share_65` applies directly.
let offered_share = C.kex_public_any

/// The key-exchange group a `NamedGroup` denotes.  ATLAS offers exactly two;
/// any other group is rejected before this is consulted (`sh_find_kex_share`
/// returns `None` for it), so the catch-all is never the negotiated answer.
let kex_group_of_named_group (g: GNG.namedGroup) : C.kex_group =
  match g with
  | GNG.Secp256r1 -> C.KexP256
  | _ -> C.KexX25519

/// The first `key_share` entry of a ServerHello extension list, accepted only
/// at a group ATLAS offers and only at that group's exact share length.
/// First-wins: a leading `key_share` at any other group rejects outright, it
/// does not scan on.
let rec sh_find_kex_share (l: list GESH.extensionServerHello)
  : Tot (option (GNG.namedGroup & offered_share)) (decreases l)
  = match l with
    | [] -> None
    | GESH.Extension_data_key_share kse :: _ ->
      let g = (kse <: GKE.keyShareEntry).GKE.group in
      let k = ((kse <: GKE.keyShareEntry).GKE.key_exchange <: Seq.seq U8.t) in
      (match g with
       | GNG.X25519 -> if Seq.length k = 32 then Some (g, k) else None
       | GNG.Secp256r1 -> if Seq.length k = 65 then Some (g, k) else None
       | _ -> None)
    | _ :: tl -> sh_find_kex_share tl

/// The negotiated group and share of a ServerHello, `None` unless the server
/// selected one of the two groups ATLAS offers at its exact length.
let serverHello_kex_share (sh: GSH.serverHello)
  : option (GNG.namedGroup & offered_share) =
  match serverHello_body sh with
  | None -> None
  | Some body -> sh_find_kex_share (body.GSHB.extensions <: list GESH.extensionServerHello)

/// The accepted groups and their exact lengths, made visible to callers that
/// only hold `serverHello_kex_share`.
let rec lemma_sh_find_kex_share_shape (l: list GESH.extensionServerHello)
  : Lemma
      (ensures (match sh_find_kex_share l with
                | Some (g, k) ->
                  (g == GNG.X25519 /\ Seq.length k == 32) \/
                  (g == GNG.Secp256r1 /\ Seq.length k == 65)
                | None -> True))
      (decreases l)
  = match l with
    | [] -> ()
    | GESH.Extension_data_key_share _ :: _ -> ()
    | _ :: tl -> lemma_sh_find_kex_share_shape tl

let lemma_serverHello_kex_share_shape (sh: GSH.serverHello)
  : Lemma
      (ensures (match serverHello_kex_share sh with
                | Some (g, k) ->
                  (g == GNG.X25519 /\ Seq.length k == 32) \/
                  (g == GNG.Secp256r1 /\ Seq.length k == 65)
                | None -> True))
      [SMTPat (serverHello_kex_share sh)]
  = match serverHello_body sh with
    | None -> ()
    | Some body ->
      lemma_sh_find_kex_share_shape (body.GSHB.extensions <: list GESH.extensionServerHello)

/// `sh_find_key_share` is the X25519 special case of `sh_find_kex_share`: both
/// stop at the first `key_share` extension, and the former succeeds exactly
/// when that entry names X25519.  A 32-byte X25519 share therefore satisfies
/// the general accessor's length rule.
let rec lemma_sh_find_kex_share_x25519 (l: list GESH.extensionServerHello)
  : Lemma
      (requires (match sh_find_key_share l with
                 | Some k -> Seq.length k == 32
                 | None -> True))
      (ensures (match sh_find_key_share l with
                | Some k -> sh_find_kex_share l == Some (GNG.X25519, (k <: offered_share))
                | None -> True))
      (decreases l)
  = match l with
    | [] -> ()
    | GESH.Extension_data_key_share _ :: _ -> ()
    | _ :: tl -> lemma_sh_find_kex_share_x25519 tl

let lemma_serverHello_kex_share_x25519 (sh: GSH.serverHello)
  : Lemma
      (requires (match serverHello_key_share_x25519 sh with
                 | Some k -> Seq.length k == 32
                 | None -> True))
      (ensures (match serverHello_key_share_x25519 sh with
                | Some k -> serverHello_kex_share sh == Some (GNG.X25519, (k <: offered_share))
                | None -> True))
      [SMTPat (serverHello_key_share_x25519 sh)]
  = match serverHello_body sh with
    | None -> ()
    | Some body ->
      lemma_sh_find_kex_share_x25519 (body.GSHB.extensions <: list GESH.extensionServerHello)

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

(* ------------------------------------------------------------------ *)
(* Certificate                                                         *)
(* ------------------------------------------------------------------ *)

/// The raw cert_data bytes of each entry of a certificate_list.  The wire
/// CertificateEntry carries a vlbytes [cert_data] (the raw certificate DER)
/// plus per-entry extensions; downstream code compares these raw DER blobs
/// against the configured leaf certificate.
let rec cert_entries_data (l: list GCertE.certificateEntry)
  : Tot (list (Seq.seq U8.t)) (decreases l)
  = match l with
    | [] -> []
    | e :: tl -> (e.GCertE.cert_data <: Seq.seq U8.t) :: cert_entries_data tl

/// The list of raw certificate DER blobs carried by a Certificate message,
/// one per CertificateEntry, in wire order (mirrors the old M.certificate_msg
/// [chain : X.cert_chain] projection field).
let certificate_entries (c: GCert.certificate) : list (Seq.seq U8.t) =
  cert_entries_data (c.GCert.certificate_list <: list GCertE.certificateEntry)
