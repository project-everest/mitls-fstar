module TLS13.Wire.Spec.Reveal.Handshake

(* Read-direction reveal layer for TLS13.Impl.Parser (phase3bd).

   Every name here is one the byte-level parser imports as [RV.*].  The
   ClientHello field synths/scanners and the per-constructor
   [synth_handshake_msg_of] reveals are thin re-exports of the corresponding
   [TLS13.Wire.Spec] (=[WS]) helpers; the reveals are re-stated over the
   generated wire records (the flat [M.*] records the old layer used were
   deleted, so e.g. [M.ClientHello] now wraps [GCH.clientHello] directly).  The
   list/cert-chain/ALPN scan helpers are pure and defined locally. *)

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module LP = LowParse.Spec
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GCS = TLS13.Wire.Generated.CipherSuite
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GSN = TLS13.Wire.Generated.ServerName
module GHN = TLS13.Wire.Generated.HostName
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GOV = TLS13.Wire.Generated.OfferedVersion
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN = TLS13.Wire.Generated.ProtocolName
module GCE = TLS13.Wire.Generated.CertificateEntry
module GFin = TLS13.Wire.Generated.Finished

(* ============================================================================ *)
(* handshake_synth: transparent re-export of the validating dispatch.           *)
(* ============================================================================ *)

let handshake_synth (h:GHS.handshake) : GTot (option M.handshake_msg) =
  WS.synth_handshake_msg_of h

(* ============================================================================ *)
(* ClientHello field synths/scanners: transparent re-exports of the WS helpers. *)
(* ============================================================================ *)

let reveal_synth_cipher_suites (l:list GCS.cipherSuite) : GTot (list T.cipher_suite) =
  WS.synth_cipher_suites l

let reveal_synth_sig_schemes (l:list GSS.signatureScheme) : GTot (list T.signature_scheme) =
  WS.synth_sig_schemes l

let reveal_ch_server_name (snl:list GSN.serverName) : GTot (option T.hostname) =
  WS.ch_server_name snl

let reveal_key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange)
  : GTot (option (B.bytes_of_len 32)) =
  WS.key_exchange_to_key32 ke

let reveal_ch_find_key_share (l:list GKSE.keyShareEntry)
  : GTot (option (B.bytes_of_len 32)) =
  WS.ch_find_key_share l

let reveal_ch_extensions
  (l:list GECH.extensionClientHello)
  (server_name:option T.hostname)
  (key_share:option (B.bytes_of_len 32))
  (saw_supported_versions:bool)
  (signature_schemes:list T.signature_scheme)
  : GTot (option (option T.hostname & option (B.bytes_of_len 32) & bool & list T.signature_scheme)) =
  WS.ch_extensions l server_name key_share saw_supported_versions signature_schemes

(* --- one-step reveals of the scanners --- *)

val lemma_reveal_synth_cipher_suites_nil (_:unit)
  : Lemma (reveal_synth_cipher_suites [] == [])

val lemma_reveal_synth_cipher_suites_cons (c:GCS.cipherSuite) (tl:list GCS.cipherSuite)
  : Lemma (reveal_synth_cipher_suites (c :: tl) ==
           WS.synth_cipher_suite c :: reveal_synth_cipher_suites tl)

val lemma_reveal_synth_sig_schemes_nil (_:unit)
  : Lemma (reveal_synth_sig_schemes [] == [])

val lemma_reveal_synth_sig_schemes_cons (s:GSS.signatureScheme) (tl:list GSS.signatureScheme)
  : Lemma (reveal_synth_sig_schemes (s :: tl) ==
           WS.synth_signature_scheme s :: reveal_synth_sig_schemes tl)

(* [synth_cipher_suite]/[synth_signature_scheme] are the identity, so mapping
   them over a list is the identity.  Needed to bridge the ClientHello scan
   (whose facts are stated over [reveal_synth_*]) with [is_valid_client_hello]
   (whose facts are stated over the raw [Sem.*] lists). *)
val lemma_reveal_synth_cipher_suites_id (l:list GCS.cipherSuite)
  : Lemma (ensures reveal_synth_cipher_suites l == l)

val lemma_reveal_synth_sig_schemes_id (l:list GSS.signatureScheme)
  : Lemma (ensures reveal_synth_sig_schemes l == l)

val lemma_reveal_ch_server_name_nil (_:unit)
  : Lemma (reveal_ch_server_name [] == None)

val lemma_reveal_ch_server_name_host (h:GHN.hostName) (tl:list GSN.serverName)
  : Lemma (reveal_ch_server_name (GSN.Name_host_name h :: tl) ==
           Some ((h <: B.bytes) <: T.hostname))

val lemma_reveal_key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange)
  : Lemma (reveal_key_exchange_to_key32 ke ==
           (if B.length (ke <: B.bytes) = 32
            then Some ((ke <: B.bytes) <: B.bytes_of_len 32)
            else None))

val lemma_reveal_ch_find_key_share_nil (_:unit)
  : Lemma (reveal_ch_find_key_share [] == None)

val lemma_reveal_ch_find_key_share_cons (e:GKSE.keyShareEntry) (tl:list GKSE.keyShareEntry)
  : Lemma (reveal_ch_find_key_share (e :: tl) ==
           (if GNG.X25519? e.GKSE.group
            then (match reveal_key_exchange_to_key32 e.GKSE.key_exchange with
                  | Some k -> Some k
                  | None -> reveal_ch_find_key_share tl)
            else reveal_ch_find_key_share tl))

(* Reveal lemmas for the Semantics first-X25519 (any length) finder, used by the
   commit-first key_share scan.  [kse_list_find_x25519] stops at the first X25519
   entry regardless of its length. *)
val lemma_reveal_kse_list_find_x25519_nil (_:unit)
  : Lemma (TLS13.Wire.Semantics.kse_list_find_x25519 [] == None)

val lemma_reveal_kse_list_find_x25519_cons (e:GKSE.keyShareEntry) (tl:list GKSE.keyShareEntry)
  : Lemma (TLS13.Wire.Semantics.kse_list_find_x25519 (e :: tl) ==
           (if GNG.X25519? e.GKSE.group
            then Some (e.GKSE.key_exchange <: Seq.seq U8.t)
            else TLS13.Wire.Semantics.kse_list_find_x25519 tl))

val lemma_reveal_ch_extensions_nil
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions [] sn ks sv ss == (if sv then Some (sn, ks, sv, ss) else None))

val lemma_reveal_ch_extensions_cons_sn
  (snl:GESN.extensionClientHello_extension_data_server_name)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions (GECH.Extension_data_server_name snl :: tl) sn ks sv ss ==
           (if Some? sn then reveal_ch_extensions tl sn ks sv ss
            else (match reveal_ch_server_name snl with
                  | Some name -> reveal_ch_extensions tl (Some name) ks sv ss
                  | None -> None)))

val lemma_reveal_ch_extensions_cons_sg
  (sgl:GESG.extensionClientHello_extension_data_supported_groups)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions (GECH.Extension_data_supported_groups sgl :: tl) sn ks sv ss ==
           reveal_ch_extensions tl sn ks sv ss)

val lemma_reveal_ch_extensions_cons_sa
  (ssl:GESA.extensionClientHello_extension_data_signature_algorithms)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions (GECH.Extension_data_signature_algorithms ssl :: tl) sn ks sv ss ==
           reveal_ch_extensions tl sn ks sv (if Nil? ss then reveal_synth_sig_schemes ssl else ss))

val lemma_reveal_ch_extensions_cons_ks
  (kscl:GESK.extensionClientHello_extension_data_key_share)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions (GECH.Extension_data_key_share kscl :: tl) sn ks sv ss ==
           (if Some? ks then reveal_ch_extensions tl sn ks sv ss
            else (match TLS13.Wire.Semantics.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
                  | Some raw -> if B.length raw = 32 then reveal_ch_extensions tl sn (Some (raw <: B.bytes_of_len 32)) sv ss else None
                  | None -> None)))

val lemma_reveal_ch_extensions_cons_sv
  (svl:GESV.extensionClientHello_extension_data_supported_versions)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (reveal_ch_extensions (GECH.Extension_data_supported_versions svl :: tl) sn ks sv ss ==
           (if FStar.List.Tot.mem GOV.Offered_TLS_1p3 svl
            then reveal_ch_extensions tl sn ks true ss
            else None))

val lemma_reveal_ch_extensions_cons_other
  (e:GECH.extensionClientHello)
  (tl:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma
    (requires
      not (GECH.Extension_data_server_name? e) /\
      not (GECH.Extension_data_supported_groups? e) /\
      not (GECH.Extension_data_signature_algorithms? e) /\
      not (GECH.Extension_data_key_share? e) /\
      not (GECH.Extension_data_supported_versions? e))
    (ensures reveal_ch_extensions (e :: tl) sn ks sv ss ==
             reveal_ch_extensions tl sn ks sv ss)

(* Per-constructor unfolding of the signature-scheme synth. *)
val lemma_synth_signature_scheme (s:GSS.signatureScheme)
  : Lemma (WS.synth_signature_scheme s ==
           (match s with
            | GSS.Ecdsa_secp256r1_sha256 -> T.Ecdsa_secp256r1_sha256
            | GSS.Rsa_pss_rsae_sha256 -> T.Rsa_pss_rsae_sha256
            | GSS.Ed25519 -> T.Ed25519
            | GSS.Unknown_signatureScheme v -> T.Unknown_signatureScheme v))

(* The ClientHello accept/reject gate. *)
val lemma_synth_client_hello_reveal (c:GCH.clientHello)
  : Lemma (WS.synth_client_hello c ==
           (if WS.clientHello_representable c then Some c else None))

(* Reveal [clientHello_representable] as the [ch_extensions] scan outcome plus the
   cipher-suite bound, re-stated over [reveal_ch_extensions] for the Parser. *)
val lemma_reveal_clientHello_representable_scan (c:GCH.clientHello)
  : Lemma (WS.clientHello_representable c ==
    ((match reveal_ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
                                 None None false [] with
      | Some (server_name, Some key_share, _, sig_schemes) ->
        Cons? sig_schemes &&
        FStar.List.Tot.length sig_schemes <= M.client_hello_max_signature_schemes &&
        (match server_name with
         | Some hostname -> B.length hostname <= M.client_hello_server_name_max_len
         | None -> true)
      | _ -> false) &&
     FStar.List.Tot.length (TLS13.Wire.Semantics.clientHello_cipher_suites c)
       <= M.client_hello_max_cipher_suites))

(* Parser bridge: re-export [WS.lemma_ch_extensions_connect] over
   [reveal_ch_extensions] — the accepted ClientHello's stored fields equal the
   first-wins [Sem] accessors that [is_valid_client_hello] compares against. *)
val lemma_reveal_ch_extensions_connect (c:GCH.clientHello)
  : Lemma (ensures (
    match reveal_ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
                               None None false [] with
    | Some (sn, ks, _, ss) ->
      sn == TLS13.Wire.Semantics.clientHello_server_name c /\
      (match ks with
       | Some k -> TLS13.Wire.Semantics.clientHello_key_share_x25519 c
                   == Some ((k <: B.bytes) <: Seq.seq U8.t)
       | None -> TLS13.Wire.Semantics.clientHello_key_share_x25519 c == None) /\
      (match TLS13.Wire.Semantics.clientHello_sig_algs c with
       | Some sas -> ss == reveal_synth_sig_schemes sas
       | None -> ss == [])
    | None -> True))

(* Parser bridge, [is_valid]-shaped: when the accepted ClientHello has a
   key_share and a *non-empty* sig_algs list, the stored scan fields equal the
   raw first-wins [Sem] accessors (the sig_algs identity is folded in here so
   the Parser needn't case-split to invoke it). *)
val lemma_reveal_ch_extensions_connect_valid (c:GCH.clientHello)
  : Lemma (ensures (
    match reveal_ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
                               None None false [] with
    | Some (sn, Some k, _, ss) ->
      TLS13.Wire.Semantics.clientHello_server_name c == sn /\
      TLS13.Wire.Semantics.clientHello_key_share_x25519 c
        == Some ((k <: B.bytes) <: Seq.seq U8.t) /\
      (Cons? ss ==> TLS13.Wire.Semantics.clientHello_sig_algs c == Some ss)
    | _ -> True))

(* ============================================================================ *)
(* Per-constructor reveals of [handshake_synth] (re-stated over the generated   *)
(* wire records; each equals the corresponding [synth_handshake_msg_of] arm).   *)
(* ============================================================================ *)

val lemma_handshake_synth_finished (b:GHS.handshake_body_finished)
  : Lemma (handshake_synth (GHS.Body_finished b) == Some (M.Finished b))

val lemma_handshake_synth_key_update (b:GHS.handshake_body_key_update)
  : Lemma (handshake_synth (GHS.Body_key_update b) == None)

val lemma_handshake_synth_client_hello (b:GHS.handshake_body_client_hello)
  : Lemma (handshake_synth (GHS.Body_client_hello b) ==
           (if WS.clientHello_representable b then Some (M.ClientHello b) else None))

val lemma_handshake_synth_certificate (b:GHS.handshake_body_certificate)
  : Lemma (handshake_synth (GHS.Body_certificate b) ==
           (if WS.certificate_representable (b <: GCert.certificate)
            then Some (M.Certificate (b <: GCert.certificate)) else None))

val lemma_handshake_synth_certificate_verify (b:GHS.handshake_body_certificate_verify)
  : Lemma (handshake_synth (GHS.Body_certificate_verify b) ==
           (if WS.certificateVerify_representable b then Some (M.CertificateVerify b) else None))

val lemma_handshake_synth_encrypted_extensions (b:GHS.handshake_body_encrypted_extensions)
  : Lemma (handshake_synth (GHS.Body_encrypted_extensions b) ==
           (if WS.encryptedExtensions_representable b then Some (M.EncryptedExtensions b) else None))

val lemma_handshake_synth_server_hello_hrr
  (b:GHS.handshake_body_server_hello) (shb:GSHBody.serverHelloBody)
  : Lemma (requires b.GSH.body == GSHB.HelloRetryRequest shb)
          (ensures handshake_synth (GHS.Body_server_hello b) == Some M.HelloRetryRequest)

val lemma_handshake_synth_server_hello_sh
  (b:GHS.handshake_body_server_hello) (sf:GSHB.serverHello_body_false)
  : Lemma (requires b.GSH.body == GSHB.ServerHello_body_false sf)
          (ensures handshake_synth (GHS.Body_server_hello b) ==
                   (if WS.serverHello_representable b then Some (M.ServerHello b) else None))

(* NOTE (restated): the agentic statement keyed the reject on a bad
   [legacy_version]; the current validating [synth_handshake_msg_of] does not
   inspect [legacy_version] (a HelloRetryRequest body always maps to
   [Some M.HelloRetryRequest]), so this reveal is keyed instead on the actual
   reject condition of the ServerHello arm: a non-representable
   ServerHello_body_false yields [None]. *)
val lemma_handshake_synth_server_hello_bad_version (b:GHS.handshake_body_server_hello)
  : Lemma (requires GSHB.ServerHello_body_false? b.GSH.body /\ not (WS.serverHello_representable b))
          (ensures handshake_synth (GHS.Body_server_hello b) == None)

(* ============================================================================ *)
(* Pure list-suffix helper for the extension scan loops.                        *)
(* ============================================================================ *)

val list_drop (#a:Type) (n:nat) (l:list a) : Tot (list a)

val lemma_list_drop_zero (#a:Type) (l:list a)
  : Lemma (ensures list_drop 0 l == l)

val lemma_list_drop_index (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length l)
          (ensures list_drop i l == FStar.List.Tot.index l i :: list_drop (i + 1) l)

val lemma_list_drop_length (#a:Type) (l:list a)
  : Lemma (ensures list_drop (FStar.List.Tot.length l) l == [])

(* ============================================================================ *)
(* ServerHello key-share scan.                                                  *)
(* ============================================================================ *)

(* The share the server selected, normalised to the widest supported group.  A
   scan result is a group tag together with the share zero-padded to 65 bytes,
   so that the accumulator's type -- and the runtime buffer it mirrors -- does
   not depend on which group the server picked.  The logical share is the
   [Sem.named_group_share_len]-byte prefix, recovered through the tag and never
   through the buffer's length. *)
let sh_kex_share = (GNG.namedGroup & B.bytes_of_len 65)

(* The share of a single [KeyShareEntry], accepted only at a group ATLAS
   offers and only at that group's exact length. *)
let reveal_key_exchange_to_share
  (g:GNG.namedGroup)
  (ke:GKSE.keyShareEntry_key_exchange)
  : GTot (option sh_kex_share)
  = match g with
    | GNG.X25519 ->
      if B.length (ke <: B.bytes) = 32
      then Some (g, TLS13.Crypto.Spec.pad_share_65 (ke <: B.bytes))
      else None
    | GNG.Secp256r1 ->
      if B.length (ke <: B.bytes) = 65
      then Some (g, TLS13.Crypto.Spec.pad_share_65 (ke <: B.bytes))
      else None
    | _ -> None

val reveal_sh_key_share
  (l:list GESH.extensionServerHello)
  (decided:bool)
  (key_share:option sh_kex_share)
  : GTot (option sh_kex_share)

val lemma_sh_key_share_nil
  (decided:bool)
  (key_share:option sh_kex_share)
  : Lemma (ensures reveal_sh_key_share [] decided key_share ==
                   (if decided then key_share else None))

val lemma_sh_key_share_cons
  (e:GESH.extensionServerHello)
  (tl:list GESH.extensionServerHello)
  (decided:bool)
  (key_share:option sh_kex_share)
  : Lemma (ensures reveal_sh_key_share (e :: tl) decided key_share ==
      (if decided then key_share
       else (match e with
             | GESH.Extension_data_key_share kse ->
               reveal_sh_key_share tl true
                 (reveal_key_exchange_to_share kse.GKSE.group kse.GKSE.key_exchange)
             | _ -> reveal_sh_key_share tl false None)))

(* Once [decided], the scan short-circuits to the committed [key_share]. *)
val lemma_sh_key_share_decided
  (l:list GESH.extensionServerHello)
  (key_share:option sh_kex_share)
  : Lemma (ensures reveal_sh_key_share l true key_share == key_share)

(* Bridge: the first-wins [reveal_sh_key_share] agrees with the first-wins
   [Sem.sh_find_kex_share], which applies the same per-group length gate. *)
val lemma_reveal_sh_key_share_connect (l:list GESH.extensionServerHello)
  : Lemma (reveal_sh_key_share l false None ==
           (match TLS13.Wire.Semantics.sh_find_kex_share l with
            | Some (g, k) -> Some (g, TLS13.Crypto.Spec.pad_share_65 k)
            | None -> None))

(* ============================================================================ *)
(* Certificate chain helpers.                                                   *)
(* ============================================================================ *)

val reveal_synth_cert_chain (l:list GCE.certificateEntry) : GTot (list B.bytes)

val reveal_cert_chain_total_bytes (chain:list B.bytes) : GTot nat

val lemma_synth_cert_chain_nil (_:unit)
  : Lemma (ensures reveal_synth_cert_chain [] == [])

val lemma_synth_cert_chain_cons (e:GCE.certificateEntry) (tl:list GCE.certificateEntry)
  : Lemma (ensures reveal_synth_cert_chain (e :: tl) ==
                   (e.GCE.cert_data <: B.bytes) :: reveal_synth_cert_chain tl)

val lemma_synth_cert_chain_length (l:list GCE.certificateEntry)
  : Lemma (ensures FStar.List.Tot.length (reveal_synth_cert_chain l) ==
                   FStar.List.Tot.length l)

val lemma_cert_chain_total_bytes_nil (_:unit)
  : Lemma (ensures reveal_cert_chain_total_bytes [] == 0)

val lemma_cert_chain_total_bytes_snoc (chain:list B.bytes) (x:B.bytes)
  : Lemma (ensures reveal_cert_chain_total_bytes (FStar.List.Tot.append chain [x]) ==
                   reveal_cert_chain_total_bytes chain + B.length x)

val lemma_cert_chain_total_bytes_prefix_le
  (prefix:list B.bytes) (x:B.bytes) (rest:list B.bytes)
  : Lemma (ensures reveal_cert_chain_total_bytes prefix + B.length x <=
                   reveal_cert_chain_total_bytes
                     (FStar.List.Tot.append prefix (x :: rest)))

(* ---- Certificate representability connect (scan <-> synth) --------------- *)

(* When the Parser's chain scan reports the chain over-long (> 8 entries) or
   over-size (> 32768 bytes), the Certificate message is not representable, so
   the validating [handshake_synth] rejects it. *)
val lemma_handshake_synth_certificate_none (b:GHS.handshake_body_certificate)
  : Lemma
    (requires
      FStar.List.Tot.length (reveal_synth_cert_chain (b.GCert.certificate_list))
        > M.certificate_chain_max_entries \/
      reveal_cert_chain_total_bytes (reveal_synth_cert_chain (b.GCert.certificate_list))
        > M.certificate_chain_max_bytes)
    (ensures handshake_synth (GHS.Body_certificate b) == None)

(* When the scan reports the chain within bounds, the message is representable:
   [handshake_synth] accepts it, and the scanned chain equals the [Sem] entries
   list (so [is_valid_certificate_msg] can be discharged over it). *)
val lemma_handshake_synth_certificate_some (b:GHS.handshake_body_certificate)
  : Lemma
    (requires
      FStar.List.Tot.length (reveal_synth_cert_chain (b.GCert.certificate_list))
        <= M.certificate_chain_max_entries /\
      reveal_cert_chain_total_bytes (reveal_synth_cert_chain (b.GCert.certificate_list))
        <= M.certificate_chain_max_bytes)
    (ensures
      handshake_synth (GHS.Body_certificate b) ==
        Some (M.Certificate (b <: GCert.certificate)) /\
      reveal_synth_cert_chain (b.GCert.certificate_list) ==
        TLS13.Wire.Semantics.certificate_entries (b <: GCert.certificate))

(* ============================================================================ *)
(* EncryptedExtensions ALPN scan.                                               *)
(*                                                                              *)
(* Re-typed (the flat [M.encrypted_extensions] record was deleted): a valid EE  *)
(* list yields [Some negotiated_alpn], where the inner [option] is the first    *)
(* ALPN name (None if no ALPN extension present).  An ALPN extension with an     *)
(* empty protocol-name list rejects the message ([None]).                       *)
(* ============================================================================ *)

val reveal_alpn_first_name
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : GTot (option B.bytes)

val reveal_synth_encrypted_extensions (l:list GEEE.extensionEncryptedExtensions)
  : GTot (option (option B.bytes))

val lemma_synth_ee_nil (_:unit)
  : Lemma (ensures reveal_synth_encrypted_extensions [] == Some None)

val lemma_synth_ee_cons_non_alpn
  (e:GEEE.extensionEncryptedExtensions)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires not (GEEE.Extension_data_application_layer_protocol_negotiation? e))
    (ensures reveal_synth_encrypted_extensions (e :: tl)
             == reveal_synth_encrypted_extensions tl)

val lemma_synth_ee_cons_alpn
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (ensures reveal_synth_encrypted_extensions
               (GEEE.Extension_data_application_layer_protocol_negotiation pnl :: tl)
             == (match reveal_alpn_first_name pnl with
                 | Some name -> Some (Some name)
                 | None -> None))

val lemma_alpn_first_name_index0
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : Lemma
    (requires FStar.List.Tot.length (pnl <: list GPN.protocolName) > 0)
    (ensures reveal_alpn_first_name pnl ==
             Some (FStar.List.Tot.index (pnl <: list GPN.protocolName) 0 <: B.bytes))

val lemma_alpn_first_name_nil
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : Lemma (requires (pnl <: list GPN.protocolName) == [])
          (ensures reveal_alpn_first_name pnl == None)

(* Bridge: when the EE ALPN scan succeeds ([Some?]), its payload equals the
   first-wins [Sem.encryptedExtensions_alpn] and the ALPN name (if any) is
   <= 255 bytes — i.e. the EE is representable. *)
val lemma_reveal_ee_connect (b:GEE.encryptedExtensions)
  : Lemma
    (requires Some? (reveal_synth_encrypted_extensions
                      (b <: list GEEE.extensionEncryptedExtensions)))
    (ensures
      Some?.v (reveal_synth_encrypted_extensions
                (b <: list GEEE.extensionEncryptedExtensions))
        == TLS13.Wire.Semantics.encryptedExtensions_alpn b /\
      (match TLS13.Wire.Semantics.encryptedExtensions_alpn b with
       | Some a -> B.length a <= M.client_hello_server_name_max_len
       | None -> true))

(* ============================================================================ *)
(* Byte-level [parse_tls_message] arm reveals (thin re-exports of WS).          *)
(* ============================================================================ *)

(* [lemma_ptm_alert] is intentionally NOT declared here: the branch provides it
   in TLS13.Wire.Spec.Reveal.Alert (re-exported by the aggregator). *)

val lemma_ptm_handshake_some (fragment:B.bytes) (v:GHS.handshake) (m:M.handshake_msg)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, B.length fragment) /\
              handshake_synth v == Some m)
    (ensures WS.parse_tls_message T.Handshake fragment == Some (M.TlsHandshake m))

val lemma_ptm_handshake_fallback (fragment:B.bytes)
  : Lemma
    (requires WS.parse_handshake fragment == None)
    (ensures WS.parse_tls_message T.Handshake fragment ==
      (match WS.parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match WS.parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

val lemma_parse_key_update_def (input:B.bytes)
  : Lemma (ensures WS.parse_key_update input ==
      (if B.length input = 5 &&
          U8.v (Seq.index input 0) = 24 &&
          U8.v (Seq.index input 1) = 0 &&
          U8.v (Seq.index input 2) = 0 &&
          U8.v (Seq.index input 3) = 1
       then (match U8.v (Seq.index input 4) with
             | 0 -> Some M.UpdateNotRequested
             | 1 -> Some M.UpdateRequested
             | _ -> None)
       else None))

val lemma_parse_ignored_post_handshake_def (input:B.bytes)
  : Lemma (ensures WS.parse_ignored_post_handshake input ==
      (if B.length input >= 4 &&
          U8.v (Seq.index input 0) = 4 &&
          (U8.v (Seq.index input 1) * 65536 +
           U8.v (Seq.index input 2) * 256 +
           U8.v (Seq.index input 3)) + 4 = B.length input
       then Some (Seq.slice input 4 (B.length input))
       else None))

val lemma_parse_handshake_none_of_lp_none (fragment:B.bytes)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures WS.parse_handshake fragment == None)

val lemma_parse_handshake_none_of_synth_none
  (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              handshake_synth v == None)
    (ensures WS.parse_handshake fragment == None)

(* ============================================================================ *)
(* Build-direction serialize reveals (branch-local): per-constructor           *)
(* definitional unfolding of [WS.serialize_handshake] onto the generated        *)
(* QuackyDucky handshake serializer, consumed by TLS13.Impl.Serializer.Handshake.*)
(* ============================================================================ *)

val lemma_serialize_handshake_client_hello (ch:GCH.clientHello) :
  Lemma (Seq.equal (WS.serialize_handshake (M.ClientHello ch))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch)))

val lemma_serialize_handshake_server_hello (sh:GSH.serverHello) :
  Lemma (Seq.equal (WS.serialize_handshake (M.ServerHello sh))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello sh)))

val lemma_serialize_handshake_encrypted_extensions (ee:GEE.encryptedExtensions) :
  Lemma (Seq.equal (WS.serialize_handshake (M.EncryptedExtensions ee))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions ee)))

val lemma_serialize_handshake_certificate (cert:GCert.certificate) :
  Lemma (requires GCert.certificate_bytesize cert <= 16777215)
        (ensures Seq.equal (WS.serialize_handshake (M.Certificate cert))
                   (LP.serialize GHS.handshake_serializer
                      (GHS.Body_certificate (cert <: GHS.handshake_body_certificate))))

val lemma_serialize_handshake_certificate_verify (cv:GCV.certificateVerify) :
  Lemma (Seq.equal (WS.serialize_handshake (M.CertificateVerify cv))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify cv)))

val lemma_serialize_handshake_finished (fin:GFin.finished) :
  Lemma (Seq.equal (WS.serialize_handshake (M.Finished fin))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_finished fin)))
