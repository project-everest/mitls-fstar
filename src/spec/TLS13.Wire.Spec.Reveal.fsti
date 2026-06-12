module TLS13.Wire.Spec.Reveal

(**
  Spec-reveal helper for the M/L parser implementation (TLS13.Impl.Parser).

  TLS13.Wire.Spec exposes [parse_tls_message]/[parse_record]/[parse_handshake]
  as abstract vals, and only one behavioural lemma
  ([lemma_parse_tls_message_round_trip]).  The implementation in
  TLS13.Impl.Parser needs the per-content-type definitional behaviour of
  [parse_tls_message] (and the connection between the QuackyDucky handshake
  parser and [parse_handshake]) to discharge its post-conditions.

  TLS13.Impl.Parser cannot [friend TLS13.Wire.Spec] itself, because its
  interface transitively depends on TLS13.Wire.Spec (through
  TLS13.Impl.Client.Types / TLS13.Impl.Messages) as a non-friend dependence.
  This module instead friends TLS13.Wire.Spec and re-exports the needed facts
  as lemmas referring only to spec/generated types (B/M/T/GHS), which
  TLS13.Impl.Parser then consumes as an ordinary non-friend dependence.
*)

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GSS = TLS13.Wire.Generated.SignatureScheme
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN = TLS13.Wire.Generated.ProtocolName
module LP = LowParse.Spec

(* --- non-handshake content-type arms ------------------------------------ *)

val lemma_ptm_change_cipher_spec (fragment:B.bytes)
  : Lemma (ensures WS.parse_tls_message T.ChangeCipherSpec fragment ==
                   (if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
                    then Some M.TlsChangeCipherSpec
                    else None))

val lemma_ptm_application_data (fragment:B.bytes)
  : Lemma (ensures WS.parse_tls_message T.ApplicationData fragment ==
                   Some (M.TlsApplicationData fragment))

(* parse_plaintext strips the trailing content-type byte, so the recovered
   fragment is exactly one byte shorter than the decrypted TLSInnerPlaintext. *)
val lemma_parse_plaintext_fragment_len (input:B.bytes)
  : Lemma (ensures (match WS.parse_plaintext input with
                    | Some pt -> B.length pt.M.fragment + 1 == B.length input
                    | None -> True))

val lemma_ptm_alert (fragment:B.bytes)
  : Lemma (ensures (
      if B.length fragment <> 2
      then WS.parse_tls_message T.Alert fragment == None
      else
        WS.parse_tls_message T.Alert fragment ==
          (match U8.v (Seq.index fragment 1) with
           | 0   -> Some (M.TlsAlert T.CloseNotify)
           | 10  -> Some (M.TlsAlert T.UnexpectedMessage)
           | 20  -> Some (M.TlsAlert T.BadRecordMac)
           | 40  -> Some (M.TlsAlert T.HandshakeFailure)
           | 46  -> Some (M.TlsAlert T.CertificateUnknown)
           | 47  -> Some (M.TlsAlert T.IllegalParameter)
           | 50  -> Some (M.TlsAlert T.DecodeError)
           | 51  -> Some (M.TlsAlert T.DecryptError)
           | 70  -> Some (M.TlsAlert T.ProtocolVersion)
           | 110 -> Some (M.TlsAlert T.UnsupportedExtension)
           | _   -> None)))

(* --- handshake arm: connect the QD parser to parse_tls_message ---------- *)

(* Re-export of the internal [synth_handshake_msg_of]. *)
val handshake_synth (h:GHS.handshake) : GTot (option M.handshake_msg)

(* Re-export of the internal cipher-suite / signature-scheme synths so the
   implementation can name the high-level field values. *)
val synth_cipher_suite (c:GCS.cipherSuite) : T.cipher_suite

val synth_signature_scheme (s:GSS.signatureScheme) : T.signature_scheme

(* The signature-scheme synth maps the generated enum to the abstract type
   per-constructor; exposed so the implementation can pick a matching wire u16. *)
val lemma_synth_signature_scheme (s:GSS.signatureScheme)
  : Lemma (ensures synth_signature_scheme s ==
                   (match s with
                    | GSS.Ecdsa_secp256r1_sha256 -> T.EcdsaSecp256r1Sha256
                    | GSS.Rsa_pss_rsae_sha256 -> T.RsaPssRsaeSha256
                    | GSS.Ed25519 -> T.Ed25519
                    | GSS.Unknown_signatureScheme v -> T.UnsupportedSignatureScheme (U16.v v)))

(* If the generated handshake parser yields [v] consuming the whole fragment
   and [handshake_synth v == Some m], then [parse_tls_message] of a Handshake
   record produces exactly [TlsHandshake m]. *)
val lemma_ptm_handshake_some (fragment:B.bytes) (v:GHS.handshake) (m:M.handshake_msg)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, B.length fragment) /\
              handshake_synth v == Some m)
    (ensures WS.parse_tls_message T.Handshake fragment == Some (M.TlsHandshake m))

(* Per-constructor reveals of [handshake_synth]. *)

val lemma_handshake_synth_finished (b:GHS.handshake_body_finished)
  : Lemma (ensures handshake_synth (GHS.Body_finished b) ==
                   Some (M.Finished ({ M.verify_data = (b <: B.bytes_of_len 32) })))

(* CertificateVerify: the synth is guarded by the 4096-byte signature bound.
   When the wire signature fits, the M value carries the verbatim wire body
   (the serialization of the parsed handshake value). *)
val lemma_handshake_synth_certificate_verify (b:GHS.handshake_body_certificate_verify)
  : Lemma (ensures handshake_synth (GHS.Body_certificate_verify b) ==
                   (if B.length (b.GCV.signature <: B.bytes) <= M.signature_max_len
                    then Some (M.CertificateVerify ({
                           M.scheme = synth_signature_scheme b.GCV.algorithm;
                           M.signature = (b.GCV.signature <: B.bytes);
                           M.body = LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify b) }))
                    else None))

(* Key_update handshake values never synth to a handshake message: the spec
   routes them through the byte-level [parse_key_update] fallback instead. *)
val lemma_handshake_synth_key_update (b:GHS.handshake_body_key_update)
  : Lemma (ensures handshake_synth (GHS.Body_key_update b) == None)

(* --- byte-level fallback formats (outside the QD handshake grammar) ------ *)

(* Re-export of the internal [parse_ignored_post_handshake] (not in the frozen
   TLS13.Wire.Spec interface). *)
val reveal_parse_ignored_post_handshake (input:B.bytes) : GTot (option B.bytes)

(* Byte-level definition of [parse_key_update]: a 5-byte [24;0;0;1;req] envelope. *)
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

(* Byte-level definition of [parse_ignored_post_handshake]: a msg_type-4 envelope
   with a 3-byte length field. *)
val lemma_parse_ignored_post_handshake_def (input:B.bytes)
  : Lemma (ensures reveal_parse_ignored_post_handshake input ==
      (if B.length input >= 4 &&
          U8.v (Seq.index input 0) = 4 &&
          (U8.v (Seq.index input 1) * 65536 +
           U8.v (Seq.index input 2) * 256 +
           U8.v (Seq.index input 3)) + 4 = B.length input
       then Some (Seq.slice input 4 (B.length input))
       else None))

(* --- handshake-arm routing into the byte-level fallbacks ----------------- *)

(* If the QD handshake parser does not parse [fragment], then [parse_handshake]
   fails too. *)
val lemma_parse_handshake_none_of_lp_none (fragment:B.bytes)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures WS.parse_handshake fragment == None)

(* If the QD handshake parser yields [v] but [handshake_synth v == None], then
   [parse_handshake] fails. *)
val lemma_parse_handshake_none_of_synth_none (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              handshake_synth v == None)
    (ensures WS.parse_handshake fragment == None)

(* When [parse_handshake] fails, [parse_tls_message] of a Handshake record is the
   byte-level key_update / ignored-post-handshake fallback. *)
val lemma_ptm_handshake_fallback (fragment:B.bytes)
  : Lemma
    (requires WS.parse_handshake fragment == None)
    (ensures WS.parse_tls_message T.Handshake fragment ==
      (match WS.parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match reveal_parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

(* If the QD handshake parser succeeds but does not consume the whole fragment,
   then [parse_tls_message] of a Handshake record is None. The proof routes
   through [TLS13.Wire.Spec.NonExact] (which friends the generated handshake
   grammar to expose the message-type tag byte). *)

(* --- EncryptedExtensions: per-constructor synth reveals ----------------- *)

(* Re-export of the internal [synth_encrypted_extensions] (scan for the first
   ALPN extension). *)
val reveal_synth_encrypted_extensions (l:list GEEE.extensionEncryptedExtensions)
  : GTot (option M.encrypted_extensions)

(* Re-export of the internal [alpn_first_name] (first protocol name of an ALPN
   extension, as raw bytes). *)
val reveal_alpn_first_name
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : GTot (option B.bytes)

(* The EncryptedExtensions arm of [synth_handshake_msg_of]: when the extension
   list synthesises an [encrypted_extensions], the carried M value's body is
   overridden with the verbatim wire bytes of the parsed handshake value. *)
val lemma_handshake_synth_encrypted_extensions (b:GHS.handshake_body_encrypted_extensions)
  : Lemma (ensures handshake_synth (GHS.Body_encrypted_extensions b) ==
                   (match reveal_synth_encrypted_extensions b with
                    | Some x -> Some (M.EncryptedExtensions ({ x with
                        M.body = LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions b) }))
                    | None -> None))

(* The empty extension list synthesises an EncryptedExtensions with no ALPN. *)
val lemma_synth_ee_nil (_:unit)
  : Lemma (ensures reveal_synth_encrypted_extensions []
                   == Some ({ M.negotiated_alpn = None; M.body = TLS13.Bytes.empty }))

(* A non-ALPN head extension is skipped: the synth of the whole list equals the
   synth of the tail. *)
val lemma_synth_ee_cons_non_alpn
  (e:GEEE.extensionEncryptedExtensions)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires not (GEEE.Extension_data_application_layer_protocol_negotiation? e))
    (ensures reveal_synth_encrypted_extensions (e :: tl)
             == reveal_synth_encrypted_extensions tl)

(* An ALPN head extension fixes the result to the first protocol name. *)
val lemma_synth_ee_cons_alpn
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (ensures reveal_synth_encrypted_extensions
               (GEEE.Extension_data_application_layer_protocol_negotiation pnl :: tl)
             == (match reveal_alpn_first_name pnl with
                 | Some name -> Some ({ M.negotiated_alpn = Some name; M.body = TLS13.Bytes.empty })
                 | None -> None))

(* --- Pure list-suffix helpers for the EncryptedExtensions scan loop ------- *)

(* The [i]-th suffix of a list (a local [drop]: FStar.List.Tot has none). *)
let rec list_drop (#a:Type) (n:nat) (l:list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else (match l with | [] -> [] | _ :: tl -> list_drop (n - 1) tl)

(* Stepping the suffix exposes the head element at index [i]. *)
val lemma_list_drop_index (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length l)
          (ensures list_drop i l == FStar.List.Tot.index l i :: list_drop (i + 1) l)

(* Dropping the whole length leaves the empty list. *)
val lemma_list_drop_length (#a:Type) (l:list a)
  : Lemma (ensures list_drop (FStar.List.Tot.length l) l == [])

(* The first protocol name of a non-empty list is its head element's bytes. *)
val lemma_alpn_first_name_index0
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : Lemma
    (requires FStar.List.Tot.length (pnl <: list GPN.protocolName) > 0)
    (ensures reveal_alpn_first_name pnl ==
             Some (FStar.List.Tot.index (pnl <: list GPN.protocolName) 0 <: B.bytes))
