module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module GCE = TLS13.Wire.Generated.CertificateEntry
module GCert = TLS13.Wire.Generated.Certificate
module GCH = TLS13.Wire.Generated.ClientHello
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GHS = TLS13.Wire.Generated.Handshake
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GOV = TLS13.Wire.Generated.OfferedVersion
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSN = TLS13.Wire.Generated.ServerName
module GHN = TLS13.Wire.Generated.HostName
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GCTX = TLS13.Wire.Generated.TLSCiphertext
module GCTXF = TLS13.Wire.Generated.TLSCiphertext_encrypted_record
module LP = LowParse.Spec
module SHC = TLS13.ServerHello.Checks

(**
  Wire-level M/L boundary.

  The high-level model (M) is the pure message layer from TLS13.Messages,
  TLS13.Types, TLS13.Spec.StateMachine.ClientTrace, and TLS13.ConnectionLog.
  The low-level representation (L) for supported wire formats is the
  extraction-oriented TLS13.Impl.Messages layer plus byte-buffer streaming
  views where the active implementation is still header-first.

  Pulse parsers/serializers should be exposed through TLS13.Impl.Parser and
  TLS13.Impl.Serializer and state their correctness by referring to the parse_*
  and serialize_* functions in this module.  The older framing modules are
  implementation backends only, not the public M/L codec boundary.
**)

type parse_error = T.tls_error

val read_u16:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  GTot (n:nat{n < 65536})

val lemma_read_u16_definition:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  Lemma (read_u16 input pos ==
         U8.v (Seq.index input pos) * 256 +
         U8.v (Seq.index input (pos + 1)))

val read_u24:
  input:B.bytes ->
  pos:nat{pos + 3 <= B.length input} ->
  GTot nat

val lemma_read_u24_one:
  input:B.bytes{B.length input >= 4} ->
  Lemma (read_u24 input 1 == 1 <==>
         (U8.v (Seq.index input 1) == 0 /\
          U8.v (Seq.index input 2) == 0 /\
          U8.v (Seq.index input 3) == 1))

val parse_ignored_post_handshake:
  input:B.bytes ->
  GTot (option B.bytes)

val lemma_parse_ignored_post_handshake_def:
  input:B.bytes ->
  Lemma (parse_ignored_post_handshake input ==
    (if B.length input >= 4 &&
        U8.v (Seq.index input 0) = 4 &&
        (U8.v (Seq.index input 1) * 65536 +
         U8.v (Seq.index input 2) * 256 +
         U8.v (Seq.index input 3)) + 4 = B.length input
     then Some (Seq.slice input 4 (B.length input))
     else None))

val parse_key_update:
  input:B.bytes ->
  GTot (option M.key_update_request)

val lemma_parse_key_update_def:
  input:B.bytes ->
  Lemma (parse_key_update input ==
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

(* ============================================================================ *)
(* Read-direction spec helpers restored for TLS13.Impl.Parser (phase3bd).       *)
(*                                                                              *)
(* These are the field scanners and per-constructor [synth_handshake_msg_of]    *)
(* reveals that the byte-level parser needs.  The representability predicates    *)
(* (the accept/reject gate of the validating [synth_handshake_msg_of]) are      *)
(* exposed opaquely above so the reveal lemmas can name the gate; their bodies   *)
(* are unchanged in the .fst.                                                    *)
(* ============================================================================ *)

(* --- cipher-suite / signature-scheme synths (identity on the shared enums,
       since [T.cipher_suite == GCS.cipherSuite] and
       [T.signature_scheme == GSS.signatureScheme]). --- *)

val synth_cipher_suite:
  c:GCS.cipherSuite ->
  GTot T.cipher_suite

val lemma_synth_cipher_suite:
  c:GCS.cipherSuite ->
  Lemma (synth_cipher_suite c == c)

val synth_cipher_suites:
  l:list GCS.cipherSuite ->
  GTot (list T.cipher_suite)

val lemma_synth_cipher_suites_nil:
  unit ->
  Lemma (synth_cipher_suites [] == [])

val lemma_synth_cipher_suites_cons:
  c:GCS.cipherSuite ->
  tl:list GCS.cipherSuite ->
  Lemma (synth_cipher_suites (c :: tl) ==
         synth_cipher_suite c :: synth_cipher_suites tl)

val synth_signature_scheme:
  s:GSS.signatureScheme ->
  GTot T.signature_scheme

val synth_sig_schemes:
  l:list GSS.signatureScheme ->
  GTot (list T.signature_scheme)

val lemma_synth_sig_schemes_nil:
  unit ->
  Lemma (synth_sig_schemes [] == [])

val lemma_synth_sig_schemes_cons:
  s:GSS.signatureScheme ->
  tl:list GSS.signatureScheme ->
  Lemma (synth_sig_schemes (s :: tl) ==
         synth_signature_scheme s :: synth_sig_schemes tl)

(* --- ClientHello field scanners --- *)

val key_exchange_to_key32:
  ke:GKSE.keyShareEntry_key_exchange ->
  GTot (option (B.bytes_of_len 32))

val lemma_key_exchange_to_key32:
  ke:GKSE.keyShareEntry_key_exchange ->
  Lemma (key_exchange_to_key32 ke ==
    (let b : B.bytes = (ke <: B.bytes) in
     if B.length b = 32 then Some (b <: B.bytes_of_len 32) else None))

val ch_find_key_share:
  l:list GKSE.keyShareEntry ->
  GTot (option (B.bytes_of_len 32))

val lemma_ch_find_key_share_nil:
  unit ->
  Lemma (ch_find_key_share [] == None)

val lemma_ch_find_key_share_cons:
  e:GKSE.keyShareEntry ->
  tl:list GKSE.keyShareEntry ->
  Lemma (ch_find_key_share (e :: tl) ==
         (if GNG.X25519? e.GKSE.group
          then (match key_exchange_to_key32 e.GKSE.key_exchange with
                | Some k -> Some k
                | None -> ch_find_key_share tl)
          else ch_find_key_share tl))

val ch_server_name:
  snl:list GSN.serverName ->
  GTot (option T.hostname)

val lemma_ch_server_name_nil:
  unit ->
  Lemma (ch_server_name [] == None)

val lemma_ch_server_name_host:
  h:GHN.hostName ->
  tl:list GSN.serverName ->
  Lemma (ch_server_name (GSN.Name_host_name h :: tl) ==
         Some ((h <: B.bytes) <: T.hostname))

val ch_extensions:
  l:list GECH.extensionClientHello ->
  server_name:option T.hostname ->
  key_share:option (B.bytes_of_len 32) ->
  saw_supported_versions:bool ->
  signature_schemes:list T.signature_scheme ->
  GTot (option (option T.hostname & option (B.bytes_of_len 32) & bool & list T.signature_scheme))

val lemma_ch_extensions_nil:
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions [] sn ks sv ss == (if sv then Some (sn, ks, sv, ss) else None))

val lemma_ch_extensions_cons_sn:
  snl:GESN.extensionClientHello_extension_data_server_name ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_server_name snl :: tl) sn ks sv ss ==
         (if Some? sn then ch_extensions tl sn ks sv ss
          else (match ch_server_name snl with
                | Some name -> ch_extensions tl (Some name) ks sv ss
                | None -> None)))

val lemma_ch_extensions_cons_sg:
  sgl:GESG.extensionClientHello_extension_data_supported_groups ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_supported_groups sgl :: tl) sn ks sv ss ==
         ch_extensions tl sn ks sv ss)

val lemma_ch_extensions_cons_sa:
  ssl:GESA.extensionClientHello_extension_data_signature_algorithms ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_signature_algorithms ssl :: tl) sn ks sv ss ==
         ch_extensions tl sn ks sv (if Nil? ss then synth_sig_schemes ssl else ss))

val lemma_ch_extensions_cons_ks:
  kscl:GESK.extensionClientHello_extension_data_key_share ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_key_share kscl :: tl) sn ks sv ss ==
         (if Some? ks then ch_extensions tl sn ks sv ss
          else (match TLS13.Wire.Semantics.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
                | Some raw -> if B.length raw = 32 then ch_extensions tl sn (Some (raw <: B.bytes_of_len 32)) sv ss else None
                | None -> None)))

val lemma_ch_extensions_cons_sv:
  svl:GESV.extensionClientHello_extension_data_supported_versions ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_supported_versions svl :: tl) sn ks sv ss ==
         (if FStar.List.Tot.mem GOV.Offered_TLS_1p3 svl
          then ch_extensions tl sn ks true ss
          else None))

val lemma_ch_extensions_cons_other:
  e:GECH.extensionClientHello ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma
    (requires
      not (GECH.Extension_data_server_name? e) /\
      not (GECH.Extension_data_supported_groups? e) /\
      not (GECH.Extension_data_signature_algorithms? e) /\
      not (GECH.Extension_data_key_share? e) /\
      not (GECH.Extension_data_supported_versions? e))
    (ensures ch_extensions (e :: tl) sn ks sv ss ==
             ch_extensions tl sn ks sv ss)
(* The total byte size of a certificate chain (sum of raw DER blob lengths),
   exposed so the Reveal layer can bridge it to [reveal_cert_chain_total_bytes].
   Declared here (ahead of the representability predicates) to match the order
   of the realizing definitions in the implementation module. *)
val cert_chain_total_bytes (l:list (Seq.seq U8.t)) : GTot nat

val clientHello_representable (b:GCH.clientHello) : GTot bool

(* --- Reveal [clientHello_representable] as the [ch_extensions] scan outcome
       (X25519 key share present, <=16 sig schemes, server_name <=255 bytes)
       plus the <=16 cipher-suite bound.  Definitional; lets the byte-level
       Parser tie its scan result to representability. --- *)

val lemma_clientHello_representable_scan:
  c:GCH.clientHello ->
  Lemma (clientHello_representable c ==
    ((match ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
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

(* --- The Parser bridge: an accepted (commit-first) ClientHello's stored
       (server_name, key_share, sig_schemes) equal the first-wins [Sem]
       accessors used by [is_valid_client_hello].  Under representability the
       key share is present (Some) and sig schemes non-empty (Cons?), so the
       Some/Cons? branches below pin the Sem accessors exactly. --- *)
val lemma_ch_extensions_connect:
  c:GCH.clientHello ->
  Lemma (ensures (
    match ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
                        None None false [] with
    | Some (sn, ks, _, ss) ->
      sn == TLS13.Wire.Semantics.clientHello_server_name c /\
      (match ks with
       | Some k -> TLS13.Wire.Semantics.clientHello_key_share_x25519 c
                   == Some ((k <: B.bytes) <: Seq.seq U8.t)
       | None -> TLS13.Wire.Semantics.clientHello_key_share_x25519 c == None) /\
      (match TLS13.Wire.Semantics.clientHello_sig_algs c with
       | Some sas -> ss == synth_sig_schemes sas
       | None -> ss == [])
    | None -> True))

val serverHello_representable (b:GSH.serverHello) : GTot bool
val encryptedExtensions_representable (b:GEE.encryptedExtensions) : GTot bool
val certificate_representable (b:GCert.certificate) : GTot bool
val certificateVerify_representable (b:GCV.certificateVerify) : GTot bool

(* Reveal the opaque per-message representability predicates as their [Sem]-level
   accept conditions (the Parser's accept/reject branches compute these). *)
val lemma_certificateVerify_representable (b:GCV.certificateVerify)
  : Lemma (certificateVerify_representable b ==
           (B.length (TLS13.Wire.Semantics.certificateVerify_signature_bytes b)
            <= M.signature_max_len))

val lemma_serverHello_representable (b:GSH.serverHello)
  : Lemma (serverHello_representable b ==
           (Some? (TLS13.Wire.Semantics.serverHello_kex_share b) &&
            (match TLS13.Wire.Semantics.serverHello_cipher_suite b with
             | Some cs -> H.is_supported_cipher_suite cs
             | None -> false)))

val lemma_encryptedExtensions_representable (b:GEE.encryptedExtensions)
  : Lemma (encryptedExtensions_representable b ==
           (match TLS13.Wire.Semantics.encryptedExtensions_alpn b with
            | Some a -> B.length a <= M.client_hello_server_name_max_len
            | None -> true))

(* Reveal [certificate_representable] as its [Sem]-level accept condition, then
   the recursion equations for [cert_chain_total_bytes] (order matches the
   realizing definitions in the implementation module). *)
val lemma_certificate_representable (b:GCert.certificate)
  : Lemma (certificate_representable b ==
           (FStar.List.Tot.length (TLS13.Wire.Semantics.certificate_entries b)
              <= M.certificate_chain_max_entries &&
            cert_chain_total_bytes (TLS13.Wire.Semantics.certificate_entries b)
              <= M.certificate_chain_max_bytes))

val lemma_cert_chain_total_bytes_nil (_:unit)
  : Lemma (cert_chain_total_bytes [] == 0)

val lemma_cert_chain_total_bytes_cons (c:Seq.seq U8.t) (tl:list (Seq.seq U8.t))
  : Lemma (cert_chain_total_bytes (c :: tl) == B.length c + cert_chain_total_bytes tl)

val synth_handshake_msg_of:
  h:GHS.handshake ->
  GTot (option M.handshake_msg)

val parse_handshake:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_handshake_msg:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val lemma_parse_handshake_strong_prefix:
  prefix:B.bytes ->
  input:B.bytes ->
  msg:M.handshake_msg ->
  consumed:nat ->
  Lemma
    (requires
      parse_handshake prefix == Some (msg, consumed) /\
      consumed == B.length prefix /\
      B.length prefix <= B.length input /\
      Seq.equal prefix (Seq.slice input 0 (B.length prefix)))
    (ensures parse_handshake input == Some (msg, consumed))

val serialize_handshake:
  msg:M.handshake_msg ->
  GTot B.bytes

val serialize_handshake_msg:
  msg:M.handshake_msg ->
  GTot B.bytes

val serialize_server_certificate_verify_input:
  transcript_hash:B.bytes ->
  GTot B.bytes

val lemma_serialize_server_certificate_verify_input_len32:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (serialize_server_certificate_verify_input transcript_hash)
    (H.certificate_verify_input transcript_hash))

val parse_record:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

val parse_record_wire:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

(**
  The exact streaming condition under which another transport read is
  warranted: either the five-byte record header is incomplete, or a valid,
  bounded header is present but its declared fragment has not fully arrived.
  Malformed complete headers do not satisfy this predicate.
**)
let record_prefix_incomplete (input:B.bytes) : GTot prop =
  if B.length input < 5 then
    True
  else
    let b0 = Seq.index input 0 in
    let b1 = Seq.index input 1 in
    let b2 = Seq.index input 2 in
    let fragment_len = read_u16 input 3 in
    b1 == 0x03uy /\
    (b2 == 0x03uy \/ (b0 == 0x16uy /\ b2 == 0x01uy)) /\
    fragment_len <= 16640 /\
    (b0 == 0x14uy \/ b0 == 0x15uy \/ b0 == 0x16uy \/ b0 == 0x17uy) /\
    B.length input < 5 + fragment_len

val lemma_record_prefix_incomplete_bound:
  input:B.bytes ->
  Lemma
    (requires record_prefix_incomplete input)
    (ensures B.length input < 5 + 16640)

val lemma_parse_record_implies_parse_record_wire:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        parse_record_wire input == Some (content_type, fragment, consumed)
      | None -> True))

val lemma_parse_record_generated:
  input:B.bytes ->
  record:GCTX.tLSCiphertext ->
  consumed:nat{consumed <= B.length input} ->
  Lemma
    (requires (
      LP.parse GCTX.tLSCiphertext_parser input == Some (record, consumed) /\
      record.GCTX.legacy_record_version == GPV.TLS_1p2))
    (ensures (
      parse_record input ==
        Some
          (record.GCTX.opaque_type,
           (record.GCTX.encrypted_record <: B.bytes),
           consumed)))

val lemma_parse_record_wire_some_consumed_positive:
  input:B.bytes ->
  content_type:T.content_type ->
  fragment:M.sealed_record ->
  consumed:nat ->
  Lemma
    (requires parse_record_wire input == Some (content_type, fragment, consumed))
    (ensures consumed >= 5 /\ consumed <= B.length input)

val parse_record_header:
  input:B.bytes ->
  GTot (option (T.content_type & nat))

val lemma_parse_record_header_some_iff:
  input:B.bytes{B.length input == 5} ->
  Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x00uy ||
      Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     (Seq.index input 2 = 0x03uy ||
      (Seq.index input 0 = 0x16uy && Seq.index input 2 = 0x01uy)) &&
     read_u16 input 3 <= 16640))

val serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot B.bytes

val lemma_serialize_record_generated:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma (serialize_record content_type fragment ==
    LP.serialize GCTX.tLSCiphertext_serializer {
      GCTX.opaque_type = content_type;
      GCTX.legacy_record_version = GPV.TLS_1p2;
      GCTX.encrypted_record =
        (fragment <: GCTXF.tLSCiphertext_encrypted_record);
    })

val lemma_serialize_record_oversize:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment > 16640} ->
  Lemma (serialize_record content_type fragment == B.empty)

val lemma_parse_record_serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma
    (B.length (serialize_record content_type fragment) == 5 + B.length fragment /\
     parse_record (serialize_record content_type fragment) ==
      Some (content_type, fragment, B.length (serialize_record content_type fragment)))

val parse_plaintext:
  input:B.bytes ->
  GTot (option M.plaintext)

val serialize_plaintext:
  pt:M.plaintext ->
  GTot B.bytes

val lemma_parse_plaintext_serialize_plaintext:
  pt:M.plaintext ->
  Lemma (parse_plaintext (serialize_plaintext pt) == Some pt)

(* --- Branch-specific (LTL/pairing) bespoke ServerHello field parser.  Parses a
       canonical fixed-layout ChaCha20 ServerHello, extracting the 32-byte random
       and the x25519 key_share by byte offset (52- or 58-byte key_share
       position).  Retargeted off the deleted M.server_hello projection record
       onto this local field-view record. --- *)
type supported_server_hello = {
  random: B.bytes_of_len 32;
  key_share: B.bytes_of_len 32;
  cipher_suite: T.cipher_suite;
}

val parse_supported_server_hello:
  input:B.bytes ->
  GTot (option supported_server_hello)

val lemma_parse_supported_server_hello_ok:
  input:B.bytes ->
  Lemma (Some? (parse_supported_server_hello input) <==>
         SHC.server_hello_ok input)

val lemma_parse_supported_server_hello_fields:
  input:B.bytes ->
  Lemma
    (requires SHC.server_hello_ok input)
    (ensures (
      match parse_supported_server_hello input with
      | Some sh ->
        sh.cipher_suite == SHC.server_hello_selected_suite input /\
        Seq.equal sh.random (Seq.slice input 6 38) /\
        ((SHC.server_hello_ok_84 input /\
          Seq.equal sh.key_share (Seq.slice input 84 116)) \/
         (SHC.server_hello_ok_90 input /\
          Seq.equal sh.key_share (Seq.slice input 90 122)))
      | None -> False))

val parse_sealed_record:
  input:B.bytes ->
  GTot (option M.sealed_record)

val serialize_sealed_record:
  record:M.sealed_record ->
  GTot B.bytes

val parse_tls_message:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot (option M.tls_message)

val lemma_parse_tls_message_handshake_some:
  fragment:B.bytes ->
  msg:M.handshake_msg ->
  Lemma
    (requires
      parse_tls_message T.Handshake fragment ==
        Some (M.TlsHandshake msg))
    (ensures
      parse_handshake fragment ==
        Some (msg, B.length fragment))

val lemma_parse_tls_message_handshake_partial_none:
  fragment:B.bytes ->
  msg:M.handshake_msg ->
  consumed:nat ->
  Lemma
    (requires
      parse_handshake fragment == Some (msg, consumed) /\
      consumed < B.length fragment)
    (ensures parse_tls_message T.Handshake fragment == None)

val lemma_parse_handshake_serialize_protected_consumes_all:
  sent_msg:M.handshake_msg ->
  parsed_msg:M.handshake_msg ->
  consumed:nat ->
  Lemma
    (requires
      (match sent_msg with
       | M.EncryptedExtensions _
       | M.Certificate _
       | M.CertificateVerify _
       | M.Finished _ -> True
       | _ -> False) /\
      parse_handshake (serialize_handshake sent_msg) ==
        Some (parsed_msg, consumed))
    (ensures consumed == B.length (serialize_handshake sent_msg))

(* The generated [Invalid] content type (wire byte 0) never carries a TLS
   message: the spec parser rejects it.  Exposed so consumers can discharge the
   "no content type matches" obligation for an unknown record content type. *)
val lemma_parse_tls_message_invalid_none:
  fragment:B.bytes ->
  Lemma (parse_tls_message T.Invalid fragment == None)

val lemma_parse_handshake_none_of_lp_none:
  fragment:B.bytes ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures parse_handshake fragment == None)

val lemma_parse_handshake_none_of_synth_none:
  fragment:B.bytes ->
  v:GHS.handshake ->
  consumed:LP.consumed_length fragment ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              synth_handshake_msg_of v == None)
    (ensures parse_handshake fragment == None)

val lemma_ptm_handshake_fallback:
  fragment:B.bytes ->
  Lemma
    (requires parse_handshake fragment == None)
    (ensures parse_tls_message T.Handshake fragment ==
      (match parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

(* --- Streaming handshake-content parser ------------------------------------

   [parse_tls_message T.Handshake] is a WHOLE-FRAGMENT parser: it succeeds only
   when the message occupies the record fragment exactly, so it cannot describe
   a record whose plaintext coalesces several handshake messages.  The internal-
   event pipeline needs a STREAMING parser: one that reads the first message of
   a handshake-content plaintext and reports how many bytes it consumed, so the
   remainder can be re-parsed by a subsequent internal step.

   [parse_handshake] is already streaming but ranges over [M.handshake_msg],
   which excludes the post-handshake messages ([TlsKeyUpdate],
   [TlsIgnoredPostHandshake]) that [parse_tls_message] handles by fallback.
   [parse_handshake_stream] closes that gap: it ranges over the full
   [M.tls_message] and always reports a consumed length.

   Note the post-handshake fallbacks are themselves whole-input parsers, so on
   that branch the reported length is [B.length input] and the residual is
   empty.  This is exactly the pre-existing behaviour, now made explicit rather
   than implicit in the record framing. *)
val parse_handshake_stream:
  input:B.bytes ->
  GTot (option (M.tls_message & nat))

val lemma_parse_handshake_stream_def:
  input:B.bytes ->
  Lemma (parse_handshake_stream input ==
    (match parse_handshake input with
     | Some (msg, consumed) -> Some (M.TlsHandshake msg, consumed)
     | None ->
       (match parse_key_update input with
        | Some req -> Some (M.TlsKeyUpdate req, B.length input)
        | None ->
          (match parse_ignored_post_handshake input with
           | Some body -> Some (M.TlsIgnoredPostHandshake body, B.length input)
           | None -> None))))

(* The consumed length is strictly positive and within the input.  Strict
   positivity is what makes an internal-step loop over a pending plaintext
   terminate: each step strictly decreases the residual length. *)
val lemma_parse_handshake_stream_bounds:
  input:B.bytes ->
  msg:M.tls_message ->
  consumed:nat ->
  Lemma
    (requires parse_handshake_stream input == Some (msg, consumed))
    (ensures 0 < consumed /\ consumed <= B.length input)

(* Agreement with the whole-fragment parser: on a plaintext holding exactly one
   message the two coincide, and when the streaming parser leaves a residual the
   whole-fragment parser rejects.  This is the bridge that lets the pipeline
   subsume the existing single-message receive path without changing its
   semantics. *)
val lemma_parse_handshake_stream_whole:
  input:B.bytes ->
  Lemma (parse_tls_message T.Handshake input ==
    (match parse_handshake_stream input with
     | Some (msg, consumed) -> if consumed = B.length input then Some msg else None
     | None -> None))

(* A streaming parse of a prefix is stable under extension of the input, so a
   message parsed out of a pending plaintext is the same message that would be
   parsed out of the whole record.  Mirrors [lemma_parse_handshake_strong_prefix]
   at [tls_message] range. *)
val lemma_parse_handshake_stream_strong_prefix:
  prefix:B.bytes ->
  input:B.bytes ->
  msg:M.tls_message ->
  consumed:nat ->
  Lemma
    (requires
      parse_handshake_stream prefix == Some (msg, consumed) /\
      consumed == B.length prefix /\
      M.TlsHandshake? msg /\
      B.length prefix <= B.length input /\
      Seq.equal prefix (Seq.slice input 0 (B.length prefix)))
    (ensures parse_handshake_stream input == Some (msg, consumed))

val serialize_tls_message:
  msg:M.tls_message ->
  GTot (T.content_type & B.bytes)

val lemma_serialize_tls_message_handshake:
  hs:M.handshake_msg ->
  Lemma (serialize_tls_message (M.TlsHandshake hs) == (T.Handshake, serialize_handshake hs))

val lemma_serialize_tls_message_application_data:
  data:B.bytes ->
  Lemma (serialize_tls_message (M.TlsApplicationData data) == (T.Application_data, data))

val lemma_serialize_tls_message_close_notify:
  unit ->
  Lemma (serialize_tls_message (M.TlsAlert T.Close_notify) ==
    (T.Alert, LP.serialize
      TLS13.Wire.Generated.Alert.alert_serializer
      {
        TLS13.Wire.Generated.Alert.level =
          TLS13.Wire.Generated.AlertLevel.Fatal;
        TLS13.Wire.Generated.Alert.description = T.Close_notify;
      }))

val lemma_serialize_tls_message_change_cipher_spec:
  unit ->
  Lemma (serialize_tls_message M.TlsChangeCipherSpec ==
    (T.Change_cipher_spec, B.singleton 1uy))

val lemma_serialize_tls_message_key_update_not_requested:
  unit ->
  Lemma (serialize_tls_message (M.TlsKeyUpdate M.UpdateNotRequested) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]))

(* The KeyUpdate body is a single byte carrying the request form; the two
   encodings differ only in that byte.  [key_update_request_byte] names it so
   that the serialisation lemma can be stated once, for both forms. *)
(* [inline_for_extraction] matters here: as a standalone extracted function this
   would put a TLS13.Messages dependency inside the Wire.Spec bundle, which
   already depends on TLS13.Messages the other way round, and KaRaMeL rejects
   the resulting bundle cycle.  Inlining leaves no declaration behind. *)
inline_for_extraction
let key_update_request_byte (req:M.key_update_request) : B.byte =
  match req with
  | M.UpdateNotRequested -> 0uy
  | M.UpdateRequested -> 1uy

val lemma_serialize_tls_message_key_update_requested:
  unit ->
  Lemma (serialize_tls_message (M.TlsKeyUpdate M.UpdateRequested) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; 1uy]))

val lemma_serialize_tls_message_key_update:
  req:M.key_update_request ->
  Lemma (serialize_tls_message (M.TlsKeyUpdate req) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; key_update_request_byte req]))

val parse_tls_record:
  input:B.bytes ->
  GTot (option (M.tls_record & nat))

val serialize_tls_record:
  record:M.tls_record ->
  GTot B.bytes

val lemma_parse_record_serializes:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        consumed > 0 /\
        consumed <= B.length input /\
        consumed == B.length (serialize_record content_type fragment) /\
        Seq.equal (serialize_record content_type fragment)
                  (Seq.slice input 0 consumed)
      | None -> True))

val lemma_parse_record_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_record_wire_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record_wire input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_tls_message_round_trip:
  content_type:T.content_type ->
  fragment:B.bytes ->
  Lemma
    (ensures (
      match parse_tls_message content_type fragment with
      | Some (M.TlsHandshake (M.ClientHello ch)) ->
        Seq.equal fragment (serialize_handshake (M.ClientHello ch))
      | Some (M.TlsHandshake (M.ServerHello sh)) ->
        Seq.equal fragment (serialize_handshake (M.ServerHello sh))
      | Some (M.TlsHandshake (M.EncryptedExtensions ee)) ->
        Seq.equal fragment (serialize_handshake (M.EncryptedExtensions ee))
      | Some (M.TlsHandshake (M.Certificate c)) ->
        Seq.equal fragment (serialize_handshake (M.Certificate c))
      | Some (M.TlsHandshake (M.CertificateVerify cv)) ->
        Seq.equal fragment (serialize_handshake (M.CertificateVerify cv))
      | Some (M.TlsHandshake (M.Finished fin)) ->
        Seq.equal fragment (serialize_handshake (M.Finished fin))
      | _ -> True))


(* --- synth_client_hello: the ClientHello accept/reject gate.  Re-targeted to
       return the generated wire record itself ([Some b] iff representable),
       matching how [synth_handshake_msg_of] wraps [M.ClientHello b]. --- *)


(* A handshake fragment that parses AS A WHOLE MESSAGE is the serialisation
   of that message, and re-parsing that serialisation returns the message and
   consumes all of it.

   Callers need this to describe a received single-message protected record
   as a [ConnProtectedHandshake] head step whose fragment is written
   [serialize_handshake msg]: it says that doing so loses no information
   about the bytes that actually arrived. *)
val lemma_parse_handshake_serialize_round_trip:
  fragment:B.bytes ->
  msg:M.handshake_msg ->
  Lemma
    (requires
      parse_tls_message T.Handshake fragment == Some (M.TlsHandshake msg) /\
      (match msg with
       | M.EncryptedExtensions _
       | M.Certificate _
       | M.CertificateVerify _
       | M.Finished _ -> True
       | _ -> False))
    (ensures
      Seq.equal fragment (serialize_handshake msg) /\
      0 < B.length (serialize_handshake msg) /\
      parse_handshake (serialize_handshake msg) ==
        Some (msg, B.length (serialize_handshake msg)))

val synth_client_hello:
  c:GCH.clientHello ->
  GTot (option GCH.clientHello)

val lemma_synth_client_hello:
  c:GCH.clientHello ->
  Lemma (synth_client_hello c ==
         (if clientHello_representable c then Some c else None))

(* --- Per-constructor reveals of [synth_handshake_msg_of].  Each equation is
       exactly the corresponding arm of the validating synth dispatch. --- *)

val lemma_synth_handshake_msg_finished:
  b:GHS.handshake_body_finished ->
  Lemma (synth_handshake_msg_of (GHS.Body_finished b) == Some (M.Finished b))

val lemma_synth_handshake_msg_key_update:
  b:GHS.handshake_body_key_update ->
  Lemma (synth_handshake_msg_of (GHS.Body_key_update b) == None)

val lemma_synth_handshake_msg_client_hello:
  b:GHS.handshake_body_client_hello ->
  Lemma (synth_handshake_msg_of (GHS.Body_client_hello b) ==
         (if clientHello_representable b then Some (M.ClientHello b) else None))

val lemma_synth_handshake_msg_certificate:
  b:GHS.handshake_body_certificate ->
  Lemma (synth_handshake_msg_of (GHS.Body_certificate b) ==
         (if certificate_representable (b <: GCert.certificate)
          then Some (M.Certificate (b <: GCert.certificate)) else None))

val lemma_synth_handshake_msg_certificate_verify:
  b:GHS.handshake_body_certificate_verify ->
  Lemma (synth_handshake_msg_of (GHS.Body_certificate_verify b) ==
         (if certificateVerify_representable b then Some (M.CertificateVerify b) else None))

val lemma_synth_handshake_msg_encrypted_extensions:
  b:GHS.handshake_body_encrypted_extensions ->
  Lemma (synth_handshake_msg_of (GHS.Body_encrypted_extensions b) ==
         (if encryptedExtensions_representable b then Some (M.EncryptedExtensions b) else None))

val lemma_synth_handshake_msg_server_hello_hrr:
  b:GHS.handshake_body_server_hello ->
  shb:GSHBody.serverHelloBody ->
  Lemma (requires b.GSH.body == GSHB.HelloRetryRequest shb)
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) == Some M.HelloRetryRequest)

val lemma_synth_handshake_msg_server_hello_sh:
  b:GHS.handshake_body_server_hello ->
  sf:GSHB.serverHello_body_false ->
  Lemma (requires b.GSH.body == GSHB.ServerHello_body_false sf)
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) ==
                 (if serverHello_representable b then Some (M.ServerHello b) else None))

val lemma_synth_handshake_msg_server_hello_bad_version:
  b:GHS.handshake_body_server_hello ->
  Lemma (requires GSHB.ServerHello_body_false? b.GSH.body /\ not (serverHello_representable b))
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) == None)

val lemma_synth_signature_scheme:
  s:GSS.signatureScheme ->
  Lemma (synth_signature_scheme s ==
         (match s with
          | GSS.Ecdsa_secp256r1_sha256 -> T.Ecdsa_secp256r1_sha256
          | GSS.Rsa_pss_rsae_sha256 -> T.Rsa_pss_rsae_sha256
          | GSS.Ed25519 -> T.Ed25519
          | GSS.Unknown_signatureScheme v -> T.Unknown_signatureScheme v))
