(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**
This modules defines TLS 1.3 Extensions.

- An AST, and it's associated parsing and formatting functions.
- Nego calls prepareExtensions : config -> list extensions.

@summary: TLS 1.3 Extensions.
*)
module Extensions

open FStar.Bytes
open FStar.Error
open TLSError
open TLSConstants

(*************************************************
 Define extension.
 *************************************************)

// Extensions may (selectively) appear in the following messages
 type ext_msg =
   | EM_ClientHello
   | EM_ServerHello
   | EM_EncryptedExtensions
   | EM_Certificate
   | EM_NewSessionTicket
   | EM_HelloRetryRequest

(* As a static invariant, we record that any intermediate, parsed
   extension and extension lists can be formatted into bytes without
   overflowing 2^16. This create dependencies on the formatting
   functions, at odd with recursive extensions. *)

(* PRE-SHARED KEYS AND KEY EXCHANGES *)

type pskIdentity = psk_identifier * PSK.obfuscated_ticket_age

// used in a refinement below
val pskiListBytes: list pskIdentity -> bytes

// how to build this type without overflows?? 
noeq type psk =
  | ClientPSK:
    // truncated PSK extension, without the list of binder tags.
    identities: list pskIdentity {let n = length (pskiListBytes identities) in 6 < n /\ n < 65536} ->
    binders_len: nat {binders_len <= 65535} -> psk
  | ServerPSK of UInt16.t
    // index into the client offer's PSK extension

// PSK binders, actually the truncated suffix of TLS 1.3 ClientHello
// We statically enforce length requirements to ensure that formatting is total.

//18-02-20 This should be defined in Hashing 
//18-02-20 We'll need a lemma on HMAC tag lengths. 
type binder = b:bytes {32 <= length b /\ length b <= 255}

(** REMARK: this is more restrictive than in the RFC, which allows up to 2047 binders *)
type binders =
  bs:list binder {1 <= List.Tot.length bs /\ List.Tot.length bs < 255}

// used in HandshakeLog
val bindersBytes: bs:binders -> b:bytes{length b >= 35 /\ length b <= 65537}

// https://tlswg.github.io/tls13-spec/#rfc.section.4.2.8
// restricting both proposed PSKs and future ones sent by the server
// will also be used in the PSK table, and possibly in the configs
type psk_kex =
  | PSK_KE
  | PSK_DHE_KE

type client_psk_kexes = l:list psk_kex
  { l = [PSK_KE] \/ l = [PSK_DHE_KE] \/ l = [PSK_KE; PSK_DHE_KE] \/ l = [PSK_DHE_KE; PSK_KE] }

#set-options "--admit_smt_queries true"
let client_psk_kexes_length (l:client_psk_kexes): Lemma (List.Tot.length l < 3) = ()

(* EARLY DATA INDICATION *)

type earlyDataIndication = option UInt32.t // Some max_early_data_size, only in NewSessionTicket

(* EC POINT FORMATS *)

type point_format =
  | ECP_UNCOMPRESSED
  | ECP_UNKNOWN of (n:nat{repr_bytes n <= 1})

// Move TLSConstants?
val alpnBytes : alpn -> b:bytes{length b < 65536}

// The length exactly reflects the RFC format constraint <2..254>
type protocol_versions =
  | ServerPV of protocolVersion
  | ClientPV of l:list protocolVersion' {0 < List.Tot.length l /\ List.Tot.length l < 128}

// We constrain unknown extensions to have headers different from
// known extensions; we rely on parametricity to avoid recursion
// between the datatype and its formatting property.
type unknownTag = lbytes 2 -> Type0

// ExtensionType and Extension Table in https://tlswg.github.io/tls13-spec/#rfc.section.4.2.
// M=Mandatory, AF=mandatory for Application Features in https://tlswg.github.io/tls13-spec/#rfc.section.8.2.
noeq type extension' (p: unknownTag) =
  | E_server_name of list serverName (* M, AF *) (* RFC 6066 *)
  | E_supported_groups of list CommonDH.namedGroup (* M, AF *) (* RFC 7919 *)
  | E_signature_algorithms of signatureSchemeList (* M, AF *) (* RFC 5246 *)
  | E_signature_algorithms_cert of signatureSchemeList (* TLS 1.3#23 addition; TLS 1.2 should also support it *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of psk (* M, AF *)
  | E_session_ticket of bytes
  | E_early_data of earlyDataIndication
  | E_supported_versions of protocol_versions   (* M, AF *)
  | E_cookie of b:bytes {0 < length b /\ length b < 65536}  (* M *)
  | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)
  | E_extended_ms
  | E_ec_point_format of list point_format
  | E_alpn of alpn
  | E_unknown_extension: x: lbytes 2 {p x} -> bytes -> extension' p (* header, payload *)
(*
We do not yet support the extensions below (authenticated but ignored)
  | E_max_fragment_length
  | E_status_request
  | E_use_srtp
  | E_heartbeat
  | E_signed_certifcate_timestamp
  | E_client_certificate_type
  | E_server_certificate_type
  | E_certificate_authorities
  | E_oid_filters
  | E_post_handshake_auth
  | E_renegotiation_info of renegotiationInfo
*)



val bindersLen: #p: unknownTag -> el: list (extension' p) -> nat
val string_of_extension: #p: unknownTag -> extension' p -> string
val string_of_extensions: #p: unknownTag -> list (extension' p) -> string

(** shallow equality, comparing just the extension tags *)
val sameExt: #p: unknownTag -> e1: extension' p -> e2: extension' p -> bool

(*************************************************
 extension formatting
 *************************************************)

val unknown: unknownTag
val is_unknown: x: lbytes 2 -> b:bool {b2t b <==> unknown x}
type extension = extension' unknown

// TLSConstants defines the application-level type for custom extensions
val ext_of_custom: custom_extensions -> list extension
val custom_of_ext: list extension -> custom_extensions
val app_ext_filter: option (list extension) -> option (list extension)

let encryptedExtension (ext: extension) : bool =
  match ext with
  | E_server_name _
  | E_supported_groups _
  | E_alpn _
  | E_unknown_extension _ _
  | E_early_data _ -> true
  | _ -> false

(** Serializes an extension *)
val extensionBytes: ext:extension -> b:bytes { 2 <= length b /\ length b < 65536 }
val extensionBytes_is_injective:
  ext1: extension -> s1: bytes{ UInt.size (length (extensionBytes ext1) + length s1) UInt32.n } ->
  ext2: extension -> s2: bytes{ UInt.size (length (extensionBytes ext2) + length s2) UInt32.n } -> 
  Lemma
  (requires (extensionBytes ext1 @| s1 = extensionBytes ext2 @| s2))
  (ensures  (ext1 == ext2 /\ s1 == s2))

// we'll need to reveal more to build extensions...
val extensionListBytes: exts: list extension -> bytes
type extensions = exts:list extension {repr_bytes (length (extensionListBytes exts)) <= 2}

(** Serializes a list of extensions.
  If there is a PreSharedKey client extension, then add the length of the PSK binders to
  the total length. Note that the `E_pre_shared_key` argument includes the length of
  binders in this case.
*)

type valid_extensions = exts: extensions {length (extensionListBytes exts) + bindersLen exts < 65536}

val extensionsBytes:
  exts:valid_extensions -> b:bytes {2 <= length b /\ length b < 2 + 65536}

val extensionsBytes_is_injective_strong:
  exts1:valid_extensions -> s1: bytes{ UInt.size (length (extensionsBytes exts1) + length s1) UInt32.n } ->
  exts2:valid_extensions -> s2: bytes{ UInt.size (length (extensionsBytes exts2) + length s2) UInt32.n } -> Lemma
  (requires extensionsBytes exts1 @| s1 = extensionsBytes exts2 @| s2)
  (ensures exts1 == exts2 /\ s1 == s2)

val extensionsBytes_is_injective:
  ext1:valid_extensions ->
  ext2:valid_extensions -> Lemma
  (requires Bytes.equal (extensionsBytes ext1) (extensionsBytes ext2))
  (ensures ext1 == ext2)

(*************************************************
 Extension parsing
**************************************************)

val parseExtension:     ext_msg -> bytes -> result (extension * option binders)
val parseExtensions:    ext_msg -> bytes -> result (extensions * option binders)

(** Called by HandshakeMessages; returns either Some,Some or None; why not using extensions here too? *)
val parseOptExtensions: ext_msg -> bytes -> result (option (list extension) * option binders)

(*************************************************
 Other extension functionality
 *************************************************)

/// 18-02-21 the rest of this module has nothing to do with formats,
/// could go to Negotiation or to a new Nego.Extensions module

val prepareExtensions:
  protocolVersion ->
  protocolVersion ->
  k:valid_cipher_suites{List.Tot.length k < 256} ->
  option bytes -> // SNI
  option alpn -> // ALPN
  custom_extensions -> // application-handled extensions
  bool -> // EMS
  bool ->
  bool -> // EDI (Nego checks that PSK is compatible)
  option bytes -> // session_ticket
  signatureSchemeList ->
  //18-02-26 
  // list CommonDH.namedGroup -> // FIXME: was: list valid_namedGroup, but the latter type disappeared
  list CommonDH.supportedNamedGroup ->
  option (cVerifyData * sVerifyData) ->
  option CommonDH.keyShare ->
  list (PSK.pskid * pskInfo) ->
  now: UInt32.t -> // for obfuscated ticket age
  l:list extension{List.Tot.length l < 256}

val negotiateClientExtensions:
  protocolVersion ->
  config ->
  option (list extension) ->
  option (list extension) ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  bool ->
  result protocolVersion

val negotiateServerExtensions:
  protocolVersion ->
  option (list extension) ->
  list cipherSuiteName ->
  config ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  option nat ->
  option CommonDH.keyShare ->
  bool ->
  result (option (list extension))

val default_signatureScheme:
  protocolVersion -> cipherSuite -> HyperStack.All.ML signatureSchemeList
