(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**

This modules groups QD types, parsers, and formatters for all
extensions, collected from TLS 1.2. TLS 1.3, and various other
RFCs---see the RFC source file for specific comments and details.

Several handshake messages include a list of extensions. Extensions
are organized by name, but their presence and contents depend on the
enclosing message. To this end, we provide a separate top-level type
of list of extensions for

  ClientHello,
  HelloRetryRequest, ServerHello, EncryptedExtensions
  CertificateRequest, Certificate, 
  NewSessionTicket 

with some sharing of their individual contents types.

Their semantics is handled in Negotiation. 

@summary: TLS Extensions.
*)
module Extensions

open FStar.Bytes
open FStar.Error
open TLSError
open TLSConstants

(* Extension tag *)
include Parsers.ExtensionType

(* Server Name Indication *)
include Parsers.NameType
include Parsers.ServerName
include Parsers.ServerNameList

(* Max fragment length *)
include Parsers.MaxFragmentLength

(* Certificate Status *)
include Parsers.CertificateStatusType
include Parsers.OCSPStatusRequest
include Parsers.CertificateStatusRequest
include Parsers.CertificateStatus

(* Supported groups *)
include Parsers.NamedGroup
include Parsers.NamedGroupList

(* EC point format *)
include Parsers.ECPointFormat
include Parsers.ECPointFormatList

(* Signature algorithms *)
include Parsers.SignatureScheme
include Parsers.SignatureSchemeList

(* SRTP *)
include Parsers.UseSRTPData

(* Signed Certificate Timestamp *)
include Parsers.SignedCertificateTimestampList

(* ALPN *)
include Parsers.ProtocolName
include Parsers.ProtocolNameList

(* Ticket *)
include Parsers.TicketContents

(* EDI (NewSessionTicket) *)
include Parsers.EarlyDataIndicationNewSessionTicket

(* Heartbeat *)
include Parsers.HeartbeatMode
include Parsers.HeartbeatExtension

(* Pre-shared key *)
include Parsers.PskIdentity
include Parsers.PskBinderEntry
include Parsers.OfferedPsks
include Parsers.PreSharedKeyServerExtension

(* Key exchange mode *)
include Parsers.PskKeyExchangeMode
include Parsers.PskKeyExchangeModes

(* Supported version *)
include Parsers.ProtocolVersion
include Parsers.SupportedVersions

(* Cookie *)
include Parsers.Cookie

(* Certificate type *)
include Parsers.CertificateType
include Parsers.ClientCertTypeExtension
include Parsers.ServerCertTypeExtension

(* Certificate Authorities *)
include Parsers.CertificateAuthoritiesExtension

(* OID filter *)
include Parsers.OIDFilterExtension

(* Key share *)
include Parsers.UncompressedPointRepresentation32
include Parsers.UncompressedPointRepresentation48
include Parsers.UncompressedPointRepresentation66
include Parsers.MontgomeryPoint32
include Parsers.MontgomeryPoint56
include Parsers.ServerDHParams
include Parsers.KeyShareEntry
include Parsers.KeyShareClientHello

(* Unknown *)
include Parsers.UnknownExtension

(* New Session Ticket *)
include Parsers.NewSessionTicketExtension
include Parsers.NewSessionTicketExtensions

(* Certificate Request *)
include Parsers.CertificateRequestExtension
include Parsers.CertificateRequestExtensions

(* Certificate *)
include Parsers.CertificateExtension
include Parsers.CertificateExtensions

(* Encrypted Extension *)
include Parsers.EncryptedExtension
include Parsers.EncryptedExtensions

(* Hello Retry Request *)
include Parsers.HRRExtension
include Parsers.HRRExtensions

(* Server Hello *)
include Parsers.ServerHelloExtension
include Parsers.ServerHelloExtensions

(* Client Hello *)
include Parsers.ClientHelloExtension
include Parsers.ClientHelloExtensions

// TLSConstants defines the application-level type for custom extensions
val cext_of_custom: custom_extensions -> clientHelloExtensions
val eext_of_custom: custom_extensions -> encryptedExtensions
val custom_of_cext: clientHelloExtensions -> custom_extensions
val custom_of_eext: encryptedExtensions -> custom_extensions

val bindersLen: clientHelloExtensions -> UInt32.t

(*
let clientHelloExtension_of_tagged_unknown_extension (x: taggedUnknownExtension) : Tot clientHelloExtension =
  CHE_Unknown_extensionType (tag_of_taggedUnknownExtension x) 
*)

/// We could specify which extensions are mandatory, and which are
/// applicative, based on table in
/// https://tlswg.github.io/tls13-spec/#rfc.section.4.2.
///
/// However, some rules, e.g. which server extensions need to be
/// encrypted, are now enforced by typing.
/// 
//
// // M=Mandatory, AF=mandatory for Application Features in https://tlswg.github.io/tls13-spec/#rfc.section.8.2.
// noeq type extension' (p: unknownTag) =
//   | E_server_name of list serverName (* M, AF *) (* RFC 6066 *)
//   | E_supported_groups of list CommonDH.namedGroup (* M, AF *) (* RFC 7919 *)
//   | E_signature_algorithms of signatureSchemeList (* M, AF *) (* RFC 5246 *)
//   | E_signature_algorithms_cert of signatureSchemeList (* TLS 1.3#23 addition; TLS 1.2 should also support it *)
//   | E_key_share of CommonDH.keyShare (* M, AF *)
//   | E_pre_shared_key of psk (* M, AF *)
//   | E_session_ticket of bytes
//   | E_early_data of earlyDataIndication
//   | E_supported_versions of protocol_versions   (* M, AF *)
//   | E_cookie of b:bytes {0 < length b /\ length b < 65536}  (* M *)
//   | E_psk_key_exchange_modes of client_psk_kexes (* client-only; mandatory when proposing PSKs *)
//   | E_extended_ms
//   | E_ec_point_format of list point_format
//   | E_alpn of alpn
//   | E_unknown_extension: x: lbytes 2 {p x} -> bytes -> extension' p (* header, payload *)

(* GONE:
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
  option protocolNameList -> // ALPN
  custom_extensions -> // application-handled extensions
  bool -> // EMS
  bool ->
  bool -> // EDI (Nego checks that PSK is compatible)
  option bytes -> // session_ticket
  signatureSchemeList ->
  list CommonDH.supportedNamedGroup ->
  option (cVerifyData * sVerifyData) ->
  option keyShareClientHello ->
  list (PSK.pskid * pskInfo) ->
  now: UInt32.t -> // for obfuscated ticket age
  clientHelloExtensions

val negotiateClientExtensions:
  protocolVersion ->
  config ->
  clientHelloExtensions ->
  serverHelloExtensions ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  bool ->
  result protocolVersion

val negotiateServerExtensions:
  protocolVersion ->
  clientHelloExtensions ->
  list cipherSuiteName ->
  config ->
  cipherSuite ->
  option (cVerifyData * sVerifyData) ->
  option nat ->
  option CommonDH.keyShareEntry ->
  bool ->
  result (serverHelloExtensions * encryptedExtensions)

val default_signatureScheme:
  protocolVersion -> cipherSuite -> HyperStack.All.ML signatureSchemeList
*)
