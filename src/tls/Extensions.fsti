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

(* Padding *)
include Parsers.PaddingExtension

(* Ticket *)
include Parsers.SessionTicket

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

val bindersLen: clientHelloExtensions -> nat

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
