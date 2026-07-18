module TLS13.Types

module B = TLS13.Bytes

(* The QuackyDucky-generated wire enums are the single source of truth for the
   TLS leaf/enum types.  This module re-exports them (so consumers keep using the
   `TLS13.Types` qualifier) and keeps the two semantic types that have no wire
   counterpart: [tls_error] (the implementation's failure vocabulary) and
   [hostname] (an unparsed server-name blob). *)

include TLS13.Wire.Generated.ProtocolVersion
include TLS13.Wire.Generated.ContentType
include TLS13.Wire.Generated.AlertDescription
include TLS13.Wire.Generated.CipherSuite
include TLS13.Wire.Generated.NamedGroup
include TLS13.Wire.Generated.SignatureScheme

(* Backwards-compatible snake_case abbreviations for the generated enums.  The
   generated [contentType] includes an [Invalid] constructor (wire byte 0) that
   is not a valid TLS record content type in this profile; the codec
   ([content_type_of_byte]/[parse_tls_message]) maps it to/from byte 0 and
   rejects it as carrying no message. *)
let protocol_version = protocolVersion
let content_type = contentType
let alert_description = alertDescription
let cipher_suite = cipherSuite
let named_group = namedGroup
let signature_scheme = signatureScheme

type tls_error =
  | AlertError of alert_description
  | UnsupportedCipherSuite
  | UnsupportedNamedGroup
  | UnsupportedSignature
  | HelloRetryRequestRejected
  | BadCertificate
  | BadCertificateVerify
  | BadFinished
  | BadRecordTag
  | OutputBufferTooSmall
  | IoError

type hostname = B.bytes
