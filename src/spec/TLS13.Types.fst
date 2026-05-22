module TLS13.Types

module B = TLS13.Bytes

type protocol_version =
  | TLS12
  | TLS13

type content_type =
  | ChangeCipherSpec
  | Alert
  | Handshake
  | ApplicationData

type alert_description =
  | CloseNotify
  | UnexpectedMessage
  | BadRecordMac
  | HandshakeFailure
  | DecodeError
  | DecryptError
  | ProtocolVersion
  | UnsupportedExtension
  | CertificateUnknown
  | IllegalParameter

type cipher_suite =
  | TLS_CHACHA20_POLY1305_SHA256

type named_group =
  | X25519
  | UnsupportedGroup of nat

type signature_scheme =
  | RsaPssRsaeSha256
  | EcdsaSecp256r1Sha256
  | Ed25519
  | UnsupportedSignatureScheme of nat

type extension_type =
  | SupportedVersions
  | SupportedGroups
  | SignatureAlgorithms
  | KeyShare
  | ServerName
  | ALPN
  | EarlyData
  | PSK
  | UnknownExtension of nat

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
