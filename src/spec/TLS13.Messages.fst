module TLS13.Messages

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module T = TLS13.Types
module X = TLS13.X509.Spec

type client_hello = {
  random: B.bytes_of_len 32;
  server_name: option T.hostname;
  key_share: C.x25519_public;
  cipher_suites: list T.cipher_suite;
  signature_schemes: list T.signature_scheme;
}

type server_hello = {
  random: B.bytes_of_len 32;
  key_share: C.x25519_public;
  cipher_suite: T.cipher_suite;
}

type encrypted_extensions = {
  negotiated_alpn: option B.bytes;
}

type certificate_msg = {
  chain: X.cert_chain;
}

type certificate_verify = {
  scheme: T.signature_scheme;
  signature: C.signature;
}

type finished = {
  verify_data: C.digest32;
}

type handshake_msg =
  | ClientHello of client_hello
  | ServerHello of server_hello
  | EncryptedExtensions of encrypted_extensions
  | Certificate of certificate_msg
  | CertificateVerify of certificate_verify
  | Finished of finished
  | HelloRetryRequest

type plaintext = {
  content_type: T.content_type;
  fragment: B.bytes;
}

type sealed_record = B.bytes

type tls_message =
  | TlsHandshake of handshake_msg
  | TlsApplicationData of B.bytes
  | TlsAlert of T.alert_description
  | TlsChangeCipherSpec
  | TlsIgnoredPostHandshake of B.bytes

type tls_record = {
  record_outer_type: T.content_type;
  record_fragment: sealed_record;
}
