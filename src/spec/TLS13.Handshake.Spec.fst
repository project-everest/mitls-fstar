module TLS13.Handshake.Spec

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

let is_supported_cipher_suite (suite:T.cipher_suite) : bool =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> true

let is_supported_group (group:T.named_group) : bool =
  match group with
  | T.X25519 -> true
  | _ -> false

let certificate_verify_input (transcript_hash:C.digest32) : B.bytes =
  transcript_hash

let verify_certificate_verify
  (peer:X.peer_identity)
  (transcript_hash:C.digest32)
  (cv:certificate_verify)
  : bool =
  C.verify_signature
    cv.scheme
    peer.X.leaf_public_key
    (certificate_verify_input transcript_hash)
    cv.signature

