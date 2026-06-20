module TLS13.Messages

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module T = TLS13.Types
module X = TLS13.X509.Spec

// Received ClientHello messages carry their full handshake fragment verbatim for
// transcript replay.  The generated handshake grammar bounds a serialized
// handshake message to a uint24 body plus the one-byte handshake tag.
let client_hello_max_len : nat = 16777219

type client_hello = {
  random: B.bytes_of_len 32;
  server_name: option T.hostname;
  key_share: C.x25519_public;
  cipher_suites: list T.cipher_suite;
  signature_schemes: list T.signature_scheme;
  body: b:B.bytes{B.length b <= client_hello_max_len};
}

// Upper bound (in bytes) on a wire-encoded ServerHello handshake message.  Kept
// in sync with TLS13.Impl.ConnectionState.Bounds.max_server_hello_len (4096);
// defined here so the spec layer (which cannot depend on the impl layer) can
// refine the carried wire bytes and so serialize_handshake stays bounded.
let server_hello_max_len : nat = 4096

// Bounds on received-message fields, kept in sync with the impl-layer storage
// maxima in TLS13.Impl.ConnectionState.Bounds / TLS13.Impl.Messages
// (max_signature_len, max_certificate_chain_bytes, max_certificate_chain_entries).
// The QuackyDucky grammar allows larger values (signature<0..2^16-1>,
// cert_data<1..2^24-1>), so the synth functions reject fields exceeding these so
// the fixed-size low-level (L) representation can always hold the parsed value.
let signature_max_len : nat = 4096
let certificate_chain_max_bytes : nat = 32768
let certificate_chain_max_entries : nat = 8
let client_hello_server_name_max_len : nat = 255
let client_hello_max_cipher_suites : nat = 16
let client_hello_max_signature_schemes : nat = 16

// The wire-encoded extensions of received messages are carried verbatim (as a
// "bytes payload", including unknown extensions) so that re-serialization is
// exact (parser round-trip), supporting servers that send extra/reordered
// extensions or echo a non-empty legacy_session_id.  For ServerHello the carried
// body is the full handshake message and is bounded by server_hello_max_len.
type server_hello = {
  random: B.bytes_of_len 32;
  key_share: C.x25519_public;
  cipher_suite: T.cipher_suite;
  body: b:B.bytes{B.length b <= server_hello_max_len};
}

type encrypted_extensions = {
  negotiated_alpn: option B.bytes;
  body: B.bytes;
}

type certificate_msg = {
  chain: X.cert_chain;
  body: B.bytes;
}

type certificate_verify = {
  scheme: T.signature_scheme;
  signature: C.signature;
  body: B.bytes;
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

type key_update_request =
  | UpdateNotRequested
  | UpdateRequested

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
  | TlsKeyUpdate of key_update_request

type tls_record = {
  record_outer_type: T.content_type;
  record_fragment: sealed_record;
}
