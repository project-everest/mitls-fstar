module TLS13.Messages

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module T = TLS13.Types
module X = TLS13.X509.Spec

module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished

// Bounds kept in sync with the impl-layer storage maxima
// (TLS13.Impl.ConnectionState.Bounds / TLS13.Impl.Messages); the generated
// grammar permits larger values, so the impl rejects fields exceeding these.
let client_hello_max_len : nat = 16777219
let server_hello_max_len : nat = 4096
let signature_max_len : nat = 4096
let certificate_chain_max_bytes : nat = 32768
let certificate_chain_max_entries : nat = 8
let client_hello_server_name_max_len : nat = 255
let client_hello_max_cipher_suites : nat = 16
let client_hello_max_signature_schemes : nat = 16

// Phase 3b: handshake messages carry the QuackyDucky-generated wire records
// directly (the single source of truth).  Profile-relevant fields are read via
// the TLS13.Wire.Semantics accessors instead of hand-written projection-record
// fields, and transcript exactness is the generated parse/serialize round-trip
// rather than a verbatim `body` field.
//
// [noextract]: this spec/model datatype wraps the generated high-level wire
// records (GCH.clientHello, ...), which are themselves `noextract` (they carry
// F* `list`s and are non-Low*).  `handshake_msg` is a ghost/model type: the impl
// operates on the L mirror (TLS13.Impl.Messages arrays) and the generated LOW
// representation at runtime, never on these high records.  Marking it `noextract`
// prevents KaRaMeL from emitting a C struct whose union members would reference
// the (undefined-in-C) generated high records.  Nothing extracted references it
// (only its own auto-generated discriminators, which vanish with the type).
noextract
type handshake_msg =
  | ClientHello of GCH.clientHello
  | ServerHello of GSH.serverHello
  | EncryptedExtensions of GEE.encryptedExtensions
  | Certificate of GCert.certificate
  | CertificateVerify of GCV.certificateVerify
  | Finished of GFin.finished
  | HelloRetryRequest

type key_update_request =
  | UpdateNotRequested
  | UpdateRequested

type plaintext = {
  content_type: T.content_type;
  fragment: B.bytes;
}

type sealed_record = B.bytes

// [noextract]: wraps `handshake_msg` (above) via `TlsHandshake`, so it is a
// ghost/model type for the same reason.  Its only C referencer (the surrounding
// `conn_event` model type) is already dead-code-eliminated; marking it
// `noextract` keeps the extraction consistent (a non-noextract type embedding a
// noextract one would produce a dangling C reference).
noextract
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
