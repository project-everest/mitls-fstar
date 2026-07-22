module TLS13.Handshake.Spec

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module K = TLS13.Keys
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec
module Sem = TLS13.Wire.Semantics
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

include TLS13.Messages

let is_supported_cipher_suite (suite:T.cipher_suite) : bool =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> true
  | T.Unknown_cipherSuite _ -> false

let is_supported_group (group:T.named_group) : bool =
  match group with
  | T.X25519 -> true
  | _ -> false

let certificate_verify_server_context : B.bytes =
  B.of_list [
    0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
    0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
    0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
    0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
    0x79uy
  ]

let certificate_verify_input (transcript_hash:C.digest32) : B.bytes =
  B.append (B.append (Seq.create 64 0x20uy) certificate_verify_server_context)
    (B.append (B.singleton B.zero) transcript_hash)

let verify_certificate_verify
  (peer:X.peer_identity)
  (transcript_hash:C.digest32)
  (cv:GCV.certificateVerify)
  : bool =
  C.verify_signature
    (Sem.certificateVerify_scheme cv)
    peer.X.leaf_public_key
    (certificate_verify_input transcript_hash)
    (Sem.certificateVerify_signature_bytes cv)

let expected_finished (base_key:C.secret) (transcript_hash:C.digest32) : GFin.finished =
  K.finished_verify_data base_key transcript_hash

let verify_finished
  (base_key:C.secret)
  (transcript_hash:C.digest32)
  (fin:GFin.finished)
  : GTot bool =
  Seq.equal (Sem.finished_verify_data fin) (K.finished_verify_data base_key transcript_hash)
