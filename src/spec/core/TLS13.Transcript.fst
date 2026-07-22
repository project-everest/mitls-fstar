module TLS13.Transcript

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec

type transcript = B.bytes

let empty : transcript = B.empty

let append (t:transcript) (handshake_bytes:B.bytes) : transcript =
  B.append t handshake_bytes

let hash (t:transcript) : C.digest32 =
  C.sha256 t

