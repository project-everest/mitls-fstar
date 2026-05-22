module TLS13.Keys

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec

type traffic_secret = C.secret

let derive_secret
  (secret:C.secret)
  (label:B.bytes)
  (context:B.bytes)
  : traffic_secret =
  C.hkdf_expand_label secret label context 32

let derive_aead_key (secret:C.secret) (label:B.bytes) : C.aead_key =
  C.hkdf_expand_label secret label B.empty 32

let derive_aead_iv (secret:C.secret) (label:B.bytes) : C.aead_nonce =
  C.hkdf_expand_label secret label B.empty 12

