module TLS13.Crypto.Spec

module B = TLS13.Bytes
module T = TLS13.Types

type bytes_of_len (n:nat) = B.bytes_of_len n

type digest32 = bytes_of_len 32
type secret = bytes_of_len 32
type aead_key = bytes_of_len 32
type aead_nonce = bytes_of_len 12
type x25519_private = bytes_of_len 32
type x25519_public = bytes_of_len 32
type x25519_shared_secret = bytes_of_len 32
type public_key = B.bytes
type signature = B.bytes

val sha256: msg:B.bytes -> Tot digest32

val hmac_sha256: key:B.bytes -> msg:B.bytes -> Tot digest32

val hkdf_extract: salt:B.bytes -> ikm:B.bytes -> Tot secret

val hkdf_expand_label:
  secret:secret ->
  label:B.bytes ->
  context:B.bytes ->
  len:nat ->
  Tot (bytes_of_len len)

val x25519_public_from_private:
  sk:x25519_private ->
  Tot x25519_public

val x25519_shared:
  sk:x25519_private ->
  pk:x25519_public ->
  Tot (option x25519_shared_secret)

val tls13_record_nonce:
  static_iv:aead_nonce ->
  seq:nat ->
  Tot aead_nonce

val chacha20_poly1305_seal:
  key:aead_key ->
  nonce:aead_nonce ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Tot (bytes_of_len (B.length plaintext + 16))

val chacha20_poly1305_open:
  key:aead_key ->
  nonce:aead_nonce ->
  aad:B.bytes ->
  ciphertext:B.bytes ->
  Tot (option B.bytes)

val verify_signature:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  Tot bool

