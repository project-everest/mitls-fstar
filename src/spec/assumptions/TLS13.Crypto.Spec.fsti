module TLS13.Crypto.Spec

module B = TLS13.Bytes
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8

type bytes_of_len (n:nat) = B.bytes_of_len n

type digest32 = bytes_of_len 32
type secret = bytes_of_len 32
type aead_key = bytes_of_len 32
type aead_nonce = bytes_of_len 12
type x25519_private = bytes_of_len 32
type x25519_public = bytes_of_len 32
type x25519_shared_secret = secret
type public_key = B.bytes
type signature = B.bytes

val sha256: msg:B.bytes -> Tot digest32

val hmac_sha256: key:B.bytes -> msg:B.bytes -> Tot digest32

val hkdf_extract: salt:B.bytes -> ikm:B.bytes -> Tot secret

val hkdf_expand_label:
  secret:B.bytes ->
  label:B.bytes ->
  context:B.bytes ->
  len:nat ->
  Tot (bytes_of_len len)

val x25519_public_from_private:
  sk:B.bytes ->
  Tot x25519_public

val x25519_shared:
  sk:B.bytes ->
  pk:B.bytes ->
  Tot (option x25519_shared_secret)

val lemma_x25519_shared_agreement:
  client_sk:x25519_private ->
  server_sk:x25519_private ->
  client_pub:x25519_public ->
  server_pub:x25519_public ->
  Lemma
    (requires
      x25519_public_from_private client_sk == client_pub /\
      x25519_public_from_private server_sk == server_pub)
    (ensures
      x25519_shared client_sk server_pub ==
      x25519_shared server_sk client_pub)

let nonce_byte (seq:nat) (divisor:pos) : U8.t =
  U8.uint_to_t ((seq / divisor) % 256)

let byte_at (bytes:B.bytes) (i:nat) : GTot U8.t =
  if i < B.length bytes then Seq.index bytes i else 0uy

let update_byte
  (bytes:B.bytes)
  (i:nat)
  (value:U8.t)
  : GTot B.bytes =
  if i < B.length bytes then Seq.upd bytes i value else bytes

let hkdf_label_info_length
  (label:B.bytes)
  (context:B.bytes)
  : nat =
  10 + B.length label + B.length context

let copy_bytes_into
  (dst:B.bytes)
  (offset:nat)
  (src:B.bytes)
  : GTot (bytes_of_len (B.length dst)) =
  if offset + B.length src <= B.length dst
  then
    B.append
      (Seq.slice dst 0 offset)
      (B.append
        src
        (Seq.slice dst (offset + B.length src) (B.length dst)))
  else dst

(** Fixed-capacity representation of RFC 8446 HkdfLabel. Only the
    [hkdf_label_info_length label context] prefix is passed to HKDF-Expand. *)
[@@ "opaque_to_smt"]
let hkdf_label_info_buffer
  (label:B.bytes)
  (context:B.bytes)
  (len:nat)
  : GTot (bytes_of_len 520) =
  let info0 = B.zeros 520 in
  let info1 = update_byte info0 0 (U8.uint_to_t ((len / 256) % 256)) in
  let info2 = update_byte info1 1 (U8.uint_to_t (len % 256)) in
  let info3 =
    update_byte info2 2 (U8.uint_to_t ((6 + B.length label) % 256)) in
  let info4 = update_byte info3 3 0x74uy in
  let info5 = update_byte info4 4 0x6cuy in
  let info6 = update_byte info5 5 0x73uy in
  let info7 = update_byte info6 6 0x31uy in
  let info8 = update_byte info7 7 0x33uy in
  let info9 = update_byte info8 8 0x20uy in
  let info10 = copy_bytes_into info9 9 label in
  let info11 =
    update_byte info10 (9 + B.length label)
      (U8.uint_to_t (B.length context % 256)) in
  copy_bytes_into info11 (10 + B.length label) context

[@@ "opaque_to_smt"]
let record_nonce_from_bytes
  (static_iv:B.bytes)
  (seq4 seq5 seq6 seq7 seq8 seq9 seq10 seq11:U8.t)
  : GTot (bytes_of_len (B.length static_iv)) =
  let nonce4 =
    update_byte static_iv 4 (U8.logxor (byte_at static_iv 4) seq4) in
  let nonce5 =
    update_byte nonce4 5 (U8.logxor (byte_at nonce4 5) seq5) in
  let nonce6 =
    update_byte nonce5 6 (U8.logxor (byte_at nonce5 6) seq6) in
  let nonce7 =
    update_byte nonce6 7 (U8.logxor (byte_at nonce6 7) seq7) in
  let nonce8 =
    update_byte nonce7 8 (U8.logxor (byte_at nonce7 8) seq8) in
  let nonce9 =
    update_byte nonce8 9 (U8.logxor (byte_at nonce8 9) seq9) in
  let nonce10 =
    update_byte nonce9 10 (U8.logxor (byte_at nonce9 10) seq10) in
  update_byte nonce10 11 (U8.logxor (byte_at nonce10 11) seq11)

[@@ "opaque_to_smt"]
let tls13_record_nonce
  (static_iv:B.bytes)
  (seq:nat)
  : GTot (bytes_of_len (B.length static_iv)) =
  record_nonce_from_bytes static_iv
    (nonce_byte seq 72057594037927936)
    (nonce_byte seq 281474976710656)
    (nonce_byte seq 1099511627776)
    (nonce_byte seq 4294967296)
    (nonce_byte seq 16777216)
    (nonce_byte seq 65536)
    (nonce_byte seq 256)
    (nonce_byte seq 1)

val chacha20_poly1305_seal:
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Tot (bytes_of_len (B.length plaintext + 16))

val chacha20_poly1305_open:
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  ciphertext:B.bytes ->
  Tot (option (plaintext:B.bytes{B.length plaintext + 16 == B.length ciphertext}))

(**
  Trust assumption: AEAD correctness for honest encryption/decryption with the
  same key, nonce, and additional authenticated data.  This is not proved in the
  model; it is part of the cryptographic TCB used to lift protected byte replay
  to decrypted TLS messages.
**)
val lemma_chacha20_poly1305_open_seal:
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Lemma
    (chacha20_poly1305_open
      key
      nonce
      aad
      (chacha20_poly1305_seal key nonce aad plaintext) ==
      Some plaintext)

val verify_signature:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  Tot bool
