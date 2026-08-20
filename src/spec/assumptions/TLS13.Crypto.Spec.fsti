module TLS13.Crypto.Spec

module B = TLS13.Bytes
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8

type bytes_of_len (n:nat) = B.bytes_of_len n

type digest32 = bytes_of_len 32
type secret = bytes_of_len 32

(**
  The two AEAD algorithms ATLAS supports, corresponding to the two cipher
  suites it offers.  Both use a 12-byte nonce and a 16-byte tag, so record
  framing is independent of the choice; only the key length differs.
**)
type aead_alg =
  | AEAD_AES128_GCM
  | AEAD_CHACHA20_POLY1305

let aead_key_len (a:aead_alg) : n:nat{n == 16 \/ n == 32} =
  match a with
  | AEAD_AES128_GCM -> 16
  | AEAD_CHACHA20_POLY1305 -> 32

(**
  The negotiated AEAD algorithm is carried as an explicit tag: it lives on the
  record-layer `direction_state` and on `traffic_key_material`, both threaded
  from the accepted ServerHello's cipher suite.  It is deliberately NOT
  recovered from `B.length key` — key lengths collide across algorithms
  (AES-256-GCM and ChaCha20-Poly1305 are both 32 bytes), so length inference is
  neither sound in general nor an honest description of what was negotiated.
**)

type aead_key (a:aead_alg) = bytes_of_len (aead_key_len a)
type aead_key_any = k:B.bytes{B.length k == 16 \/ B.length k == 32}

(**
  Runtime buffers holding a traffic key are always 32 bytes wide, so that the
  buffer layout does not depend on the negotiated suite.  A 16-byte AES key is
  stored zero-padded to 32 bytes; the logical key is the `aead_key_len`-byte
  prefix.  `pad_key_32` is the spec-level image of that storage convention, so
  representation predicates can pin the full 32-byte buffer contents while the
  model keeps the exact-length key.
**)
let pad_key_32 (k:aead_key_any) : bytes_of_len 32 =
  Seq.append k (Seq.create (32 - B.length k) 0uy)

(** Total inverse of `pad_key_32`: recovers the logical key from a padded
    32-byte buffer.  Total (rather than refined) so it can appear in
    postconditions, where `requires` clauses are not in scope. **)
let unpad_key_32 (key:B.bytes) (key_len:nat) : B.bytes =
  if key_len < B.length key then Seq.slice key 0 key_len else key

(** At the full buffer width the padding is empty, so unpadding is the
    identity.  Stated with a pattern because `requires` clauses of a Pulse
    signature are not in scope for its `ensures`, so call sites must recover
    this from the buffer length alone. **)
let lemma_unpad_key_32_full (key:B.bytes) (key_len:nat)
  : Lemma (requires key_len >= B.length key)
          (ensures unpad_key_32 key key_len == key)
          [SMTPat (unpad_key_32 key key_len)]
  = ()

let lemma_pad_key_32_prefix (k:aead_key_any)
  : Lemma (ensures Seq.equal (Seq.slice (pad_key_32 k) 0 (B.length k)) k)
          [SMTPat (pad_key_32 k)]
  = ()

(** Round trip: unpadding a padded key at its own length recovers it. **)
let lemma_unpad_pad_key_32 (k:aead_key_any)
  : Lemma (ensures unpad_key_32 (pad_key_32 k) (B.length k) == k)
  = if B.length k < 32
    then Seq.lemma_eq_intro (Seq.slice (pad_key_32 k) 0 (B.length k)) k
    else Seq.lemma_eq_intro (pad_key_32 k) k

(** The logical AEAD key held by a 32-byte padded traffic-key buffer, given the
    negotiated algorithm.  Every layer that stores a padded key buffer alongside
    its algorithm projects it with this. **)
let logical_key (a:aead_alg) (k:B.bytes) : B.bytes =
  unpad_key_32 k (aead_key_len a)

let lemma_logical_key_length (a:aead_alg) (k:B.bytes)
  : Lemma (requires B.length k == 32)
          (ensures B.length (logical_key a k) == aead_key_len a)
          [SMTPat (logical_key a k)]
  = ()

(** `pad_key_32` is injective: the key length is recoverable, so no two
    distinct keys share a padded image. **)
let lemma_pad_key_32_injective (k1 k2:aead_key_any)
  : Lemma (requires B.length k1 == B.length k2 /\
                    Seq.equal (pad_key_32 k1) (pad_key_32 k2))
          (ensures Seq.equal k1 k2)
  = assert (Seq.equal k1 (Seq.slice (pad_key_32 k1) 0 (B.length k1)));
    assert (Seq.equal k2 (Seq.slice (pad_key_32 k2) 0 (B.length k2)))
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

(**
  secp256r1 (NIST P-256).  The private key is 32 bytes as for X25519, but the
  public value is the 65-byte uncompressed SEC1 point `0x04 || X || Y` that TLS
  puts in a `KeyShareEntry`.  The shared secret is the 32-byte X coordinate of
  the shared point (RFC 8446 section 7.4.2), so it has the same type as the
  X25519 one and the key schedule above it is unchanged.

  `p256_shared` is partial: unlike X25519 it can fail, because a peer's point
  must lie on the curve and P-256 has no all-zero-output convention to fall
  back on.
**)
type p256_private = bytes_of_len 32
type p256_public = bytes_of_len 65

val p256_public_from_private:
  sk:B.bytes ->
  Tot p256_public

val p256_shared:
  sk:B.bytes ->
  pk:B.bytes ->
  Tot (option x25519_shared_secret)

val lemma_p256_shared_agreement:
  client_sk:p256_private ->
  server_sk:p256_private ->
  client_pub:p256_public ->
  server_pub:p256_public ->
  Lemma
    (requires
      p256_public_from_private client_sk == client_pub /\
      p256_public_from_private server_sk == server_pub)
    (ensures
      p256_shared client_sk server_pub ==
      p256_shared server_sk client_pub)

(**
  The negotiated key-exchange group.  Like the AEAD algorithm, this is carried
  as an explicit tag and never recovered from a share's length: `kex_public_len`
  happens to be injective today, but the group is what the peer actually named
  in its `KeyShareEntry` and there is no reason to launder it through a size.
**)
type kex_group =
  | KexX25519
  | KexP256

let kex_public_len (g:kex_group) : n:nat{n == 32 \/ n == 65} =
  match g with
  | KexX25519 -> 32
  | KexP256 -> 65

type kex_private = bytes_of_len 32
type kex_public (g:kex_group) = bytes_of_len (kex_public_len g)
type kex_shared_secret = x25519_shared_secret

let kex_public_from_private (g:kex_group) (sk:B.bytes) : kex_public g =
  match g with
  | KexX25519 -> x25519_public_from_private sk
  | KexP256 -> p256_public_from_private sk

let kex_shared (g:kex_group) (sk:B.bytes) (pk:B.bytes) : option kex_shared_secret =
  match g with
  | KexX25519 -> x25519_shared sk pk
  | KexP256 -> p256_shared sk pk

(**
  Runtime buffers holding a peer key share are always 65 bytes wide -- the
  widest group -- so that the buffer layout does not depend on the negotiated
  group, exactly as `pad_key_32` does for AEAD keys.  A 32-byte X25519 share is
  stored zero-padded; the logical share is the `kex_public_len`-byte prefix, and
  which prefix that is comes from the explicit group tag, never from the buffer.
**)
type kex_public_any = k:B.bytes{B.length k == 32 \/ B.length k == 65}

let pad_share_65 (k:kex_public_any) : bytes_of_len 65 =
  Seq.append k (Seq.create (65 - B.length k) 0uy)

(** Total inverse of `pad_share_65`, in the same style as `unpad_key_32`. **)
let unpad_share_65 (share:B.bytes) (share_len:nat) : B.bytes =
  if share_len < B.length share then Seq.slice share 0 share_len else share

let lemma_unpad_share_65 (k:kex_public_any)
  : Lemma (unpad_share_65 (pad_share_65 k) (B.length k) == k)
          [SMTPat (unpad_share_65 (pad_share_65 k) (B.length k))]
  = assert (Seq.equal (Seq.slice (pad_share_65 k) 0 (B.length k)) k)

(**
  A 65-byte buffer is a *padded* share of width [share_len] when it is exactly
  [pad_share_65] of its own [share_len]-byte prefix -- i.e. the bytes past the
  logical share are zero.  This is the shape the ServerHello representation
  stores, and the shape [TLS13.KEX.kex_public_from_private_runtime] produces
  when handed a zeroed buffer.
**)
let padded_share_65 (share:B.bytes) (share_len:nat) : prop =
  B.length share == 65 /\
  (share_len == 32 \/ share_len == 65) /\
  Seq.equal share (pad_share_65 (unpad_share_65 share share_len))

let lemma_pad_share_65_injective (k1 k2:kex_public_any)
  : Lemma (requires Seq.equal (pad_share_65 k1) (pad_share_65 k2) /\
                    B.length k1 == B.length k2)
          (ensures Seq.equal k1 k2)
  = assert (Seq.equal k1 (Seq.slice (pad_share_65 k1) 0 (B.length k1)));
    assert (Seq.equal k2 (Seq.slice (pad_share_65 k2) 0 (B.length k2)))

let lemma_kex_shared_agreement
  (g:kex_group)
  (client_sk server_sk:kex_private)
  (client_pub server_pub:kex_public g)
  : Lemma
      (requires
        kex_public_from_private g client_sk == client_pub /\
        kex_public_from_private g server_sk == server_pub)
      (ensures
        kex_shared g client_sk server_pub ==
        kex_shared g server_sk client_pub)
  = match g with
    | KexX25519 -> lemma_x25519_shared_agreement client_sk server_sk client_pub server_pub
    | KexP256 -> lemma_p256_shared_agreement client_sk server_sk client_pub server_pub

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

val aead_seal:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Tot (bytes_of_len (B.length plaintext + 16))

val aead_open:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  ciphertext:B.bytes ->
  Tot (option (plaintext:B.bytes{B.length plaintext + 16 == B.length ciphertext}))

(**
  Trust assumption: AEAD correctness for honest encryption/decryption with the
  same algorithm, key, nonce, and additional authenticated data.  This is not
  proved in the model; it is part of the cryptographic TCB used to lift
  protected byte replay to decrypted TLS messages.

  Both supported algorithms have a 16-byte tag, so the ciphertext length
  relation above is algorithm-independent and the record framing proofs are
  unaffected by the choice of AEAD.
**)
val lemma_aead_open_seal:
  alg:aead_alg ->
  key:B.bytes ->
  nonce:B.bytes ->
  aad:B.bytes ->
  plaintext:B.bytes ->
  Lemma
    (aead_open
      alg
      key
      nonce
      aad
      (aead_seal alg key nonce aad plaintext) ==
      Some plaintext)

val verify_signature:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  Tot bool

(* The signature scheme a credential can produce, as a function of the
   credential's public key.  A TLS 1.3 credential's algorithm is determined by
   its SubjectPublicKeyInfo -- an RSA key can only produce rsa_pss_rsae_sha256
   in this profile and a P-256 key only ecdsa_secp256r1_sha256 -- so this is a
   function of the identity rather than an extra field the configuration has to
   carry.  It is what makes the server's CertificateVerify algorithm agile
   (parity gap G5) without indexing the credential predicate by a scheme. *)
val credential_signature_scheme:
  public_key:public_key ->
  Tot T.signature_scheme

(* The profile implements exactly two credential algorithms, so a runtime query
   of the credential's scheme has only two answers to distinguish. *)
val lemma_credential_signature_scheme_supported:
  public_key:public_key ->
  Lemma
    (ensures
      credential_signature_scheme public_key == T.Rsa_pss_rsae_sha256 \/
      credential_signature_scheme public_key == T.Ecdsa_secp256r1_sha256)
    [SMTPat (credential_signature_scheme public_key)]
