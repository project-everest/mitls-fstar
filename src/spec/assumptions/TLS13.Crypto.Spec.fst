module TLS13.Crypto.Spec

(**
  The cryptographic primitives of the model, defined by hacl-pulse's
  specifications.

  Two gaps between the two sides are bridged here:

  - hacl-pulse specifies over secret bytes ([Hacl.Secret.UInt8.t], or
    [Spec.Byte.elem] for AES-GCM) while TLS uses public [FStar.UInt8.t]
    bytes.  [TLS13.Crypto.Secret] converts; underneath the two are the same.

  - hacl-pulse's specifications are ghost ([GTot]): the value of a secret
    byte is ghost.  The model's primitives are therefore ghost too; the
    model only ever uses them in specifications and proofs.

  hacl-pulse's specifications are also partial: each is defined only for
  inputs within its length limits (and with exact key and nonce lengths).
  The model's primitives are total, so outside those limits they return a
  fixed value -- zeros for a digest, key or ciphertext, [None] for a
  decryption or key exchange -- which the implementation in [TLS13.Crypto]
  reproduces with run-time length checks.  The limits are far above
  anything TLS uses.
**)

module B = TLS13.Bytes
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module CS = TLS13.Crypto.Secret
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module SB = Spec.Byte
module SHA = Spec.SHA2
module SC = Spec.SHA2.Constants
module HM = Spec.HMAC
module HK = Spec.HKDF
module X = Spec.Curve25519
module HP = Spec.HPKE
module HPX = Spec.HPKE.Correctness
module P = Spec.P256
module Ch = Spec.Chacha20
module CP = Spec.Chacha20Poly1305
module CPX = Spec.Chacha20Poly1305.Correctness
module G = Spec.GCM
module GX = Spec.GCM.Correctness
module AES = Spec.AES

open Hacl.Secret.Word.Instances

noextract
let c (s: B.bytes) : GTot (r: Seq.seq S8.t { Seq.length r == B.length s }) = CS.classify_seq s

noextract
let d (s: Seq.seq S8.t) : GTot (r: B.bytes { B.length r == Seq.length s }) = CS.declassify_seq s

let sha2_facts ()
  : Lemma (SHA.max_input #S32.t == pow2 61 /\ SHA.block_len #S32.t == 64 /\
           SHA.hash_bytes SC.sha2_256 == 32 /\ pow2 61 == 2305843009213693952)
  = assert_norm (pow2 61 == 2305843009213693952);
    assert_norm (SHA.max_input #S32.t == pow2 61);
    assert_norm (SHA.block_len #S32.t == 64);
    assert_norm (SHA.hash_bytes SC.sha2_256 == 32)

(** {2 Hashing} *)

noextract
let sha256_g (msg: B.bytes) : GTot digest32 =
  sha2_facts ();
  if B.length msg < pow2 61
  then d (SHA.hash SC.sha2_256 (c msg))
  else B.zeros 32

let sha256 msg = sha256_g msg

let sha256_eq (msg: B.bytes) : Lemma (sha256 msg == sha256_g msg) = ()

(** HMAC and HKDF-Extract, over a key and message bounded so that the
    implementation can check the bound with 16-bit size arithmetic. *)
unfold let hmac_in_range (key msg: B.bytes) : bool =
  B.length key <= 65535 && B.length msg <= 65471

noextract
let hmac_g2 (key msg: B.bytes) : GTot digest32 =
  sha2_facts ();
  if hmac_in_range key msg
  then begin
    let k = c key in
    let m = c msg in
    assert (Seq.length k < SHA.max_input #S32.t);
    assert (SHA.block_len #S32.t + Seq.length m < SHA.max_input #S32.t);
    let r = HM.hmac SC.sha2_256 k m in
    assert (Seq.length r == 32);
    d r
  end
  else B.zeros 32

let hmac_sha256 key msg = hmac_g2 key msg

let hmac_sha256_eq (key msg: B.bytes) : Lemma (hmac_sha256 key msg == hmac_g2 key msg) = ()

noextract
let hkdf_extract_g2 (salt ikm: B.bytes) : GTot secret =
  sha2_facts ();
  if hmac_in_range salt ikm
  then begin
    let k = c salt in
    let m = c ikm in
    assert (Seq.length k < SHA.max_input #S32.t);
    assert (SHA.block_len #S32.t + Seq.length m < SHA.max_input #S32.t);
    let r = HK.extract SC.sha2_256 k m in
    assert (Seq.length r == 32);
    d r
  end
  else B.zeros 32

let hkdf_extract salt ikm = hkdf_extract_g2 salt ikm

let hkdf_extract_eq (salt ikm: B.bytes)
  : Lemma (hkdf_extract salt ikm == hkdf_extract_g2 salt ikm) = ()

(** {2 Key exchange} *)

noextract
let x25519_public_from_private_g (sk: B.bytes) : GTot x25519_public =
  if B.length sk = 32 then d (X.secret_to_public (c sk)) else B.zeros 32

let x25519_public_from_private sk = x25519_public_from_private_g sk

let x25519_public_from_private_eq (sk: B.bytes)
  : Lemma (x25519_public_from_private sk == x25519_public_from_private_g sk) = ()

noextract
let map_d (#n: nat) (o: option (Seq.lseq S8.t n)) : GTot (option (bytes_of_len n)) =
  match o with Some s -> Some (d s) | None -> None

noextract
let x25519_shared_g (skpk: B.bytes & B.bytes) : GTot (option x25519_shared_secret) =
  let (sk, pk) = skpk in
  if B.length sk = 32 && B.length pk = 32
  then map_d (HP.dh HP.DH_X25519 (c sk) (c pk))
  else None

let x25519_shared sk pk = x25519_shared_g (sk, pk)

let x25519_shared_eq (sk pk: B.bytes)
  : Lemma (x25519_shared sk pk == x25519_shared_g (sk, pk)) = ()

let lemma_x25519_shared_agreement client_sk server_sk client_pub server_pub =
  HPX.dh_agree HP.DH_X25519 (c client_sk) (c server_sk)

noextract
let p256_public_from_private_g (sk: B.bytes) : GTot p256_public =
  if B.length sk = 32
  then (match HP.secret_to_public HP.DH_P256 (c sk) with
        | Some p -> d p
        | None -> B.zeros 65)
  else B.zeros 65

let p256_public_from_private sk = p256_public_from_private_g sk

let p256_public_from_private_eq (sk: B.bytes)
  : Lemma (p256_public_from_private sk == p256_public_from_private_g sk) = ()

noextract
let p256_shared_g (skpk: B.bytes & B.bytes) : GTot (option x25519_shared_secret) =
  let (sk, pk) = skpk in
  if B.length sk = 32 && B.length pk = 65
  then map_d (HP.dh HP.DH_P256 (c sk) (c pk))
  else None

let p256_shared sk pk = p256_shared_g (sk, pk)

let p256_shared_eq (sk pk: B.bytes)
  : Lemma (p256_shared sk pk == p256_shared_g (sk, pk)) = ()

(** A private key outside [1, order) has no public key, so
    [p256_public_from_private] falls back to all zeros -- which lacks the
    uncompressed-point tag and so is rejected by every peer -- and the key
    itself is rejected by [dh_responder]. *)
let p256_invalid_sk (sk: p256_private) (pk: p256_public)
  : Lemma (requires None? (HP.secret_to_public HP.DH_P256 (c sk)))
          (ensures p256_shared sk pk == None /\
                   p256_public_from_private sk == B.zeros 65)
  = ()

let p256_shared_zeros (sk: p256_private)
  : Lemma (p256_shared sk (B.zeros 65) == None)
  = assert (S8.v (Seq.index (c (B.zeros 65)) 0) == 0)

let lemma_p256_shared_agreement client_sk server_sk client_pub server_pub =
  match HP.secret_to_public HP.DH_P256 (c client_sk),
        HP.secret_to_public HP.DH_P256 (c server_sk) with
  | Some pA, Some pB ->
    HPX.dh_agree HP.DH_P256 (c client_sk) (c server_sk);
    p256_public_from_private_eq client_sk;
    p256_public_from_private_eq server_sk;
    assert (c client_pub == pA);
    assert (c server_pub == pB);
    p256_shared_eq client_sk server_pub;
    p256_shared_eq server_sk client_pub
  | None, _ -> p256_shared_zeros server_sk; p256_invalid_sk client_sk server_pub
  | _, None -> p256_shared_zeros client_sk; p256_invalid_sk server_sk client_pub

(** {2 HKDF-Expand-Label} *)

unfold let hkdf_expand_in_range (secret label context: B.bytes) (len: nat) : bool =
  B.length secret <= 65535 && B.length label <= 249 &&
  B.length context <= 255 && len <= 8160

noextract
let hkdf_info (label context: B.bytes) (len: nat)
  : GTot (r: B.bytes { B.length label <= 249 /\ B.length context <= 255 ==>
                       B.length r == hkdf_label_info_length label context })
  = if B.length label <= 249 && B.length context <= 255
    then Seq.slice (hkdf_label_info_buffer label context len) 0
           (hkdf_label_info_length label context)
    else B.empty

noextract
let hkdf_expand_label_g4 (secret label context: B.bytes) (len: nat)
  : GTot (bytes_of_len len) =
  sha2_facts ();
  if hkdf_expand_in_range secret label context len
  then d (HK.expand SC.sha2_256 (c secret) (c (hkdf_info label context len)) len)
  else B.zeros len

let hkdf_expand_label secret label context len =
  hkdf_expand_label_g4 secret label context len

let hkdf_expand_label_eq (secret label context: B.bytes) (len: nat)
  : Lemma (hkdf_expand_label secret label context len ==
           hkdf_expand_label_g4 secret label context len) = ()

(** {2 AEAD} *)

unfold let aead_in_range (aad plaintext: B.bytes) : bool =
  B.length plaintext <= aead_max_len && B.length aad <= aead_max_len

unfold let aead_open_in_range (aad ciphertext: B.bytes) : bool =
  B.length ciphertext >= 16 && B.length ciphertext - 16 <= aead_max_len &&
  B.length aad <= aead_max_len

noextract
let norm (n: nat) (s: B.bytes) : bytes_of_len n =
  if B.length s = n then s else B.zeros n

let aead_limits ()
  : Lemma (aead_max_len <= Ch.max_len 1ul /\ aead_max_len <= G.max_msg /\
           aead_max_len <= G.max_aad /\ 12 <= G.max_aad)
  = assert_norm (aead_max_len <= Ch.max_len 1ul);
    assert_norm (aead_max_len <= G.max_msg);
    assert_norm (aead_max_len <= G.max_aad)

noextract
let gcm_seal (key nonce aad plaintext: B.bytes)
  : Ghost (bytes_of_len (B.length plaintext + 16))
          (requires aead_in_range aad plaintext) (ensures fun _ -> True)
  = aead_limits ();
    let k = SB.vals (c (norm 16 key)) in
    let n = SB.vals (c (norm 12 nonce)) in
    let a = SB.vals (c aad) in
    let m = SB.vals (c plaintext) in
    GX.decrypt_encrypt AES.AES128 k n a m;
    let (ct, tag) = G.gcm_encrypt AES.AES128 k n a m in
    CS.of_elems (Seq.append ct tag)

noextract
let aead_seal_g5 (alg: aead_alg) (key nonce aad plaintext: B.bytes)
  : GTot (bytes_of_len (B.length plaintext + 16)) =
  aead_limits ();
  if aead_in_range aad plaintext then
    match alg with
    | AEAD_CHACHA20_POLY1305 ->
      let (ct, tag) = CP.encrypt (c (norm 32 key)) (c (norm 12 nonce)) (c aad) (c plaintext) in
      d (Seq.append ct tag)
    | AEAD_AES128_GCM -> gcm_seal key nonce aad plaintext
  else B.zeros (B.length plaintext + 16)

let aead_seal alg key nonce aad plaintext =
  aead_seal_g5 alg key nonce aad plaintext

let aead_seal_eq (alg: aead_alg) (key nonce aad plaintext: B.bytes)
  : Lemma (aead_seal alg key nonce aad plaintext == aead_seal_g5 alg key nonce aad plaintext) = ()

type opened (n: nat) = p: B.bytes { B.length p + 16 == n }

noextract
let gcm_open (key nonce aad ciphertext: B.bytes)
  : Ghost (option (opened (B.length ciphertext)))
          (requires aead_open_in_range aad ciphertext) (ensures fun _ -> True)
  = aead_limits ();
    let len = B.length ciphertext - 16 in
    let k = SB.vals (c (norm 16 key)) in
    let n = SB.vals (c (norm 12 nonce)) in
    let a = SB.vals (c aad) in
    let m = SB.vals (c (Seq.slice ciphertext 0 len)) in
    let t = SB.vals (c (Seq.slice ciphertext len (B.length ciphertext))) in
    match G.gcm_decrypt AES.AES128 k n a m t with
    | Some p -> if Seq.length p = len then Some (CS.of_elems p) else None
    | None -> None

noextract
let chacha_open (key nonce aad ciphertext: B.bytes)
  : Ghost (option (opened (B.length ciphertext)))
          (requires aead_open_in_range aad ciphertext) (ensures fun _ -> True)
  = aead_limits ();
    let len = B.length ciphertext - 16 in
    let k = c (norm 32 key) in
    let n = c (norm 12 nonce) in
    let m = c (Seq.slice ciphertext 0 len) in
    let t = c (Seq.slice ciphertext len (B.length ciphertext)) in
    if FStar.IndefiniteDescription.strong_excluded_middle (CP.decrypt_ok k n (c aad) m t)
    then Some (d (CP.decrypted k n m))
    else None

noextract
let aead_open_g5 (alg: aead_alg) (key nonce aad ciphertext: B.bytes)
  : GTot (option (opened (B.length ciphertext))) =
  if aead_open_in_range aad ciphertext then
    match alg with
    | AEAD_CHACHA20_POLY1305 -> chacha_open key nonce aad ciphertext
    | AEAD_AES128_GCM -> gcm_open key nonce aad ciphertext
  else None

let aead_open alg key nonce aad ciphertext =
  match aead_open_g5 alg key nonce aad ciphertext with
  | Some p -> Some (p <: B.bytes)
  | None -> None

let aead_open_eq (alg: aead_alg) (key nonce aad ciphertext: B.bytes)
  : Lemma ((None? (aead_open alg key nonce aad ciphertext) <==>
            None? (aead_open_g5 alg key nonce aad ciphertext)) /\
           (Some? (aead_open_g5 alg key nonce aad ciphertext) ==>
            Some?.v (aead_open alg key nonce aad ciphertext) ==
            (Some?.v (aead_open_g5 alg key nonce aad ciphertext) <: B.bytes)))
  = ()

let split_sealed (ct tag: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length ct == n /\ Seq.length tag == 16)
          (ensures (let s = d (Seq.append ct tag) in
                    c (Seq.slice s 0 n) == ct /\
                    c (Seq.slice s n (n + 16)) == tag))
  = let s = d (Seq.append ct tag) in
    CS.classify_slice s 0 n;
    CS.classify_slice s n (n + 16);
    Seq.lemma_eq_intro (Seq.slice (Seq.append ct tag) 0 n) ct;
    Seq.lemma_eq_intro (Seq.slice (Seq.append ct tag) n (n + 16)) tag

let chacha_open_seal (key nonce aad plaintext: B.bytes)
  : Lemma (requires aead_in_range aad plaintext)
          (ensures (let s = aead_seal_g5 AEAD_CHACHA20_POLY1305 key nonce aad plaintext in
                    Some? (aead_open_g5 AEAD_CHACHA20_POLY1305 key nonce aad s) /\
                    (Some?.v (aead_open_g5 AEAD_CHACHA20_POLY1305 key nonce aad s) <: B.bytes)
                      == plaintext))
  = aead_limits ();
    let n = B.length plaintext in
    let k = c (norm 32 key) in
    let nn = c (norm 12 nonce) in
    let r = CP.encrypt k nn (c aad) (c plaintext) in
    let ct = fst r in
    let tag = snd r in
    CPX.decrypt_encrypt k nn (c aad) (c plaintext);
    let s = d (Seq.append ct tag) in
    assert (aead_seal_g5 AEAD_CHACHA20_POLY1305 key nonce aad plaintext == s);
    split_sealed ct tag n;
    assert (CP.decrypted k nn ct == c plaintext);
    assert (chacha_open key nonce aad s == Some (d (c plaintext)))

let gcm_open_seal (key nonce aad plaintext: B.bytes)
  : Lemma (requires aead_in_range aad plaintext)
          (ensures (let s = aead_seal_g5 AEAD_AES128_GCM key nonce aad plaintext in
                    Some? (aead_open_g5 AEAD_AES128_GCM key nonce aad s) /\
                    (Some?.v (aead_open_g5 AEAD_AES128_GCM key nonce aad s) <: B.bytes)
                      == plaintext))
  = aead_limits ();
    let n = B.length plaintext in
    let k = SB.vals (c (norm 16 key)) in
    let nn = SB.vals (c (norm 12 nonce)) in
    let a = SB.vals (c aad) in
    let m = SB.vals (c plaintext) in
    GX.decrypt_encrypt AES.AES128 k nn a m;
    let r = G.gcm_encrypt AES.AES128 k nn a m in
    let ct = fst r in
    let tag = snd r in
    let s = d (Seq.append (SB.secrets ct) (SB.secrets tag)) in
    Seq.lemma_eq_intro (SB.secrets (Seq.append ct tag))
                       (Seq.append (SB.secrets ct) (SB.secrets tag));
    assert (aead_seal_g5 AEAD_AES128_GCM key nonce aad plaintext == s);
    split_sealed (SB.secrets ct) (SB.secrets tag) n;
    assert (G.gcm_decrypt AES.AES128 k nn a ct tag == Some m);
    assert (SB.secrets m == c plaintext);
    assert (CS.of_elems m == plaintext)

let some_eq (#t: Type) (o: option t) (x: t)
  : Lemma (requires Some? o /\ Some?.v o == x) (ensures o == Some x) = ()

let lemma_aead_open_seal alg key nonce aad plaintext =
  let s = aead_seal alg key nonce aad plaintext in
  aead_seal_eq alg key nonce aad plaintext;
  aead_open_eq alg key nonce aad s;
  (match alg with
   | AEAD_CHACHA20_POLY1305 -> chacha_open_seal key nonce aad plaintext
   | AEAD_AES128_GCM -> gcm_open_seal key nonce aad plaintext);
  some_eq (aead_open alg key nonce aad (aead_seal alg key nonce aad plaintext)) plaintext

(** {2 Signatures}

    Signature verification is OpenSSL's, not hacl-pulse's, so it stays an
    assumption: a function the model names but does not define. *)

assume val verify_signature_ax:
  scheme:T.signature_scheme ->
  public_key:public_key ->
  message:B.bytes ->
  signature:signature ->
  Tot bool

let verify_signature = verify_signature_ax

assume val credential_signature_scheme_ax: public_key:public_key -> Tot T.signature_scheme

let credential_signature_scheme = credential_signature_scheme_ax

assume val lemma_credential_signature_scheme_supported_ax:
  public_key:public_key ->
  Lemma
    (ensures
      credential_signature_scheme_ax public_key == T.Rsa_pss_rsae_sha256 \/
      credential_signature_scheme_ax public_key == T.Ecdsa_secp256r1_sha256)

let lemma_credential_signature_scheme_supported public_key =
  lemma_credential_signature_scheme_supported_ax public_key
