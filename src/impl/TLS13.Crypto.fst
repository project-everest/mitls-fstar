module TLS13.Crypto

(**
  The cryptographic primitives, implemented by calling hacl-pulse directly.

  Every function here views its public-byte ([FStar.UInt8.t]) arrays as
  hacl-pulse secret-byte arrays ([TLS13.Crypto.Secret.secret], the same
  pointer), calls the hacl-pulse function, and proves the result is the
  [TLS13.Crypto.Spec] value, whose definitions are hacl-pulse's
  specifications.  The specification is total and the hacl-pulse functions
  are not, so each function first checks the same length bounds as the
  specification and, outside them, produces the specification's fallback
  value (zeros or failure).

  Calls into hacl-pulse are never in tail position: Custard currently
  eta-reduces a tail call to a linked function into a partial application.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

friend TLS13.Crypto.Spec

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Crypto.Secret
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module SB = Spec.Byte
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem

(** {2 Sequence facts} *)

(** The bounds hacl-pulse's HMAC and HKDF preconditions need, stated per
    call so that no [pow2 61] equation reaches the solver's context (it
    derails the [pow2 16] reasoning behind every [size_t] literal). *)
let hmac_limits (k m: nat)
  : Lemma (requires k <= 65535 /\ m <= 65471)
          (ensures k < pow2 61 /\ SZ.fits (Spec.SHA2.block_len #Hacl.Secret.UInt32.t + m) /\
                   Spec.SHA2.block_len #Hacl.Secret.UInt32.t + m < pow2 61)
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 (64 + m);
    C.sha2_facts ()

let expand_limits (p i: nat)
  : Lemma (requires p <= 65535 /\ i <= 514)
          (ensures p < pow2 61 /\
                   Spec.SHA2.block_len #Hacl.Secret.UInt32.t + 32 + i + 1 < pow2 61 /\
                   SZ.fits (Spec.SHA2.block_len #Hacl.Secret.UInt32.t + 32 + i + 1))
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 (64 + 32 + i + 1);
    C.sha2_facts ()


let declassify_ext (s: Seq.seq S8.t) (t: B.bytes)
  : Lemma (requires Seq.length s == Seq.length t /\
                    (forall (i: nat). i < Seq.length s ==>
                       S8.v (Seq.index s i) == U8.v (Seq.index t i)))
          (ensures CS.declassify_seq s == t)
  = let aux (i: nat { i < Seq.length s })
      : Lemma (Seq.index (CS.declassify_seq s) i == Seq.index t i)
      = U8.v_inj (Seq.index (CS.declassify_seq s) i) (Seq.index t i) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (CS.declassify_seq s) t

let declassify_zeros (n: nat)
  : Lemma (CS.declassify_seq (Seq.create n (S8.classify 0uy)) == B.zeros n)
  = declassify_ext (Seq.create n (S8.classify 0uy)) (B.zeros n)

let classify_equal (a b: B.bytes)
  : Lemma (Seq.equal (CS.classify_seq a) (CS.classify_seq b) <==> Seq.equal a b)
  = let l1 () : Lemma (requires Seq.equal (CS.classify_seq a) (CS.classify_seq b))
                      (ensures Seq.equal a b)
      = Seq.lemma_eq_elim (CS.classify_seq a) (CS.classify_seq b);
        CS.declassify_classify a; CS.declassify_classify b in
    let l2 () : Lemma (requires Seq.equal a b)
                      (ensures Seq.equal (CS.classify_seq a) (CS.classify_seq b))
      = Seq.lemma_eq_elim a b in
    FStar.Classical.move_requires l1 ();
    FStar.Classical.move_requires l2 ()

let of_elems_vals (a: Seq.seq S8.t)
  : Lemma (CS.of_elems (SB.vals a) == CS.declassify_seq a)
  = SB.secrets_vals a

let of_elems_vals2 (a b: Seq.seq S8.t)
  : Lemma (CS.of_elems (Seq.append (SB.vals a) (SB.vals b)) ==
           CS.declassify_seq (Seq.append a b))
  = Seq.lemma_eq_intro (Seq.append (SB.vals a) (SB.vals b)) (SB.vals (Seq.append a b));
    SB.secrets_vals (Seq.append a b)

(** The pointwise postconditions of [Hacl.Impl.Copy] and [Hacl.Impl.Sub],
    turned into the sequence equalities the specification needs. *)
let seal_combine (n: nat) (vct vtag w vo: Seq.seq S8.t)
  : Lemma (requires Seq.length vct == n /\ Seq.length vtag == 16 /\
                    Seq.length w == n + 16 /\ Seq.length vo == n + 16 /\
                    (forall (k: nat). k < n ==> Seq.index w k == Seq.index vct k) /\
                    (forall (k: nat). k < n ==> Seq.index vo k == Seq.index w k) /\
                    (forall (k: nat). k < 16 ==> Seq.index vo (n + k) == Seq.index vtag k))
          (ensures vo == Seq.append vct vtag)
  = let aux (k: nat { k < n + 16 })
      : Lemma (Seq.index vo k == Seq.index (Seq.append vct vtag) k)
      = if k < n then () else assert (Seq.index vo (n + (k - n)) == Seq.index vtag (k - n)) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro vo (Seq.append vct vtag)

let window_eq (n m: nat) (a b: Seq.seq S8.t)
  : Lemma (requires Seq.length a == m /\ n + m <= Seq.length b /\
                    (forall (k: nat). k < m ==> Seq.index a k == Seq.index b (n + k)))
          (ensures a == Seq.slice b n (n + m))
  = Seq.lemma_eq_intro a (Seq.slice b n (n + m))

let prefix_eq (n: nat) (a b: Seq.seq S8.t)
  : Lemma (requires n <= Seq.length a /\ n <= Seq.length b /\
                    (forall (k: nat). k < n ==> Seq.index a k == Seq.index b k))
          (ensures Seq.slice a 0 n == Seq.slice b 0 n)
  = Seq.lemma_eq_intro (Seq.slice a 0 n) (Seq.slice b 0 n)

(** [n < 2^61], checked without constants that do not fit a 16-bit [size_t]. *)
let below_pow2_61 (n: nat)
  : Lemma (n / 32768 / 32768 / 32768 / 32768 < 2 <==> n < pow2 61)
  = FStar.Math.Lemmas.division_multiplication_lemma n 32768 32768;
    FStar.Math.Lemmas.division_multiplication_lemma n (32768 * 32768) 32768;
    FStar.Math.Lemmas.division_multiplication_lemma n (32768 * 32768 * 32768) 32768;
    assert_norm (pow2 61 == 2 * (32768 * 32768 * 32768 * 32768))


(** {2 Helpers} *)

fn zero_fill (a: array U8.t) (n: SZ.t)
  requires pts_to a 'old ** pure (Seq.length 'old == SZ.v n)
  ensures pts_to a (B.zeros (SZ.v n))
{
  CS.to_secret a;
  Copy.fill (CS.secret a) (S8.classify 0uy) n;
  CS.of_secret a;
  declassify_zeros (SZ.v n);
  ()
}

inline_for_extraction
fn below_pow2_61_sz (n: SZ.t)
  returns b: bool
  ensures pure (b <==> SZ.v n < pow2 61)
{
  let q1 = SZ.div n 32768sz;
  let q2 = SZ.div q1 32768sz;
  let q3 = SZ.div q2 32768sz;
  let q4 = SZ.div q3 32768sz;
  below_pow2_61 (SZ.v n);
  SZ.lt q4 2sz
}

inline_for_extraction
fn hmac_in_range_sz (k m: SZ.t)
  returns b: bool
  ensures pure (b <==> (SZ.v k <= 65535 /\ SZ.v m <= 65471))
{
  (SZ.lte k 65535sz && SZ.lte m 65471sz)
}

inline_for_extraction
fn aead_in_range_sz (p a: SZ.t)
  returns b: bool
  ensures pure (b <==> (SZ.v p <= C.aead_max_len /\ SZ.v a <= C.aead_max_len))
{
  (SZ.lte p 65280sz && SZ.lte a 65280sz)
}

(** {2 Randomness} *)

fn random_bytes (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old ** pure (B.length 'old == SZ.v out_len)
  returns ok: bool
  ensures exists* bytes. pts_to out bytes ** pure (B.length bytes == SZ.v out_len)
{
  TLS13.Crypto.Random.random_bytes out out_len
}

(** {2 Hashing} *)

fn hash_prefix (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (SZ.v input_len <= B.length 'msg /\
                 B.length 'old == 32)
  ensures pts_to input 'msg **
          pts_to out (C.sha256 (CL.raw_slice 'msg 0 (SZ.v input_len)))
{
  let small = below_pow2_61_sz input_len;
  let m = Ghost.hide (Seq.slice 'msg 0 (SZ.v input_len));
  C.sha256_eq m;
  if small {
    CS.to_secret input;
    CS.to_secret out;
    A.pts_to_len (CS.secret input);
    let s = Sub.sub (CS.secret input) 0sz input_len;
    CS.classify_slice 'msg 0 (SZ.v input_len);
    Hacl.Hash.SHA2.sha256 (CS.secret out) s input_len;
    Sub.unsub_id (CS.secret input) 0 (SZ.v input_len) s;
    CS.of_secret input;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn sha256 (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (B.length 'msg == SZ.v input_len /\ B.length 'old == 32)
  ensures pts_to input 'msg ** pts_to out (C.sha256 'msg)
{
  hash_prefix input input_len out;
  assert pure (Seq.equal (CL.raw_slice 'msg 0 (SZ.v input_len)) 'msg);
  ()
}

fn sha256_prefix (input: array U8.t) (input_len: SZ.t) (out: array U8.t)
  requires pts_to input 'msg **
           pts_to out 'old **
           pure (SZ.v input_len <= B.length 'msg /\
                 B.length 'old == 32)
  ensures pts_to input 'msg **
          pts_to out (C.sha256 (CL.raw_slice 'msg 0 (SZ.v input_len)))
{
  hash_prefix input input_len out
}

fn sha256_empty (out: array U8.t)
  requires pts_to out 'old **
           pure (B.length 'old == 32)
  ensures pts_to out (C.sha256 B.empty)
{
  let mut e = [| 0uy; 1sz |];
  hash_prefix e 0sz out;
  assert pure (Seq.equal (CL.raw_slice (Seq.create 1 0uy) 0 0) B.empty);
  ()
}

(** {2 HMAC and HKDF} *)

fn hmac_sha256 (key: array U8.t) (key_len: SZ.t) (msg: array U8.t) (msg_len: SZ.t) (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to msg 'msg_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'msg_bytes == SZ.v msg_len /\
                 B.length 'old == 32)
  ensures pts_to key 'key_bytes **
          pts_to msg 'msg_bytes **
          pts_to out (C.hmac_sha256 'key_bytes 'msg_bytes)
{
  C.hmac_sha256_eq 'key_bytes 'msg_bytes;
  let ok = hmac_in_range_sz key_len msg_len;
  if ok {
    hmac_limits (SZ.v key_len) (SZ.v msg_len);
    CS.to_secret key;
    CS.to_secret msg;
    CS.to_secret out;
    Hacl.HMAC.hmac_sha256 (CS.secret out) (CS.secret key) key_len (CS.secret msg) msg_len;
    CS.of_secret key;
    CS.of_secret msg;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn equal32 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)
{
  CS.to_secret a;
  CS.to_secret b;
  let ok = Hacl.Impl.Bytes.bytes_eq (CS.secret a) (CS.secret b) 32sz;
  CS.of_secret a;
  CS.of_secret b;
  classify_equal 'a_bytes 'b_bytes;
  ok
}

fn equal12 (a: array U8.t) (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 12 /\ B.length 'b_bytes == 12)
  returns ok: bool
  ensures pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pure (ok <==> Seq.equal 'a_bytes 'b_bytes)
{
  CS.to_secret a;
  CS.to_secret b;
  let ok = Hacl.Impl.Bytes.bytes_eq (CS.secret a) (CS.secret b) 12sz;
  CS.of_secret a;
  CS.of_secret b;
  classify_equal 'a_bytes 'b_bytes;
  ok
}

fn hkdf_extract (salt: array U8.t) (salt_len: SZ.t) (ikm: array U8.t) (ikm_len: SZ.t) (out: array U8.t)
  requires pts_to salt 'salt_bytes **
           pts_to ikm 'ikm_bytes **
           pts_to out 'old **
           pure (B.length 'salt_bytes == SZ.v salt_len /\
                 B.length 'ikm_bytes == SZ.v ikm_len /\
                 B.length 'old == 32)
  ensures pts_to salt 'salt_bytes **
          pts_to ikm 'ikm_bytes **
          pts_to out (C.hkdf_extract 'salt_bytes 'ikm_bytes)
{
  C.hkdf_extract_eq 'salt_bytes 'ikm_bytes;
  let ok = hmac_in_range_sz salt_len ikm_len;
  if ok {
    hmac_limits (SZ.v salt_len) (SZ.v ikm_len);
    CS.to_secret salt;
    CS.to_secret ikm;
    CS.to_secret out;
    Hacl.HKDF.extract_sha256 (CS.secret out) (CS.secret salt) salt_len (CS.secret ikm) ikm_len;
    CS.of_secret salt;
    CS.of_secret ikm;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 32sz;
    ()
  }
}

fn hkdf_expand
  (secret: array U8.t)
  (info: array U8.t)
  (info_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#lbl: erased B.bytes)
  (#context: erased B.bytes)
  requires pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pts_to out 'old **
          pure (B.length 'secret_bytes == 32 /\
                B.length 'info_bytes == 520 /\
                B.length 'old == SZ.v out_len /\
                B.length (Ghost.reveal lbl) <= 249 /\
                B.length (Ghost.reveal context) <= 255 /\
                SZ.v out_len <= 8160 /\
                SZ.v info_len ==
                  C.hkdf_label_info_length
                    (Ghost.reveal lbl)
                    (Ghost.reveal context) /\
                'info_bytes ==
                  C.hkdf_label_info_buffer
                    (Ghost.reveal lbl)
                    (Ghost.reveal context)
                    (SZ.v out_len))
  ensures pts_to secret 'secret_bytes **
          pts_to info 'info_bytes **
          pure (B.length
                 (C.hkdf_expand_label
                   'secret_bytes
                   (Ghost.reveal lbl)
                   (Ghost.reveal context)
                   (SZ.v out_len)) == SZ.v out_len) **
          pts_to out (C.hkdf_expand_label
                       'secret_bytes
                       (Ghost.reveal lbl)
                       (Ghost.reveal context)
                       (SZ.v out_len))
{
  let prk_len = 32sz;
  C.hkdf_expand_label_eq 'secret_bytes lbl context (SZ.v out_len);
  expand_limits 32 (SZ.v info_len);
  CS.to_secret secret;
  CS.to_secret info;
  CS.to_secret out;
  A.pts_to_len (CS.secret info);
  A.pts_to_len (CS.secret out);
  let i = Sub.sub (CS.secret info) 0sz info_len;
  CS.classify_slice 'info_bytes 0 (SZ.v info_len);
  Hacl.HKDF.expand_sha256 (CS.secret out) out_len (CS.secret secret) prk_len i info_len;
  Sub.unsub_id (CS.secret info) 0 (SZ.v info_len) i;
  CS.of_secret secret;
  CS.of_secret info;
  CS.of_secret out;
  ()
}

(** {2 X25519} *)

fn x25519_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.x25519_public_from_private 'sk_bytes)
{
  C.x25519_public_from_private_eq 'sk_bytes;
  CS.to_secret sk;
  CS.to_secret out;
  Hacl.Curve25519.secret_to_public (CS.secret out) (CS.secret sk);
  CS.of_secret sk;
  CS.of_secret out;
  ()
}

fn x25519_ecdh (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> Some? (C.x25519_shared 'sk_bytes 'pk_bytes) /\
                        Some?.v (C.x25519_shared 'sk_bytes 'pk_bytes) == out_bytes) /\
                (not ok ==> None? (C.x25519_shared 'sk_bytes 'pk_bytes)))
{
  C.x25519_shared_eq 'sk_bytes 'pk_bytes;
  CS.to_secret sk;
  CS.to_secret pk;
  CS.to_secret out;
  let ok = Hacl.Curve25519.ecdh (CS.secret out) (CS.secret sk) (CS.secret pk);
  CS.of_secret sk;
  CS.of_secret pk;
  CS.of_secret out;
  ok
}

fn x25519_shared (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          (exists* shared.
            pts_to out shared **
            pure (B.length shared == 32 /\
                  (ok ==>
                   Some? (C.x25519_shared 'sk_bytes 'pk_bytes) /\
                   Some?.v (C.x25519_shared 'sk_bytes 'pk_bytes) == shared) /\
                  (not ok ==> C.x25519_shared 'sk_bytes 'pk_bytes == None)))
{
  x25519_ecdh sk pk out
}

let x25519_shared_call sk pk shared ok =
  B.length shared == 32 /\
  (ok ==> Some? (C.x25519_shared sk pk) /\ Some?.v (C.x25519_shared sk pk) == shared) /\
  (not ok ==> None? (C.x25519_shared sk pk))

let lemma_x25519_shared_call_success sk pk shared ok = ()

fn x25519_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 32 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (x25519_shared_call 'sk_bytes 'pk_bytes out_bytes ok)
{
  x25519_ecdh sk pk out
}

(** {2 P-256} *)

fn p256_public_from_private (sk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 65)
  ensures pts_to sk 'sk_bytes ** pts_to out (C.p256_public_from_private 'sk_bytes)
{
  C.p256_public_from_private_eq 'sk_bytes;
  CS.to_secret sk;
  let zraw : S8.t = S8.classify 0uy;
    let mut raw = [| zraw; 64sz |];
  let ok = Hacl.P256.Ecdh.dh_initiator raw (CS.secret sk);
  CS.of_secret sk;
  if ok {
    CS.to_secret out;
    Hacl.P256.Sec1.raw_to_uncompressed (CS.secret out) raw;
    CS.of_secret out;
    ()
  } else {
    zero_fill out 65sz;
    ()
  }
}

let p256_shared_call sk pk shared ok =
  B.length shared == 32 /\
  (ok ==> Some? (C.p256_shared sk pk) /\ Some?.v (C.p256_shared sk pk) == shared) /\
  (not ok ==> None? (C.p256_shared sk pk))

let lemma_p256_shared_call_success sk pk shared ok = ()

fn p256_shared_runtime (sk: array U8.t) (pk: array U8.t) (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'pk_bytes == 65 /\ B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk 'pk_bytes **
          pts_to out out_bytes **
          pure (p256_shared_call 'sk_bytes 'pk_bytes out_bytes ok)
{
  C.p256_shared_eq 'sk_bytes 'pk_bytes;
  CS.to_secret pk;
  let zraw : S8.t = S8.classify 0uy;
    let mut raw = [| zraw; 64sz |];
  let ok1 = Hacl.P256.Sec1.uncompressed_to_raw raw (CS.secret pk);
  CS.of_secret pk;
  if ok1 {
    CS.to_secret sk;
    let zsh : S8.t = S8.classify 0uy;
    let mut sh = [| zsh; 64sz |];
    Mem.track sh;
    let ok2 = Hacl.P256.Ecdh.dh_responder sh raw (CS.secret sk);
    CS.of_secret sk;
    with vsh. assert (A.pts_to sh vsh);
    if ok2 {
      CS.to_secret out;
      A.pts_to_len (CS.secret out);
      Copy.copy_prefix (CS.secret out) sh 32sz;
      with vo. assert (A.pts_to (CS.secret out) vo);
      window_eq 0 32 vo vsh;
      CS.of_secret out;
      Mem.wipe sh 64sz;
      true
    } else {
      Mem.wipe sh 64sz;
      false
    }
  } else {
    false
  }
}

(** {2 AEAD} *)

fn chacha20_poly1305_seal
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out (C.aead_seal C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)
{
  C.aead_seal_eq C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes;
  C.aead_limits ();
  let in_range = aead_in_range_sz plain_len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret plain;
    CS.to_secret out;
    A.pts_to_len (CS.secret out);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    let ct = Sub.sub (CS.secret out) 0sz plain_len;
    Hacl.Chacha20Poly1305.encrypt ct tag (CS.secret plain) plain_len (CS.secret aad) aad_len
      (CS.secret key) (CS.secret nonce);
    with vct vtag. assert (A.pts_to ct vct ** A.pts_to tag vtag);
    Sub.unsub (CS.secret out) 0 (SZ.v plain_len) ct;
    with w. assert (A.pts_to (CS.secret out) w);
    Copy.copy_at (CS.secret out) plain_len tag 16sz;
    with vo. assert (A.pts_to (CS.secret out) vo);
    seal_combine (SZ.v plain_len) vct vtag w vo;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret plain;
    CS.of_secret out;
    ()
  } else {
    A.pts_to_len out;
    zero_fill out (SZ.add plain_len 16sz);
    ()
  }
}

let chacha_open_post (key nonce aad cipher old: B.bytes) (ok: bool) (vmsg: Seq.seq S8.t)
  : Lemma
    (requires (
      let n = B.length cipher in
      let len = n - 16 in
      B.length key == 32 /\ B.length nonce == 12 /\ n >= 16 /\ B.length old == len /\
      C.aead_open_in_range aad cipher /\
      Seq.length vmsg == len /\
      (ok <==> Spec.Chacha20Poly1305.decrypt_ok (CS.classify_seq key) (CS.classify_seq nonce)
                 (CS.classify_seq aad) (CS.classify_seq (Seq.slice cipher 0 len))
                 (CS.classify_seq (Seq.slice cipher len n))) /\
      (if ok then vmsg == Spec.Chacha20Poly1305.decrypted (CS.classify_seq key)
                            (CS.classify_seq nonce) (CS.classify_seq (Seq.slice cipher 0 len))
       else vmsg == CS.classify_seq old)))
    (ensures (
      let r = C.aead_open C.AEAD_CHACHA20_POLY1305 key nonce aad cipher in
      (ok ==> Some? r /\ CS.declassify_seq vmsg == Some?.v r) /\
      (not ok ==> r == None /\ CS.declassify_seq vmsg == old)))
  = C.aead_open_eq C.AEAD_CHACHA20_POLY1305 key nonce aad cipher;
    CS.declassify_classify old;
    assert (C.norm 32 key == key);
    assert (C.norm 12 nonce == nonce)

let aead_open_out_of_range (alg: C.aead_alg) (key nonce aad cipher: B.bytes)
  : Lemma (requires not (C.aead_open_in_range aad cipher))
          (ensures C.aead_open alg key nonce aad cipher == None)
  = C.aead_open_eq alg key nonce aad cipher

fn chacha20_poly1305_open
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure ((ok ==> Some? (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
{
  C.aead_limits ();
  let len = SZ.sub cipher_len 16sz;
  let in_range = aead_in_range_sz len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret cipher;
    CS.to_secret out;
    A.pts_to_len (CS.secret cipher);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    Copy.copy_range tag 0sz (CS.secret cipher) len 16sz;
    with vtag. assert (A.pts_to tag vtag);
    CS.classify_slice 'cipher_bytes (SZ.v len) (SZ.v cipher_len);
    window_eq (SZ.v len) 16 vtag (CS.classify_seq 'cipher_bytes);
    let ct = Sub.sub (CS.secret cipher) 0sz len;
    CS.classify_slice 'cipher_bytes 0 (SZ.v len);
    let ok = Hacl.Chacha20Poly1305.decrypt (CS.secret out) ct len tag (CS.secret aad) aad_len
               (CS.secret key) (CS.secret nonce);
    Sub.unsub_id (CS.secret cipher) 0 (SZ.v len) ct;
    with vmsg. assert (A.pts_to (CS.secret out) vmsg);
    chacha_open_post 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes 'old ok vmsg;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret cipher;
    CS.of_secret out;
    ok
  } else {
    aead_open_out_of_range C.AEAD_CHACHA20_POLY1305 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes;
    false
  }
}

fn aes128_gcm_seal
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 16 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  ensures pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out (C.aead_seal C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes)
{
  C.aead_seal_eq C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'plain_bytes;
  C.aead_limits ();
  let in_range = aead_in_range_sz plain_len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret plain;
    CS.to_secret out;
    A.pts_to_len (CS.secret out);
    Copy.copy_at (CS.secret out) 0sz (CS.secret plain) plain_len;
    with vo0. assert (A.pts_to (CS.secret out) vo0);
    window_eq 0 (SZ.v plain_len) (CS.classify_seq 'plain_bytes) vo0;
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    let m = Sub.sub (CS.secret out) 0sz plain_len;
    Hacl.AES.GCM.aes128_encrypt tag m plain_len (CS.secret key) (CS.secret nonce) 12sz
      (CS.secret aad) aad_len;
    with vm vtag. assert (A.pts_to m vm ** A.pts_to tag vtag);
    Sub.unsub (CS.secret out) 0 (SZ.v plain_len) m;
    with w. assert (A.pts_to (CS.secret out) w);
    Copy.copy_at (CS.secret out) plain_len tag 16sz;
    with vo. assert (A.pts_to (CS.secret out) vo);
    seal_combine (SZ.v plain_len) vm vtag w vo;
    of_elems_vals2 vm vtag;
    CS.of_secret key;
    CS.of_secret nonce;
    CS.of_secret aad;
    CS.of_secret plain;
    CS.of_secret out;
    ()
  } else {
    A.pts_to_len out;
    zero_fill out (SZ.add plain_len 16sz);
    ()
  }
}

let gcm_fits (a m: nat)
  : Lemma (requires a <= C.aead_max_len /\ m <= C.aead_max_len)
          (ensures SZ.fits 28 /\ SZ.fits (a + 16) /\ SZ.fits (m + 16))
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 28;
    SZ.fits_at_least_16 (a + 16);
    SZ.fits_at_least_16 (m + 16)

let gcm_open_post (key nonce aad cipher: B.bytes) (ok: bool) (vm: Seq.seq S8.t)
  : Lemma
    (requires (
      let n = B.length cipher in
      let len = n - 16 in
      B.length key == 16 /\ B.length nonce == 12 /\ n >= 16 /\
      C.aead_open_in_range aad cipher /\
      Seq.length vm == len /\
      Spec.GCM.iv_ok (SB.vals (CS.classify_seq nonce)) /\
      Spec.GCM.aad_ok (SB.vals (CS.classify_seq aad)) /\
      Spec.GCM.msg_ok (SB.vals (CS.classify_seq (Seq.slice cipher 0 len))) /\
      (let d = Spec.GCM.gcm_decrypt Spec.AES.AES128 (SB.vals (CS.classify_seq key))
                 (SB.vals (CS.classify_seq nonce)) (SB.vals (CS.classify_seq aad))
                 (SB.vals (CS.classify_seq (Seq.slice cipher 0 len)))
                 (SB.vals (CS.classify_seq (Seq.slice cipher len n))) in
       (ok ==> Some? d /\ SB.vals vm == Some?.v d) /\
       (not ok ==> None? d))))
    (ensures (
      let r = C.aead_open C.AEAD_AES128_GCM key nonce aad cipher in
      (ok ==> Some? r /\ CS.declassify_seq vm == Some?.v r) /\
      (not ok ==> r == None)))
  = C.aead_open_eq C.AEAD_AES128_GCM key nonce aad cipher;
    of_elems_vals vm;
    assert (C.norm 16 key == key);
    assert (C.norm 12 nonce == nonce)

fn aes128_gcm_open
  (key: array U8.t)
  (nonce: array U8.t)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires pts_to key 'key_bytes **
           pts_to nonce 'nonce_bytes **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 16 /\
                 B.length 'nonce_bytes == 12 /\
                 B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to key 'key_bytes **
          pts_to nonce 'nonce_bytes **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure ((ok ==> Some? (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes) /\
                        out_bytes == Some?.v (C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes)) /\
                (not ok ==> C.aead_open C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes == None /\
                            out_bytes == 'old))
{
  C.aead_limits ();
  let len = SZ.sub cipher_len 16sz;
  let in_range = aead_in_range_sz len aad_len;
  if in_range {
    CS.to_secret key;
    CS.to_secret nonce;
    CS.to_secret aad;
    CS.to_secret cipher;
    A.pts_to_len (CS.secret cipher);
    let ztag : S8.t = S8.classify 0uy;
    let mut tag = [| ztag; 16sz |];
    Copy.copy_range tag 0sz (CS.secret cipher) len 16sz;
    with vtag. assert (A.pts_to tag vtag);
    CS.classify_slice 'cipher_bytes (SZ.v len) (SZ.v cipher_len);
    window_eq (SZ.v len) 16 vtag (CS.classify_seq 'cipher_bytes);
    (* GCM decrypts in place and leaves the ciphertext behind on failure,
       but a failed open must leave [out] untouched: decrypt in a copy. *)
    let tmp = Mem.alloc #S8.t (S8.classify 0uy) cipher_len;
    Copy.copy_prefix tmp (CS.secret cipher) len;
    with vt0. assert (A.pts_to tmp vt0);
    CS.classify_slice 'cipher_bytes 0 (SZ.v len);
    prefix_eq (SZ.v len) vt0 (CS.classify_seq 'cipher_bytes);
    let m = Sub.sub tmp 0sz len;
    gcm_fits (SZ.v aad_len) (SZ.v len);
    let ok = Hacl.AES.GCM.aes128_decrypt m len tag (CS.secret key) (CS.secret nonce) 12sz
               (CS.secret aad) aad_len;
    with vm. assert (A.pts_to m vm);
    gcm_open_post 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes ok vm;
    if ok {
      CS.to_secret out;
      Copy.copy_exact (CS.secret out) m len;
      CS.of_secret out;
      Sub.unsub tmp 0 (SZ.v len) m;
      Mem.free tmp cipher_len;
      CS.of_secret key;
      CS.of_secret nonce;
      CS.of_secret aad;
      CS.of_secret cipher;
      true
    } else {
      Sub.unsub tmp 0 (SZ.v len) m;
      Mem.free tmp cipher_len;
      CS.of_secret key;
      CS.of_secret nonce;
      CS.of_secret aad;
      CS.of_secret cipher;
      false
    }
  } else {
    aead_open_out_of_range C.AEAD_AES128_GCM 'key_bytes 'nonce_bytes 'aad_bytes 'cipher_bytes;
    false
  }
}
