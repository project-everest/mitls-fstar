module TLS13.KEX

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module AC = TLS13.Impl.ArrayCopy
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Crypto = TLS13.Crypto
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

let kex_group_eq (a b:C.kex_group) : r:bool{r <==> a == b} =
  match a, b with
  | C.KexX25519, C.KexX25519 -> true
  | C.KexP256, C.KexP256 -> true
  | _, _ -> false

let kex_public_len_sz (g:C.kex_group) : n:SZ.t{SZ.v n == C.kex_public_len g} =
  match g with
  | C.KexX25519 -> 32sz
  | C.KexP256 -> 65sz

let kex_shared_call g sk pk shared ok =
  match g with
  | C.KexX25519 -> Crypto.x25519_shared_call sk pk shared ok
  | C.KexP256 -> Crypto.p256_shared_call sk pk shared ok

let lemma_kex_shared_call_success g sk pk shared ok =
  match g with
  | C.KexX25519 -> Crypto.lemma_x25519_shared_call_success sk pk shared ok
  | C.KexP256 -> Crypto.lemma_p256_shared_call_success sk pk shared ok

(** At the full buffer width the padding is empty, so a P-256 share is stored
    verbatim and can be handed to the binding as-is. *)
let lemma_unpad_share_p256 (pk:B.bytes)
  : Lemma (requires B.length pk == 65)
          (ensures C.unpad_share_65 pk (C.kex_public_len C.KexP256) == pk)
  = ()

let lemma_unpad_share_x25519 (pk:B.bytes)
  : Lemma (requires B.length pk == 65)
          (ensures Seq.equal (C.unpad_share_65 pk (C.kex_public_len C.KexX25519))
                             (Seq.slice pk 0 32))
  = ()

(** A 32-byte share copied into the front of a zeroed 65-byte buffer leaves that
    buffer holding exactly [C.pad_share_65] of the share: the tail the copy did
    not touch is the zero padding. *)
let lemma_pad_share_65_zeroed_tail
  (old out:B.bytes)
  (pub:B.bytes{B.length pub == 32})
  : Lemma (requires B.length old == 65 /\
                    Seq.equal old (Seq.create 65 0uy) /\
                    Seq.equal out (Seq.append (Seq.slice pub 0 32)
                                              (Seq.slice old 32 65)))
          (ensures Seq.equal out (C.pad_share_65 pub))
  = Seq.lemma_eq_elim (Seq.slice old 32 65) (Seq.create 33 0uy);
    Seq.lemma_eq_elim (Seq.slice pub 0 32) pub

let lemma_pad_share_65_from_zeroed_prefix_copy
  (old out:B.bytes)
  (pub:B.bytes{B.length pub == 32})
  : Lemma (requires B.length old == 65 /\
                    Seq.equal out (Seq.append (Seq.slice pub 0 32)
                                              (Seq.slice old 32 65)))
          (ensures Seq.equal old (Seq.create 65 0uy) ==>
                   Seq.equal out (C.pad_share_65 pub))
  = FStar.Classical.arrow_to_impl
      #(Seq.equal old (Seq.create 65 0uy))
      #(Seq.equal out (C.pad_share_65 pub))
      (fun _ -> lemma_pad_share_65_zeroed_tail old out pub)

fn kex_shared_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (pk65: array U8.t)
  (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk65 'pk_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\
                 B.length 'pk_bytes == 65 /\
                 B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk65 'pk_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                kex_shared_call g 'sk_bytes
                  (C.unpad_share_65 'pk_bytes (C.kex_public_len g))
                  out_bytes ok)
{
  pts_to_len out;
  pts_to_len pk65;
  match g {
    C.KexX25519 -> {
      let mut pk32 = [| 0uy; 32sz |];
      AC.copy_prefix 32sz pk65 65sz pk32 32sz;
      with pk32_bytes. assert (pts_to pk32 pk32_bytes);
      lemma_unpad_share_x25519 'pk_bytes;
      Seq.lemma_eq_elim pk32_bytes
        (C.unpad_share_65 'pk_bytes (C.kex_public_len C.KexX25519));
      let ok = Crypto.x25519_shared_runtime sk pk32 out;
      with out_bytes. assert (pts_to out out_bytes);
      pts_to_len out;
      assert (pure (B.length out_bytes == 32));
      assert (pure (Crypto.x25519_shared_call 'sk_bytes pk32_bytes out_bytes ok));
      ok
    }
    C.KexP256 -> {
      lemma_unpad_share_p256 'pk_bytes;
      let ok = Crypto.p256_shared_runtime sk pk65 out;
      with out_bytes. assert (pts_to out out_bytes);
      pts_to_len out;
      ok
    }
  }
}

fn kex_shared_split_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (pk32: array U8.t)
  (pk65: array U8.t)
  (out: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to pk32 'x25519_bytes **
           pts_to pk65 'p256_bytes **
           pts_to out 'old **
           pure (B.length 'sk_bytes == 32 /\
                 B.length 'x25519_bytes == 32 /\
                 B.length 'p256_bytes == 65 /\
                 B.length 'old == 32)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to pk32 'x25519_bytes **
          pts_to pk65 'p256_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                kex_shared_call g 'sk_bytes
                  (kex_split_share g 'x25519_bytes 'p256_bytes)
                  out_bytes ok)
{
  pts_to_len out;
  pts_to_len pk32;
  pts_to_len pk65;
  match g {
    C.KexX25519 -> {
      let ok = Crypto.x25519_shared_runtime sk pk32 out;
      with out_bytes. assert (pts_to out out_bytes);
      pts_to_len out;
      ok
    }
    C.KexP256 -> {
      let ok = Crypto.p256_shared_runtime sk pk65 out;
      with out_bytes. assert (pts_to out out_bytes);
      pts_to_len out;
      ok
    }
  }
}

fn kex_public_from_private_runtime
  (g: C.kex_group)
  (sk: array U8.t)
  (out65: array U8.t)
  requires pts_to sk 'sk_bytes **
           pts_to out65 'old **
           pure (B.length 'sk_bytes == 32 /\ B.length 'old == 65)
  returns n: SZ.t
  ensures exists* out_bytes.
          pts_to sk 'sk_bytes **
          pts_to out65 out_bytes **
          pure (B.length out_bytes == 65 /\
                SZ.v n == C.kex_public_len g /\
                Seq.equal
                  (C.unpad_share_65 out_bytes (C.kex_public_len g))
                  (C.kex_public_from_private g 'sk_bytes) /\
                (Seq.equal (Ghost.reveal 'old) (Seq.create 65 0uy) ==>
                 Seq.equal
                   out_bytes
                   (C.pad_share_65 (C.kex_public_from_private g 'sk_bytes))))
{
  pts_to_len sk;
  pts_to_len out65;
  match g {
    C.KexX25519 -> {
      let mut pub32 = [| 0uy; 32sz |];
      Crypto.x25519_public_from_private sk pub32;
      with pub32_bytes. assert (pts_to pub32 pub32_bytes);
      pts_to_len pub32;
      AC.copy_prefix 32sz pub32 32sz out65 65sz;
      with out_bytes. assert (pts_to out65 out_bytes);
      pts_to_len out65;
      Seq.lemma_eq_elim
        (C.unpad_share_65 out_bytes (C.kex_public_len C.KexX25519))
        (C.x25519_public_from_private 'sk_bytes);
      lemma_pad_share_65_from_zeroed_prefix_copy
        (Ghost.reveal 'old) out_bytes pub32_bytes;
      32sz
    }
    C.KexP256 -> {
      Crypto.p256_public_from_private sk out65;
      with out_bytes. assert (pts_to out65 out_bytes);
      pts_to_len out65;
      lemma_unpad_share_p256 out_bytes;
      Seq.lemma_eq_elim out_bytes (C.pad_share_65 out_bytes);
      65sz
    }
  }
}
