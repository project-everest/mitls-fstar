module TLS13.KeySchedule

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module K = TLS13.Keys
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn early_secret_empty
  (out: array U8.t)
  requires pts_to out 'old **
           pure (B.length 'old == 32)
  ensures pts_to out (K.early_secret B.empty)

fn handshake_secret
  (early: array U8.t)
  (shared: array U8.t)
  (shared_len: SZ.t)
  (out: array U8.t)
  requires pts_to early 'early_bytes **
           pts_to shared 'shared_bytes **
           pts_to out 'old **
           pure (B.length 'early_bytes == 32 /\
                 B.length 'shared_bytes == SZ.v shared_len /\
                 B.length 'old == 32)
  ensures pts_to early 'early_bytes **
          pts_to shared 'shared_bytes **
          pts_to out (K.handshake_secret (Ghost.reveal 'early_bytes) (Ghost.reveal 'shared_bytes))

fn master_secret
  (handshake: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to out (K.master_secret (Ghost.reveal 'handshake_bytes))

fn client_handshake_traffic_secret
  (handshake: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.client_handshake_traffic_secret
                        (Ghost.reveal 'handshake_bytes)
                        (Ghost.reveal 'hash_bytes))

fn server_handshake_traffic_secret
  (handshake: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to handshake 'handshake_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'handshake_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to handshake 'handshake_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.server_handshake_traffic_secret
                        (Ghost.reveal 'handshake_bytes)
                        (Ghost.reveal 'hash_bytes))

fn client_application_traffic_secret
  (master: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to master 'master_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'master_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to master 'master_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.client_application_traffic_secret
                        (Ghost.reveal 'master_bytes)
                        (Ghost.reveal 'hash_bytes))

fn server_application_traffic_secret
  (master: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to master 'master_bytes **
           pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'master_bytes == 32 /\
                 B.length 'hash_bytes == 32 /\
                 B.length 'old == 32)
  ensures pts_to master 'master_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.server_application_traffic_secret
                        (Ghost.reveal 'master_bytes)
                        (Ghost.reveal 'hash_bytes))

fn application_traffic_secret_update
  (old_secret: array U8.t)
  (out: array U8.t)
  requires pts_to old_secret 'old_secret_bytes **
          pts_to out 'old **
          pure (B.length 'old_secret_bytes == 32 /\
                B.length 'old == 32)
  ensures pts_to old_secret 'old_secret_bytes **
          pts_to out (K.application_traffic_secret_update
                       (Ghost.reveal 'old_secret_bytes))

fn finished_verify_data
  (base_key: array U8.t)
  (transcript_hash: array U8.t)
  (out: array U8.t)
  requires pts_to base_key 'base_key_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out 'old **
          pure (B.length 'base_key_bytes == 32 /\
                B.length 'hash_bytes == 32 /\
                B.length 'old == 32)
  ensures pts_to base_key 'base_key_bytes **
          pts_to transcript_hash 'hash_bytes **
          pts_to out (K.finished_verify_data
                       (Ghost.reveal 'base_key_bytes)
                       (Ghost.reveal 'hash_bytes))

(**
  Derives the record-protection key for the negotiated suite, branching on the
  negotiated algorithm.  The output buffer is always 32 bytes: a shorter key is
  zero-padded, so the buffer layout is independent of the suite and the logical
  key is the `C.aead_key_len alg`-byte prefix (see
  `TLS13.Crypto.Spec.pad_key_32`).
**)
fn derive_traffic_key
  (traffic_secret: array U8.t)
  (alg: C.aead_alg)
  (out: array U8.t)
  requires pts_to traffic_secret 'secret_bytes **
          pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 32)
  ensures pts_to traffic_secret 'secret_bytes **
          pts_to out (C.pad_key_32
                       (K.derive_aead_key alg (Ghost.reveal 'secret_bytes)))

fn derive_traffic_iv
  (traffic_secret: array U8.t)
  (out: array U8.t)
  requires pts_to traffic_secret 'secret_bytes **
           pts_to out 'old **
           pure (B.length 'secret_bytes == 32 /\ B.length 'old == 12)
  ensures pts_to traffic_secret 'secret_bytes **
          pts_to out (K.derive_aead_iv (Ghost.reveal 'secret_bytes))
