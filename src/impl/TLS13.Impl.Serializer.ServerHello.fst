module TLS13.Impl.Serializer.ServerHello

friend TLS13.Wire.Spec

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal
module WSRD = TLS13.Wire.Spec.RevealDecode

let byte_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures C.byte n == b /\ WS.byte n == b)
=
  C.lemma_byte_reveal n;
  assert_norm (WS.byte n == U8.uint_to_t (n % 256));
  assert (U8.v (C.byte n) == U8.v b);
  assert (U8.v (WS.byte n) == U8.v b);
  U8.v_inj (C.byte n) b;
  U8.v_inj (WS.byte n) b

let u8_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures Seq.equal (WS.u8 n) (B.of_list [b]))
=
  byte_literal n b;
  assert (WS.u8 n == B.singleton (WS.byte n));
  TLS13.Wire.Spec.Reveal.Util.lemma_singleton_of_list b

let u16_literal (n:nat) (hi lo:U8.t)
  : Lemma
      (requires U8.v hi == (n / 256) % 256 /\
                U8.v lo == n % 256)
      (ensures Seq.equal (WS.u16 n) (B.of_list [hi; lo]))
=
  byte_literal (n / 256) hi;
  byte_literal n lo;
  assert (WS.u16 n == B.of_list [WS.byte (n / 256); WS.byte n])

let u24_literal (n:nat) (b0 b1 b2:U8.t)
  : Lemma
      (requires U8.v b0 == (n / 65536) % 256 /\
                U8.v b1 == (n / 256) % 256 /\
                U8.v b2 == n % 256)
      (ensures Seq.equal (WS.u24 n) (B.of_list [b0; b1; b2]))
=
  byte_literal (n / 65536) b0;
  byte_literal (n / 256) b1;
  byte_literal n b2;
  assert (WS.u24 n == B.of_list [WS.byte (n / 65536); WS.byte (n / 256); WS.byte n])

let wsr_byte_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures WSR.byte n == b)
=
  WSR.lemma_byte_value n;
  assert (U8.v (WSR.byte n) == U8.v b);
  U8.v_inj (WSR.byte n) b

let handshake_record_header_literal (n:nat) (hi lo:U8.t)
  : Lemma
      (requires U8.v hi == (n / 256) % 256 /\
                U8.v lo == n % 256)
      (ensures Seq.equal
        (WSR.serialize_record_header T.Handshake n)
        (B.of_list [22uy; 0x03uy; 0x03uy; hi; lo]))
=
  WSR.lemma_serialize_handshake_record_header_reveal n;
  wsr_byte_literal (n / 256) hi;
  wsr_byte_literal n lo;
  assert (WSR.serialize_record_header T.Handshake n ==
    B.of_list [0x16uy; 0x03uy; 0x03uy; WSR.byte (n / 256); WSR.byte n])

let rec lemma_of_list_append (l1 l2:list U8.t)
  : Lemma (ensures Seq.equal (B.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))
          (decreases l1)
=
  match l1 with
  | [] ->
    Seq.lemma_seq_of_list_induction ([] <: list U8.t);
    Seq.append_empty_l (B.of_list l2)
  | hd :: tl ->
    lemma_of_list_append tl l2;
    Seq.lemma_seq_of_list_induction (hd :: (tl `FStar.List.Tot.append` l2));
    Seq.lemma_seq_of_list_induction (hd :: tl);
    Seq.append_assoc (Seq.create 1 hd) (B.of_list tl) (B.of_list l2)

let server_key_share_extension_prefix_bytes : B.bytes =
  B.append
    (B.of_list [0uy; 0x33uy])
    (B.append
      (B.of_list [0uy; 36uy])
      (B.append
        (B.of_list [0uy; 0x1duy])
        (B.of_list [0uy; 32uy])))

let server_key_share_extension_bytes (key_share:B.bytes) : B.bytes =
  B.append server_key_share_extension_prefix_bytes key_share

let server_supported_versions_extension_bytes : B.bytes =
  B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]

let server_hello_extensions_bytes (key_share:B.bytes) : B.bytes =
  B.append (server_key_share_extension_bytes key_share) server_supported_versions_extension_bytes

let server_hello_body_bytes (random key_share:B.bytes) : B.bytes =
  B.append
    (B.of_list [0x03uy; 0x03uy])
    (B.append
      random
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0x13uy; 0x03uy])
          (B.append
            (B.of_list [0uy])
            (B.append
              (B.of_list [0uy; 46uy])
              (server_hello_extensions_bytes key_share))))))

let server_hello_prefix_bytes : B.bytes =
  B.append
    (B.of_list [2uy])
    (B.append
      (B.of_list [0uy; 0uy; 86uy])
      (B.of_list [0x03uy; 0x03uy]))

let server_hello_middle_bytes : B.bytes =
  B.append
    (B.of_list [0uy])
    (B.append
      (B.of_list [0x13uy; 0x03uy])
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0uy; 46uy])
          server_key_share_extension_prefix_bytes)))

let server_hello_tail_bytes : B.bytes =
  B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]

let server_hello_bytes (random key_share:B.bytes) : B.bytes =
  B.append
    server_hello_prefix_bytes
    (B.append
      random
      (B.append
        server_hello_middle_bytes
        (B.append key_share server_hello_tail_bytes)))

let server_hello_bytes_old_grouping (random key_share:B.bytes) : B.bytes =
  B.append
    (B.of_list [2uy])
    (B.append
      (B.of_list [0uy; 0uy; 86uy])
      (server_hello_body_bytes random key_share))

let lemma_server_hello_prefix_bytes_literal ()
  : Lemma (Seq.equal
      server_hello_prefix_bytes
      (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy]))
=
  lemma_of_list_append [0uy; 0uy; 86uy] [0x03uy; 0x03uy];
  Seq.lemma_eq_elim
    (B.append (B.of_list [0uy; 0uy; 86uy]) (B.of_list [0x03uy; 0x03uy]))
    (B.of_list [0uy; 0uy; 86uy; 0x03uy; 0x03uy]);
  lemma_of_list_append [2uy] [0uy; 0uy; 86uy; 0x03uy; 0x03uy];
  Seq.lemma_eq_elim
    server_hello_prefix_bytes
    (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy])

let lemma_server_key_share_extension_prefix_bytes_literal ()
  : Lemma (Seq.equal
      server_key_share_extension_prefix_bytes
      (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]))
=
  lemma_of_list_append [0uy; 0x1duy] [0uy; 32uy];
  Seq.lemma_eq_elim
    (B.append (B.of_list [0uy; 0x1duy]) (B.of_list [0uy; 32uy]))
    (B.of_list [0uy; 0x1duy; 0uy; 32uy]);
  lemma_of_list_append [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy];
  Seq.lemma_eq_elim
    (B.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy]))
    (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_of_list_append [0uy; 0x33uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  Seq.lemma_eq_elim
    server_key_share_extension_prefix_bytes
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])

let lemma_server_hello_middle_bytes_literal ()
  : Lemma (Seq.equal
      server_hello_middle_bytes
      (B.of_list [
        0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy;
        0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy
      ]))
=
  lemma_server_key_share_extension_prefix_bytes_literal ();
  Seq.lemma_eq_elim
    server_key_share_extension_prefix_bytes
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_of_list_append
    [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  Seq.lemma_eq_elim
    server_hello_middle_bytes
    (B.of_list [
      0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy;
      0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy
    ])

let lemma_server_key_share_extension_bytes (key_share:B.bytes)
  : Lemma (Seq.equal
      (WS.server_key_share_extension key_share)
      (server_key_share_extension_bytes key_share))
=
  u16_literal 0x0033 0uy 0x33uy;
  u16_literal 36 0uy 36uy;
  u16_literal 0x001d 0uy 0x1duy;
  u16_literal 32 0uy 32uy;
  assert (WS.server_key_share_extension key_share ==
    WS.append5 (WS.u16 0x0033) (WS.u16 36) (WS.u16 0x001d) (WS.u16 32) key_share);
  Seq.lemma_eq_elim (WS.u16 0x0033) (B.of_list [0uy; 0x33uy]);
  Seq.lemma_eq_elim (WS.u16 36) (B.of_list [0uy; 36uy]);
  Seq.lemma_eq_elim (WS.u16 0x001d) (B.of_list [0uy; 0x1duy]);
  Seq.lemma_eq_elim (WS.u16 32) (B.of_list [0uy; 32uy])

let lemma_server_supported_versions_extension_bytes ()
  : Lemma (Seq.equal
      (WS.server_supported_versions_extension ())
      server_supported_versions_extension_bytes)
=
  u16_literal 0x002b 0uy 0x2buy;
  u16_literal 2 0uy 2uy;
  u16_literal 0x0304 0x03uy 0x04uy;
  assert (WS.server_supported_versions_extension () ==
    WS.append3 (WS.u16 0x002b) (WS.u16 2) (WS.u16 0x0304));
  Seq.lemma_eq_elim (WS.u16 0x002b) (B.of_list [0uy; 0x2buy]);
  Seq.lemma_eq_elim (WS.u16 2) (B.of_list [0uy; 2uy]);
  Seq.lemma_eq_elim (WS.u16 0x0304) (B.of_list [0x03uy; 0x04uy])

let lemma_server_hello_bytes_len (random key_share:B.bytes)
  : Lemma
      (requires B.length random == 32 /\ B.length key_share == 32)
      (ensures B.length (server_hello_bytes random key_share) == 90 /\
               B.length (server_hello_body_bytes random key_share) == 86)
=
  ()

let lemma_server_hello_bytes_spec (sh:M.server_hello)
  : Lemma
      (requires B.length sh.M.random == 32 /\
                B.length sh.M.key_share == 32)
      (ensures Seq.equal
        (server_hello_bytes sh.M.random sh.M.key_share)
        (WS.serialize_server_hello_from_selection sh))
=
  u8_literal 2 2uy;
  u24_literal 86 0uy 0uy 86uy;
  u16_literal 0x0303 0x03uy 0x03uy;
  u8_literal 0 0uy;
  u16_literal 0x1303 0x13uy 0x03uy;
  u16_literal 46 0uy 46uy;
  lemma_server_key_share_extension_bytes sh.M.key_share;
  lemma_server_supported_versions_extension_bytes ();
  assert (WS.serialize_server_hello sh ==
    WS.append6
      (WS.u16 0x0303)
      sh.M.random
      (WS.u8 0)
      (WS.u16 (WS.cipher_suite_to_u16 sh.M.cipher_suite))
      (WS.u8 0)
      (B.append
        (WS.u16 (B.length (B.append
          (WS.server_key_share_extension sh.M.key_share)
          (WS.server_supported_versions_extension ()))))
        (B.append
          (WS.server_key_share_extension sh.M.key_share)
          (WS.server_supported_versions_extension ()))));
  assert_norm (WS.cipher_suite_to_u16 sh.M.cipher_suite == 0x1303);
  assert (B.length (server_key_share_extension_bytes sh.M.key_share) == 40);
  assert (B.length server_supported_versions_extension_bytes == 6);
  assert (B.length (server_hello_extensions_bytes sh.M.key_share) == 46);
  assert (B.length (WS.serialize_server_hello sh) == 86);
  assert (WS.serialize_server_hello_from_selection sh ==
    WS.append3 (WS.u8 2) (WS.u24 86) (WS.serialize_server_hello sh));
  Seq.lemma_eq_elim (WS.u8 2) (B.of_list [2uy]);
  Seq.lemma_eq_elim (WS.u24 86) (B.of_list [0uy; 0uy; 86uy]);
  Seq.lemma_eq_elim (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]);
  Seq.lemma_eq_elim (WS.u8 0) (B.of_list [0uy]);
  Seq.lemma_eq_elim (WS.u16 0x1303) (B.of_list [0x13uy; 0x03uy]);
  Seq.lemma_eq_elim (WS.u16 46) (B.of_list [0uy; 46uy]);
  Seq.lemma_eq_elim
    (WS.server_key_share_extension sh.M.key_share)
    (server_key_share_extension_bytes sh.M.key_share);
  Seq.lemma_eq_elim
    (WS.server_supported_versions_extension ())
    server_supported_versions_extension_bytes;
  Seq.append_assoc
    server_key_share_extension_prefix_bytes
    sh.M.key_share
    server_supported_versions_extension_bytes;
  assert (Seq.equal
    (WS.serialize_server_hello_from_selection sh)
    (server_hello_bytes sh.M.random sh.M.key_share));
  Seq.lemma_eq_intro
    (server_hello_bytes sh.M.random sh.M.key_share)
    (WS.serialize_server_hello_from_selection sh)

let server_hello_bytes_shape
  (out_bytes:B.bytes)
  (random key_share:B.bytes)
  : Lemma
      (requires B.length out_bytes == 90 /\
                B.length random == 32 /\
                B.length key_share == 32 /\
                Seq.equal (CL.raw_slice out_bytes 0 6) server_hello_prefix_bytes /\
                Seq.equal (CL.raw_slice out_bytes 6 38) random /\
                Seq.equal (CL.raw_slice out_bytes 38 52) server_hello_middle_bytes /\
                Seq.equal (CL.raw_slice out_bytes 52 84) key_share /\
                Seq.equal (CL.raw_slice out_bytes 84 90) server_hello_tail_bytes)
      (ensures Seq.equal out_bytes (server_hello_bytes random key_share))
=
  C.lemma_raw_slice_all out_bytes;
  CL.lemma_raw_slice_split out_bytes 0 6 38;
  CL.lemma_raw_slice_split out_bytes 0 38 52;
  CL.lemma_raw_slice_split out_bytes 0 52 84;
  CL.lemma_raw_slice_split out_bytes 0 84 90;
  C.lemma_raw_slice_empty out_bytes 90;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 0 6) server_hello_prefix_bytes;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 6 38) random;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 38 52) server_hello_middle_bytes;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 52 84) key_share;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 84 90) server_hello_tail_bytes;
  Seq.lemma_eq_elim (CL.raw_slice out_bytes 90 90) B.empty;
  assert (Seq.equal (CL.raw_slice out_bytes 0 90) out_bytes);
  assert (Seq.equal out_bytes (server_hello_bytes random key_share))

let server_hello_tail_slice (bytes:B.bytes)
  : Lemma
      (requires B.length bytes == 90 /\
                Seq.index bytes 84 == 0uy /\
                Seq.index bytes 85 == 0x2buy /\
                Seq.index bytes 86 == 0uy /\
                Seq.index bytes 87 == 2uy /\
                Seq.index bytes 88 == 0x03uy /\
                Seq.index bytes 89 == 0x04uy)
      (ensures Seq.equal
        (CL.raw_slice bytes 84 90)
        (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))
=
  Seq.lemma_len_slice bytes 84 90;
  assert (B.length (CL.raw_slice bytes 84 90) == 6);
  C.lemma_raw_slice_index bytes 84 90 0;
  C.lemma_raw_slice_index bytes 84 90 1;
  C.lemma_raw_slice_index bytes 84 90 2;
  C.lemma_raw_slice_index bytes 84 90 3;
  C.lemma_raw_slice_index bytes 84 90 4;
  C.lemma_raw_slice_index bytes 84 90 5;
  assert (Seq.index (CL.raw_slice bytes 84 90) 0 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 84 90) 1 == 0x2buy);
  assert (Seq.index (CL.raw_slice bytes 84 90) 2 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 84 90) 3 == 2uy);
  assert (Seq.index (CL.raw_slice bytes 84 90) 4 == 0x03uy);
  assert (Seq.index (CL.raw_slice bytes 84 90) 5 == 0x04uy);
  Seq.lemma_eq_intro
    (CL.raw_slice bytes 84 90)
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])

let server_hello_prefix_slice (bytes:B.bytes)
  : Lemma
      (requires B.length bytes == 90 /\
                Seq.index bytes 0 == 2uy /\
                Seq.index bytes 1 == 0uy /\
                Seq.index bytes 2 == 0uy /\
                Seq.index bytes 3 == 86uy /\
                Seq.index bytes 4 == 0x03uy /\
                Seq.index bytes 5 == 0x03uy)
      (ensures Seq.equal
        (CL.raw_slice bytes 0 6)
        (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy]))
=
  Seq.lemma_len_slice bytes 0 6;
  assert (B.length (CL.raw_slice bytes 0 6) == 6);
  C.lemma_raw_slice_index bytes 0 6 0;
  C.lemma_raw_slice_index bytes 0 6 1;
  C.lemma_raw_slice_index bytes 0 6 2;
  C.lemma_raw_slice_index bytes 0 6 3;
  C.lemma_raw_slice_index bytes 0 6 4;
  C.lemma_raw_slice_index bytes 0 6 5;
  assert (Seq.index (CL.raw_slice bytes 0 6) 0 == 2uy);
  assert (Seq.index (CL.raw_slice bytes 0 6) 1 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 0 6) 2 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 0 6) 3 == 86uy);
  assert (Seq.index (CL.raw_slice bytes 0 6) 4 == 0x03uy);
  assert (Seq.index (CL.raw_slice bytes 0 6) 5 == 0x03uy);
  Seq.lemma_eq_intro
    (CL.raw_slice bytes 0 6)
    (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy])

let lemma_upd_preserves_slice_after
  (bytes:B.bytes)
  (idx:nat)
  (b:U8.t)
  (lo hi:nat)
  : Lemma
      (requires lo <= hi /\ hi <= idx /\ idx < B.length bytes)
      (ensures Seq.equal
        (CL.raw_slice (Seq.upd bytes idx b) lo hi)
        (CL.raw_slice bytes lo hi))
=
  Seq.lemma_len_upd idx b bytes;
  Seq.lemma_len_slice (Seq.upd bytes idx b) lo hi;
  Seq.lemma_len_slice bytes lo hi;
  introduce forall (i:nat).
    i < hi - lo ==>
    Seq.index (CL.raw_slice (Seq.upd bytes idx b) lo hi) i ==
    Seq.index (CL.raw_slice bytes lo hi) i
  with introduce _ ==> _
  with _. (
    C.lemma_raw_slice_index (Seq.upd bytes idx b) lo hi i;
    C.lemma_raw_slice_index bytes lo hi i;
    Seq.lemma_index_upd2 bytes idx b (lo + i)
  );
  Seq.lemma_eq_intro
    (CL.raw_slice (Seq.upd bytes idx b) lo hi)
    (CL.raw_slice bytes lo hi)

let server_hello_middle_tail_updates (bytes:B.bytes{B.length bytes == 90}) : B.bytes =
  let s38 = Seq.upd bytes 38 0uy in
  let s39 = Seq.upd s38 39 0x13uy in
  let s40 = Seq.upd s39 40 0x03uy in
  let s41 = Seq.upd s40 41 0uy in
  let s42 = Seq.upd s41 42 0uy in
  let s43 = Seq.upd s42 43 46uy in
  let s44 = Seq.upd s43 44 0uy in
  let s45 = Seq.upd s44 45 0x33uy in
  let s46 = Seq.upd s45 46 0uy in
  let s47 = Seq.upd s46 47 36uy in
  let s48 = Seq.upd s47 48 0uy in
  let s49 = Seq.upd s48 49 0x1duy in
  let s50 = Seq.upd s49 50 0uy in
  let s51 = Seq.upd s50 51 32uy in
  let s84 = Seq.upd s51 84 0uy in
  let s85 = Seq.upd s84 85 0x2buy in
  let s86 = Seq.upd s85 86 0uy in
  let s87 = Seq.upd s86 87 2uy in
  let s88 = Seq.upd s87 88 0x03uy in
  Seq.upd s88 89 0x04uy

let lemma_server_hello_middle_tail_preserves_prefix
  (bytes:B.bytes)
  : Lemma
      (requires B.length bytes == 90)
      (ensures Seq.equal
        (CL.raw_slice (server_hello_middle_tail_updates bytes) 0 6)
        (CL.raw_slice bytes 0 6))
=
  let s38 = Seq.upd bytes 38 0uy in
  let s39 = Seq.upd s38 39 0x13uy in
  let s40 = Seq.upd s39 40 0x03uy in
  let s41 = Seq.upd s40 41 0uy in
  let s42 = Seq.upd s41 42 0uy in
  let s43 = Seq.upd s42 43 46uy in
  let s44 = Seq.upd s43 44 0uy in
  let s45 = Seq.upd s44 45 0x33uy in
  let s46 = Seq.upd s45 46 0uy in
  let s47 = Seq.upd s46 47 36uy in
  let s48 = Seq.upd s47 48 0uy in
  let s49 = Seq.upd s48 49 0x1duy in
  let s50 = Seq.upd s49 50 0uy in
  let s51 = Seq.upd s50 51 32uy in
  let s84 = Seq.upd s51 84 0uy in
  let s85 = Seq.upd s84 85 0x2buy in
  let s86 = Seq.upd s85 86 0uy in
  let s87 = Seq.upd s86 87 2uy in
  let s88 = Seq.upd s87 88 0x03uy in
  lemma_upd_preserves_slice_after bytes 38 0uy 0 6;
  lemma_upd_preserves_slice_after s38 39 0x13uy 0 6;
  lemma_upd_preserves_slice_after s39 40 0x03uy 0 6;
  lemma_upd_preserves_slice_after s40 41 0uy 0 6;
  lemma_upd_preserves_slice_after s41 42 0uy 0 6;
  lemma_upd_preserves_slice_after s42 43 46uy 0 6;
  lemma_upd_preserves_slice_after s43 44 0uy 0 6;
  lemma_upd_preserves_slice_after s44 45 0x33uy 0 6;
  lemma_upd_preserves_slice_after s45 46 0uy 0 6;
  lemma_upd_preserves_slice_after s46 47 36uy 0 6;
  lemma_upd_preserves_slice_after s47 48 0uy 0 6;
  lemma_upd_preserves_slice_after s48 49 0x1duy 0 6;
  lemma_upd_preserves_slice_after s49 50 0uy 0 6;
  lemma_upd_preserves_slice_after s50 51 32uy 0 6;
  lemma_upd_preserves_slice_after s51 84 0uy 0 6;
  lemma_upd_preserves_slice_after s84 85 0x2buy 0 6;
  lemma_upd_preserves_slice_after s85 86 0uy 0 6;
  lemma_upd_preserves_slice_after s86 87 2uy 0 6;
  lemma_upd_preserves_slice_after s87 88 0x03uy 0 6;
  lemma_upd_preserves_slice_after s88 89 0x04uy 0 6

let server_hello_middle_slice (bytes:B.bytes)
  : Lemma
      (requires B.length bytes == 90 /\
                Seq.index bytes 38 == 0uy /\
                Seq.index bytes 39 == 0x13uy /\
                Seq.index bytes 40 == 0x03uy /\
                Seq.index bytes 41 == 0uy /\
                Seq.index bytes 42 == 0uy /\
                Seq.index bytes 43 == 46uy /\
                Seq.index bytes 44 == 0uy /\
                Seq.index bytes 45 == 0x33uy /\
                Seq.index bytes 46 == 0uy /\
                Seq.index bytes 47 == 36uy /\
                Seq.index bytes 48 == 0uy /\
                Seq.index bytes 49 == 0x1duy /\
                Seq.index bytes 50 == 0uy /\
                Seq.index bytes 51 == 32uy)
      (ensures Seq.equal
        (CL.raw_slice bytes 38 52)
        server_hello_middle_bytes)
=
  Seq.lemma_len_slice bytes 38 44;
  Seq.lemma_len_slice bytes 44 52;
  assert (B.length (CL.raw_slice bytes 38 44) == 6);
  assert (B.length (CL.raw_slice bytes 44 52) == 8);
  C.lemma_raw_slice_index bytes 38 52 0;
  C.lemma_raw_slice_index bytes 38 52 1;
  C.lemma_raw_slice_index bytes 38 52 2;
  C.lemma_raw_slice_index bytes 38 52 3;
  C.lemma_raw_slice_index bytes 38 52 4;
  C.lemma_raw_slice_index bytes 38 52 5;
  C.lemma_raw_slice_index bytes 38 52 6;
  C.lemma_raw_slice_index bytes 38 52 7;
  C.lemma_raw_slice_index bytes 38 52 8;
  C.lemma_raw_slice_index bytes 38 52 9;
  C.lemma_raw_slice_index bytes 38 52 10;
  C.lemma_raw_slice_index bytes 38 52 11;
  C.lemma_raw_slice_index bytes 38 52 12;
  C.lemma_raw_slice_index bytes 38 52 13;
  assert (Seq.index (CL.raw_slice bytes 38 52) 0 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 1 == 0x13uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 2 == 0x03uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 3 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 4 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 5 == 46uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 6 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 7 == 0x33uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 8 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 9 == 36uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 10 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 11 == 0x1duy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 12 == 0uy);
  assert (Seq.index (CL.raw_slice bytes 38 52) 13 == 32uy);
  Seq.lemma_eq_intro (CL.raw_slice bytes 38 44)
    (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]);
  lemma_server_key_share_extension_prefix_bytes_literal ();
  Seq.lemma_eq_elim
    server_key_share_extension_prefix_bytes
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  Seq.lemma_eq_intro (CL.raw_slice bytes 44 52)
    server_key_share_extension_prefix_bytes;
  CL.lemma_raw_slice_split bytes 38 44 52;
  Seq.lemma_eq_elim
    (CL.raw_slice bytes 38 44)
    (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]);
  Seq.lemma_eq_elim
    (CL.raw_slice bytes 44 52)
    server_key_share_extension_prefix_bytes

fn serialize_server_hello_from_selection
  (#sh: erased M.server_hello)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 90)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 90 /\
                SZ.v written == 90 /\
                Seq.equal out_bytes
                  (WS.serialize_server_hello_from_selection (Ghost.reveal sh)))
{
  unfold (L.is_valid_server_hello lsh (Ghost.reveal sh));
  with random key_share. assert (
    V.pts_to lsh.L.server_hello_random random **
    V.pts_to lsh.L.server_hello_key_share key_share);
  V.pts_to_len lsh.L.server_hello_random;
  V.pts_to_len lsh.L.server_hello_key_share;
  assert (pure (B.length random == 32));
  assert (pure (B.length key_share == 32));

  pts_to_len out;
  out.(0sz) <- 2uy;
  out.(1sz) <- 0uy;
  out.(2sz) <- 0uy;
  out.(3sz) <- 86uy;
  out.(4sz) <- 0x03uy;
  out.(5sz) <- 0x03uy;
  with after_prefix. assert (pts_to out after_prefix);
  out.(38sz) <- 0uy;
  out.(39sz) <- 0x13uy;
  out.(40sz) <- 0x03uy;
  out.(41sz) <- 0uy;
  out.(42sz) <- 0uy;
  out.(43sz) <- 46uy;
  out.(44sz) <- 0uy;
  out.(45sz) <- 0x33uy;
  out.(46sz) <- 0uy;
  out.(47sz) <- 36uy;
  out.(48sz) <- 0uy;
  out.(49sz) <- 0x1duy;
  with before_middle_50. assert (pts_to out before_middle_50);
  pts_to_len out;
  out.(50sz) <- 0uy;
  pts_to_len out;
  with before_middle_last. assert (pts_to out before_middle_last);
  Seq.lemma_index_upd1 before_middle_50 50 0uy;
  assert (pure (Seq.index before_middle_last 38 == 0uy));
  assert (pure (Seq.index before_middle_last 39 == 0x13uy));
  assert (pure (Seq.index before_middle_last 40 == 0x03uy));
  assert (pure (Seq.index before_middle_last 41 == 0uy));
  assert (pure (Seq.index before_middle_last 42 == 0uy));
  assert (pure (Seq.index before_middle_last 43 == 46uy));
  assert (pure (Seq.index before_middle_last 44 == 0uy));
  assert (pure (Seq.index before_middle_last 45 == 0x33uy));
  assert (pure (Seq.index before_middle_last 46 == 0uy));
  assert (pure (Seq.index before_middle_last 47 == 36uy));
  assert (pure (Seq.index before_middle_last 48 == 0uy));
  assert (pure (Seq.index before_middle_last 49 == 0x1duy));
  assert (pure (Seq.index before_middle_last 50 == 0uy));
  pts_to_len out;
  out.(51sz) <- 32uy;
  with after_middle. assert (pts_to out after_middle);
  Seq.lemma_index_upd2 before_middle_last 51 32uy 38;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 39;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 40;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 41;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 42;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 43;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 44;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 45;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 46;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 47;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 48;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 49;
  Seq.lemma_index_upd2 before_middle_last 51 32uy 50;
  assert (pure (Seq.index after_middle 38 == 0uy));
  assert (pure (Seq.index after_middle 39 == 0x13uy));
  assert (pure (Seq.index after_middle 40 == 0x03uy));
  assert (pure (Seq.index after_middle 41 == 0uy));
  assert (pure (Seq.index after_middle 42 == 0uy));
  assert (pure (Seq.index after_middle 43 == 46uy));
  assert (pure (Seq.index after_middle 44 == 0uy));
  assert (pure (Seq.index after_middle 45 == 0x33uy));
  assert (pure (Seq.index after_middle 46 == 0uy));
  assert (pure (Seq.index after_middle 47 == 36uy));
  assert (pure (Seq.index after_middle 48 == 0uy));
  assert (pure (Seq.index after_middle 49 == 0x1duy));
  assert (pure (Seq.index after_middle 50 == 0uy));
  assert (pure (Seq.index after_middle 51 == 32uy));
  pts_to_len out;
  out.(84sz) <- 0uy;
  with after_tail84. assert (pts_to out after_tail84);
  Seq.lemma_index_upd2 after_middle 84 0uy 51;
  assert (pure (Seq.index after_tail84 51 == 32uy));
  pts_to_len out;
  out.(85sz) <- 0x2buy;
  with after_tail85. assert (pts_to out after_tail85);
  Seq.lemma_index_upd2 after_tail84 85 0x2buy 51;
  assert (pure (Seq.index after_tail85 51 == 32uy));
  pts_to_len out;
  out.(86sz) <- 0uy;
  with after_tail86. assert (pts_to out after_tail86);
  Seq.lemma_index_upd2 after_tail85 86 0uy 51;
  assert (pure (Seq.index after_tail86 51 == 32uy));
  pts_to_len out;
  out.(87sz) <- 2uy;
  with after_tail87. assert (pts_to out after_tail87);
  Seq.lemma_index_upd2 after_tail86 87 2uy 51;
  assert (pure (Seq.index after_tail87 51 == 32uy));
  pts_to_len out;
  out.(88sz) <- 0x03uy;
  with after_tail88. assert (pts_to out after_tail88);
  Seq.lemma_index_upd2 after_tail87 88 0x03uy 51;
  assert (pure (Seq.index after_tail88 51 == 32uy));
  pts_to_len out;
  out.(89sz) <- 0x04uy;
  with before_random_copy. assert (pts_to out before_random_copy);
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 51;
  assert (pure (Seq.index before_random_copy 51 == 32uy));
  Seq.lemma_index_upd1 after_middle 84 0uy;
  Seq.lemma_index_upd2 after_tail84 85 0x2buy 84;
  Seq.lemma_index_upd1 after_tail84 85 0x2buy;
  Seq.lemma_index_upd2 after_tail85 86 0uy 84;
  Seq.lemma_index_upd2 after_tail85 86 0uy 85;
  Seq.lemma_index_upd1 after_tail85 86 0uy;
  Seq.lemma_index_upd2 after_tail86 87 2uy 84;
  Seq.lemma_index_upd2 after_tail86 87 2uy 85;
  Seq.lemma_index_upd2 after_tail86 87 2uy 86;
  Seq.lemma_index_upd1 after_tail86 87 2uy;
  Seq.lemma_index_upd2 after_tail87 88 0x03uy 84;
  Seq.lemma_index_upd2 after_tail87 88 0x03uy 85;
  Seq.lemma_index_upd2 after_tail87 88 0x03uy 86;
  Seq.lemma_index_upd2 after_tail87 88 0x03uy 87;
  Seq.lemma_index_upd1 after_tail87 88 0x03uy;
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 84;
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 85;
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 86;
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 87;
  Seq.lemma_index_upd2 after_tail88 89 0x04uy 88;
  Seq.lemma_index_upd1 after_tail88 89 0x04uy;
  assert (pure (Seq.index before_random_copy 84 == 0uy));
  assert (pure (Seq.index before_random_copy 85 == 0x2buy));
  assert (pure (Seq.index before_random_copy 86 == 0uy));
  assert (pure (Seq.index before_random_copy 87 == 2uy));
  assert (pure (Seq.index before_random_copy 88 == 0x03uy));
  assert (pure (Seq.index before_random_copy 89 == 0x04uy));
  lemma_upd_preserves_slice_after after_middle 84 0uy 38 52;
  lemma_upd_preserves_slice_after after_tail84 85 0x2buy 38 52;
  lemma_upd_preserves_slice_after after_tail85 86 0uy 38 52;
  lemma_upd_preserves_slice_after after_tail86 87 2uy 38 52;
  lemma_upd_preserves_slice_after after_tail87 88 0x03uy 38 52;
  lemma_upd_preserves_slice_after after_tail88 89 0x04uy 38 52;
  assert (pure (B.length before_random_copy == 90));
  V.to_array_pts_to lsh.L.server_hello_random;
  C.copy_array_slice_to_array
    (V.vec_to_array lsh.L.server_hello_random)
    32sz
    0sz
    32sz
    out
    out_len
    6sz;
  V.to_vec_pts_to lsh.L.server_hello_random;
  with before_key_copy. assert (pts_to out before_key_copy);
  assert (pure (B.length before_key_copy == 90));
  V.to_array_pts_to lsh.L.server_hello_key_share;
  C.copy_array_slice_to_array
    (V.vec_to_array lsh.L.server_hello_key_share)
    32sz
    0sz
    32sz
    out
    out_len
    52sz;
  V.to_vec_pts_to lsh.L.server_hello_key_share;

  with out_bytes. assert (pts_to out out_bytes);
  pts_to_len out;
  assert (pure (B.length out_bytes == 90));
  assert (pure (Seq.equal random (Ghost.reveal sh).M.random));
  assert (pure (Seq.equal key_share (Ghost.reveal sh).M.key_share));
  lemma_server_hello_bytes_len random key_share;
  lemma_server_hello_bytes_spec (Ghost.reveal sh);
  C.lemma_raw_slice_all random;
  Seq.lemma_eq_elim (CL.raw_slice random 0 32) random;
  C.lemma_copy_expr_preserves_prefix_slice before_random_copy random 6 32 90 0 6;
  C.lemma_copy_expr_copied_slice before_random_copy random 6 32 90;
  C.lemma_copy_expr_preserves_suffix_slice before_random_copy random 6 32 90 38 52;
  C.lemma_copy_expr_preserves_suffix_slice before_random_copy random 6 32 90 84 90;
  C.lemma_raw_slice_all key_share;
  Seq.lemma_eq_elim (CL.raw_slice key_share 0 32) key_share;
  C.lemma_copy_expr_preserves_prefix_slice before_key_copy key_share 52 32 90 0 6;
  C.lemma_copy_expr_preserves_prefix_slice before_key_copy key_share 52 32 90 6 38;
  C.lemma_copy_expr_preserves_prefix_slice before_key_copy key_share 52 32 90 38 52;
  C.lemma_copy_expr_copied_slice before_key_copy key_share 52 32 90;
  C.lemma_copy_expr_preserves_suffix_slice before_key_copy key_share 52 32 90 84 90;
  assert (pure (Seq.index after_prefix 0 == 2uy));
  assert (pure (Seq.index after_prefix 1 == 0uy));
  assert (pure (Seq.index after_prefix 2 == 0uy));
  assert (pure (Seq.index after_prefix 3 == 86uy));
  assert (pure (Seq.index after_prefix 4 == 0x03uy));
  assert (pure (Seq.index after_prefix 5 == 0x03uy));
  server_hello_prefix_slice after_prefix;
  lemma_server_hello_middle_tail_preserves_prefix after_prefix;
  assert (pure (Seq.equal
    (CL.raw_slice before_random_copy 0 6)
    (CL.raw_slice after_prefix 0 6)));
  Seq.lemma_eq_elim
    (CL.raw_slice before_key_copy 0 6)
    (CL.raw_slice before_random_copy 0 6);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 0 6)
    (CL.raw_slice before_key_copy 0 6);
  Seq.lemma_eq_elim
    (CL.raw_slice before_random_copy 0 6)
    (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy]);
  assert (pure (Seq.index after_middle 38 == 0uy));
  assert (pure (Seq.index after_middle 39 == 0x13uy));
  assert (pure (Seq.index after_middle 40 == 0x03uy));
  assert (pure (Seq.index after_middle 41 == 0uy));
  assert (pure (Seq.index after_middle 42 == 0uy));
  assert (pure (Seq.index after_middle 43 == 46uy));
  assert (pure (Seq.index after_middle 44 == 0uy));
  assert (pure (Seq.index after_middle 45 == 0x33uy));
  assert (pure (Seq.index after_middle 46 == 0uy));
  assert (pure (Seq.index after_middle 47 == 36uy));
  assert (pure (Seq.index after_middle 48 == 0uy));
  assert (pure (Seq.index after_middle 49 == 0x1duy));
  assert (pure (Seq.index after_middle 50 == 0uy));
  assert (pure (Seq.index after_middle 51 == 32uy));
  server_hello_middle_slice after_middle;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 38 52)
    (CL.raw_slice before_key_copy 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice before_key_copy 38 52)
    (CL.raw_slice before_random_copy 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice before_random_copy 38 52)
    (CL.raw_slice after_tail88 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice after_tail88 38 52)
    (CL.raw_slice after_tail87 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice after_tail87 38 52)
    (CL.raw_slice after_tail86 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice after_tail86 38 52)
    (CL.raw_slice after_tail85 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice after_tail85 38 52)
    (CL.raw_slice after_tail84 38 52);
  Seq.lemma_eq_elim
    (CL.raw_slice after_tail84 38 52)
    (CL.raw_slice after_middle 38 52);
  lemma_server_hello_middle_bytes_literal ();
  Seq.lemma_eq_elim
    (CL.raw_slice after_middle 38 52)
    server_hello_middle_bytes;
  Seq.lemma_eq_elim
    server_hello_middle_bytes
    (B.of_list [
      0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy;
      0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy
    ]);
  assert (pure (Seq.index before_random_copy 84 == 0uy));
  assert (pure (Seq.index before_random_copy 85 == 0x2buy));
  assert (pure (Seq.index before_random_copy 86 == 0uy));
  assert (pure (Seq.index before_random_copy 87 == 2uy));
  assert (pure (Seq.index before_random_copy 88 == 0x03uy));
  Seq.lemma_index_upd1 after_tail88 89 0x04uy;
  assert (pure (Seq.index before_random_copy 89 == 0x04uy));
  server_hello_tail_slice before_random_copy;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 84 90)
    (CL.raw_slice before_key_copy 84 90);
  Seq.lemma_eq_elim
    (CL.raw_slice before_key_copy 84 90)
    (CL.raw_slice before_random_copy 84 90);
  Seq.lemma_eq_elim
    (CL.raw_slice before_random_copy 84 90)
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 6 38)
    (CL.raw_slice before_key_copy 6 38);
  Seq.lemma_eq_elim
    (CL.raw_slice before_key_copy 6 38)
    random;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 52 84)
    key_share;
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 0 6)
    (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy])));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 6 38) random));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 38 52)
    (B.of_list [
      0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy;
      0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy
    ])));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 52 84) key_share));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 84 90)
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])));
  lemma_server_hello_prefix_bytes_literal ();
  lemma_server_hello_middle_bytes_literal ();
  Seq.lemma_eq_elim
    server_hello_prefix_bytes
    (B.of_list [2uy; 0uy; 0uy; 86uy; 0x03uy; 0x03uy]);
  Seq.lemma_eq_elim
    server_hello_middle_bytes
    (B.of_list [
      0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy;
      0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy
    ]);
  server_hello_bytes_shape out_bytes random key_share;
  assert (pure (Seq.equal out_bytes (server_hello_bytes random key_share)));
  Seq.lemma_eq_elim random (Ghost.reveal sh).M.random;
  Seq.lemma_eq_elim key_share (Ghost.reveal sh).M.key_share;
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))));
  fold (L.is_valid_server_hello lsh (Ghost.reveal sh));
  90sz
}

fn serialize_server_hello_record_from_selection
  (#sh: erased M.server_hello)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 95)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 95 /\
                SZ.v written == 95 /\
                Seq.equal out_bytes
                  (WS.serialize_record
                    T.Handshake
                    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))) /\
                WS.parse_record out_bytes ==
                  Some
                    (T.Handshake,
                     WS.serialize_server_hello_from_selection (Ghost.reveal sh),
                     95) /\
                CS.raw_records_exactly out_bytes T.Handshake 1)
{
  let mut fragment = [| 0uy; 90sz |];
  let fragment_written =
    serialize_server_hello_from_selection #sh lsh fragment 90sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 90));
  assert (pure (SZ.v fragment_written == 90));
  assert (pure (Seq.equal
    fragment_bytes
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))));

  out.(0sz) <- 22uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  out.(3sz) <- 0uy;
  out.(4sz) <- 90uy;
  with header_bytes. assert (pts_to out header_bytes);
  assert (pure (B.length header_bytes == 95));
  C.copy_array_slice_to_array
    fragment
    90sz
    0sz
    90sz
    out
    out_len
    5sz;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == 95));
  C.lemma_copy_expr_preserves_prefix_slice
    header_bytes
    fragment_bytes
    5
    90
    95
    0
    5;
  C.lemma_copy_expr_copied_slice
    header_bytes
    fragment_bytes
    5
    90
    95;
  assert (pure (Seq.equal (CL.raw_slice out_bytes 5 95) fragment_bytes));
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 5 95)
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh))));
  assert (pure (Seq.equal (CL.raw_slice out_bytes 0 5)
    (B.of_list [22uy; 0x03uy; 0x03uy; 0uy; 90uy])));
  handshake_record_header_literal 90 0uy 90uy;
  Seq.lemma_eq_elim
    (WSR.serialize_record_header T.Handshake 90)
    (B.of_list [22uy; 0x03uy; 0x03uy; 0uy; 90uy]);
  assert (pure (Seq.equal
    (CL.raw_slice out_bytes 0 5)
    (WSR.serialize_record_header T.Handshake 90)));
  CL.lemma_raw_slice_split out_bytes 0 5 95;
  Seq.lemma_eq_elim
    (CL.raw_slice out_bytes 5 95)
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh));
  assert (pure (Seq.equal
    out_bytes
    (B.append
      (WSR.serialize_record_header T.Handshake 90)
      (WS.serialize_server_hello_from_selection (Ghost.reveal sh)))));
  WSR.lemma_serialize_record_reveal
    T.Handshake
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_record
      T.Handshake
      (WS.serialize_server_hello_from_selection (Ghost.reveal sh)))));
  WS.lemma_parse_record_serialize_record
    T.Handshake
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh));
  assert (pure (WS.parse_record out_bytes ==
    Some
      (T.Handshake,
       WS.serialize_server_hello_from_selection (Ghost.reveal sh),
       95)));
  CSL.lemma_parse_record_full_raw_records_exactly
    out_bytes
    T.Handshake
    (WS.serialize_server_hello_from_selection (Ghost.reveal sh));
  assert (pure (CS.raw_records_exactly out_bytes T.Handshake 1));
  95sz
}
