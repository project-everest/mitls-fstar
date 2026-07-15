module TLS13.Impl.Serializer.ServerHello

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
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GCS = TLS13.Wire.Generated.CipherSuite
module SerH = TLS13.Impl.Serializer.Handshake

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

(* (a) Build-direction ServerHello handshake serializer: a thin POC wrapper. *)
fn serialize_server_hello_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 90 /\
                 Seq.length (Ghost.reveal rnd) == 32 /\
                 (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 Seq.length (Ghost.reveal ks) == 32 /\
                 Ghost.reveal cs == GCS.TLS_CHACHA20_POLY1305_SHA256 /\
                 Ghost.reveal sh ==
                   SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 90 /\
                SZ.v written == 90 /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  SerH.serialize_server_hello_handshake_poc #sh #rnd #ks #cs lsh out out_len #old_bytes
}

(* (b) Build-direction ServerHello record: call (a) to lay down the 90-byte
   handshake fragment, prepend the 5-byte Handshake record header, and prove the
   95 bytes == [WS.serialize_record T.Handshake (serialize_handshake (M.ServerHello sh))]
   via the restored record-framing reveal helpers. *)
fn serialize_server_hello_record_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 95 /\
                 Seq.length (Ghost.reveal rnd) == 32 /\
                 (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 Seq.length (Ghost.reveal ks) == 32 /\
                 Ghost.reveal cs == GCS.TLS_CHACHA20_POLY1305_SHA256 /\
                 Ghost.reveal sh ==
                   SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 95 /\
                SZ.v written == 95 /\
                Seq.equal out_bytes
                  (WS.serialize_record
                    T.Handshake
                    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))) /\
                WS.parse_record out_bytes ==
                  Some
                    (T.Handshake,
                     WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)),
                     95) /\
                CS.raw_records_exactly out_bytes T.Handshake 1)
{
  let mut fragment = [| 0uy; 90sz |];
  let fragment_written =
    serialize_server_hello_from_selection #sh #rnd #ks #cs lsh fragment 90sz;
  with fragment_bytes. assert (pts_to fragment fragment_bytes);
  assert (pure (B.length fragment_bytes == 90));
  assert (pure (SZ.v fragment_written == 90));
  assert (pure (Seq.equal
    fragment_bytes
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))));

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
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))));
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
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  assert (pure (Seq.equal
    out_bytes
    (B.append
      (WSR.serialize_record_header T.Handshake 90)
      (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))));
  WSR.lemma_serialize_record_reveal
    T.Handshake
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_record
      T.Handshake
      (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))));
  WS.lemma_parse_record_serialize_record
    T.Handshake
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  assert (pure (WS.parse_record out_bytes ==
    Some
      (T.Handshake,
       WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)),
       95)));
  CSL.lemma_parse_record_full_raw_records_exactly
    out_bytes
    T.Handshake
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)));
  assert (pure (CS.raw_records_exactly out_bytes T.Handshake 1));
  95sz
}
