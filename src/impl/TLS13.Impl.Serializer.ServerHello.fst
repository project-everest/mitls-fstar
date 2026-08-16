module TLS13.Impl.Serializer.ServerHello

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module CS = TLS13.Spec.StateMachine
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GCS = TLS13.Wire.Generated.CipherSuite
module SerH = TLS13.Impl.Serializer.Handshake
module SerPR = TLS13.Impl.Serializer.ProtectedRecord
module V = Pulse.Lib.Vec

(* (a) Build-direction ServerHello handshake serializer: a thin POC wrapper. *)
fn serialize_server_hello_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#sid: erased B.bytes)
  (#g: erased TLS13.Wire.Generated.NamedGroup.namedGroup)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 58 + Seq.length (Ghost.reveal ks) + Seq.length (Ghost.reveal sid) /\
                 Seq.length (Ghost.reveal rnd) == 32 /\
                 (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 (Ghost.reveal g == TLS13.Wire.Generated.NamedGroup.X25519 \/
                  Ghost.reveal g == TLS13.Wire.Generated.NamedGroup.Secp256r1) /\
                 Seq.length (Ghost.reveal ks) ==
                   TLS13.Crypto.Spec.kex_public_len
                     (TLS13.Wire.Semantics.kex_group_of_named_group (Ghost.reveal g)) /\
                 Seq.length (Ghost.reveal sid) <= 32 /\
                 Ghost.reveal sh ==
                   SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal sid) (Ghost.reveal g) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh))))
{
  SerH.serialize_server_hello_handshake_poc #sh #rnd #ks #sid #g #cs lsh out out_len #old_bytes
}

(* (b) Build-direction ServerHello record: serialize the handshake fragment,
   then frame it with the generated record writer. *)
fn serialize_server_hello_record_from_selection
  (#sh: erased GSH.serverHello)
  (#rnd: erased B.bytes)
  (#ks: erased B.bytes)
  (#sid: erased B.bytes)
  (#g: erased TLS13.Wire.Generated.NamedGroup.namedGroup)
  (#cs: erased GCS.cipherSuite)
  (lsh: L.server_hello)
  (sid_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_server_hello lsh (Ghost.reveal sh) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v sid_len == Seq.length (Ghost.reveal sid) /\
                 SZ.v out_len == 63 + Seq.length (Ghost.reveal ks) + Seq.length (Ghost.reveal sid) /\
                 Seq.length (Ghost.reveal rnd) == 32 /\
                 (Ghost.reveal rnd <: Seq.lseq U8.t 32) <> GSHB.serverHello_body_cst /\
                 (Ghost.reveal g == TLS13.Wire.Generated.NamedGroup.X25519 \/
                  Ghost.reveal g == TLS13.Wire.Generated.NamedGroup.Secp256r1) /\
                 Seq.length (Ghost.reveal ks) ==
                   TLS13.Crypto.Spec.kex_public_len
                     (TLS13.Wire.Semantics.kex_group_of_named_group (Ghost.reveal g)) /\
                 Seq.length (Ghost.reveal sid) <= 32 /\
                 Ghost.reveal sh ==
                   SerH.poc_canonical_sh (Ghost.reveal rnd) (Ghost.reveal ks) (Ghost.reveal sid) (Ghost.reveal g) (Ghost.reveal cs))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello lsh (Ghost.reveal sh) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_record
                    T.Handshake
                    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))) /\
                WS.parse_record out_bytes ==
                  Some
                    (T.Handshake,
                     WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)),
                     SZ.v out_len) /\
                CS.raw_records_exactly out_bytes T.Handshake 1)
{
  (* RFC 8446 4.1.3: the message is 58 bytes plus the key-share and the
     echoed legacy_session_id, so the fragment buffer must be sized at run
     time.  The record adds a 5-byte header, so the fragment is exactly
     [out_len - 5].  Pulse stack arrays need a constant extent, hence the
     heap vec. *)
  let fragment_len = out_len `SZ.sub` 5sz;
  let fragment_vec = V.alloc 0uy fragment_len;
  V.to_array_pts_to fragment_vec;
  let fragment_written =
    serialize_server_hello_from_selection #sh #rnd #ks #sid #g #cs lsh
      (V.vec_to_array fragment_vec) fragment_len;
  with fragment_bytes. assert (pts_to (V.vec_to_array fragment_vec) fragment_bytes);
  assert (pure (B.length fragment_bytes == SZ.v fragment_len));
  assert (pure (SZ.v fragment_written == SZ.v fragment_len));
  assert (pure (Seq.equal
    fragment_bytes
    (WS.serialize_handshake (M.ServerHello (Ghost.reveal sh)))));

  let written =
    SerPR.serialize_raw_record T.Handshake (V.vec_to_array fragment_vec) fragment_len
      out out_len;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v written == SZ.v out_len));
  C.lemma_raw_slice_all out_bytes;
  Seq.lemma_eq_elim (Seq.slice out_bytes 0 (SZ.v out_len)) out_bytes;
  V.to_vec_pts_to fragment_vec;
  V.free fragment_vec;
  written
}
