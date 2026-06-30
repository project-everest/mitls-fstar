module TLS13.Impl.Serializer.ServerHello

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
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
module SerH = TLS13.Impl.Serializer.FinishedPOC

(* Build-direction ServerHello serializer, retargeted onto the verified copyful
   POC writer [SerH.serialize_server_hello_handshake_poc].  The ServerHello
   message is under-determined by the L mirror alone, so the POC (and hence this
   wrapper) is pinned to the canonical ServerHello shape
   [SerH.poc_canonical_sh rnd ks cs]; callers establish the pin. *)
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
