module TLS13.Impl.Serializer.Finished

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module SerH = TLS13.Impl.Serializer.FinishedPOC
module GFin = TLS13.Wire.Generated.Finished

fn serialize_server_finished
  (#fin: erased GFin.finished)
  (lfin: L.finished)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          pts_to out out_bytes **
          pure (B.length out_bytes == 36 /\
                SZ.v written == 36 /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                WS.parse_tls_message T.Handshake out_bytes ==
                  Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  SerH.serialize_finished_handshake_poc #fin lfin out out_len #old_bytes
}
