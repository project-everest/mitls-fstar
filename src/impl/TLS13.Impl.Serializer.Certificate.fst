module TLS13.Impl.Serializer.Certificate

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module GCert = TLS13.Wire.Generated.Certificate
module SerH = TLS13.Impl.Serializer.FinishedPOC

fn serialize_certificate_from_credential
  (#cert: erased GCert.certificate)
  (#chain: erased B.bytes)
  (lcert: L.certificate_msg)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 1 <= Seq.length (Ghost.reveal chain) /\
                 Seq.length (Ghost.reveal chain) <= 32768 /\
                 Ghost.reveal cert == SerH.poc_canonical_cert (Ghost.reveal chain) /\
                 SZ.v out_len ==
                   B.length (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg lcert (Ghost.reveal cert) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.Certificate (Ghost.reveal cert))))
{
  SerH.serialize_certificate_handshake_poc #cert #chain lcert out out_len #old_bytes
}
