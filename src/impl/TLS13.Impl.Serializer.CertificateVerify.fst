module TLS13.Impl.Serializer.CertificateVerify

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
module GCV = TLS13.Wire.Generated.CertificateVerify
module SerH = TLS13.Impl.Serializer.FinishedPOC

fn serialize_certificate_verify_from_signature
  (#cv: erased GCV.certificateVerify)
  (lcv: L.certificate_verify)
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len ==
                   B.length (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_verify lcv (Ghost.reveal cv) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == SZ.v out_len /\
                Seq.equal out_bytes
                  (WS.serialize_handshake (M.CertificateVerify (Ghost.reveal cv))))
{
  SerH.serialize_certificate_verify_handshake_poc #cv lcv out out_len #old_bytes
}
