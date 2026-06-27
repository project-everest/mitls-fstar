module TLS13.Impl.Serializer.Finished

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal

fn serialize_server_finished
  (#fin: erased M.finished)
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
                  (WS.serialize_server_finished (Ghost.reveal fin)) /\
                WS.parse_tls_message T.Handshake out_bytes ==
                  Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  unfold (L.is_valid_finished lfin (Ghost.reveal fin));
  with verify_data. assert (V.pts_to lfin.L.finished_verify_data verify_data);
  out.(0sz) <- 20uy;
  out.(1sz) <- 0uy;
  out.(2sz) <- 0uy;
  out.(3sz) <- 32uy;
  V.to_array_pts_to lfin.L.finished_verify_data;
  C.copy_array_slice_to_array
    (V.vec_to_array lfin.L.finished_verify_data)
    32sz
    0sz
    32sz
    out
    36sz
    4sz;
  V.to_vec_pts_to lfin.L.finished_verify_data;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == 36));
  assert (pure (B.length verify_data == 32));
  WS.lemma_serialize_finished_len (Ghost.reveal fin);
  WSR.lemma_serialize_finished_reveal (Ghost.reveal fin);
  assert (pure (Seq.equal verify_data (Ghost.reveal fin).M.verify_data));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  WS.lemma_fixed_server_handshake_serializers
    {
      M.random = Seq.create 32 0uy;
      M.key_share = Seq.create 32 0uy;
      M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
      M.body = B.empty;
    }
    { M.chain = []; M.body = B.empty }
    { M.scheme = T.Rsa_pss_rsae_sha256; M.signature = B.empty; M.body = B.empty }
    (Ghost.reveal fin);
  assert (pure (Seq.equal
    (WS.serialize_server_finished (Ghost.reveal fin))
    (WS.serialize_handshake (M.Finished (Ghost.reveal fin)))));
  Seq.lemma_eq_elim
    (WS.serialize_server_finished (Ghost.reveal fin))
    (WS.serialize_handshake (M.Finished (Ghost.reveal fin)));
  assert (pure (Seq.equal
    out_bytes
    (WS.serialize_server_finished (Ghost.reveal fin))));
  WSR.lemma_parse_finished_handshake (Ghost.reveal fin);
  Seq.lemma_eq_elim
    out_bytes
    (WS.serialize_handshake (M.Finished (Ghost.reveal fin)));
  fold (L.is_valid_finished lfin (Ghost.reveal fin));
  36sz
}
