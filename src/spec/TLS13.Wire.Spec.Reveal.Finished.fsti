module TLS13.Wire.Spec.Reveal.Finished

module B = TLS13.Bytes
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* A [M.Finished] now wraps the generated [GFin.finished] record, which is the raw
   32-byte verify_data ([Seq.lseq U8.t 32]).  The wire image of a Finished
   handshake message is the 4-byte header [20; 0; 0; 32] (HandshakeType.finished
   plus the u24 body length 32) followed by the verify_data itself. *)

val lemma_serialize_finished_reveal:
  fin:GFin.finished ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.Finished fin))
    (B.append (B.of_list [20uy; 0uy; 0uy; 32uy]) fin))

val lemma_parse_finished_handshake:
  fin:GFin.finished ->
  Lemma (WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.Finished fin)) ==
         Some (M.TlsHandshake (M.Finished fin)))
