module TLS13.Wire.Spec.Reveal.Finished

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

val lemma_serialize_finished_reveal:
  fin:M.finished ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.Finished fin))
    (B.append (B.of_list [20uy; 0uy; 0uy; 32uy]) fin.M.verify_data))

val lemma_parse_finished_handshake:
  fin:M.finished ->
  Lemma (WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.Finished fin)) ==
         Some (M.TlsHandshake (M.Finished fin)))
