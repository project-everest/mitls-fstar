module TLS13.Wire.Spec.Reveal.FinishedRoundTrip

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

val lemma_parse_finished_handshake_round_trip:
  fragment:B.bytes ->
  fin:M.finished ->
  Lemma
    (requires
      WS.parse_tls_message T.Handshake fragment ==
        Some (M.TlsHandshake (M.Finished fin)))
    (ensures Seq.equal fragment (WS.serialize_handshake (M.Finished fin)))
