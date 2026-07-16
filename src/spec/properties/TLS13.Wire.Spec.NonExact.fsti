module TLS13.Wire.Spec.NonExact

module B = TLS13.Bytes
module T = TLS13.Types
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module LP = LowParse.Spec

(* When the QuackyDucky handshake parser succeeds on [fragment] but does not
   consume it entirely, [parse_tls_message] of a Handshake record is [None].
   (See the implementation for the proof, which opens the generated grammar to
   expose the 1-byte message-type tag and observe that the NewSessionTicket
   handshake case is uninhabited.) *)
val lemma_ptm_handshake_nonexact_none
  (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              consumed <> B.length fragment)
    (ensures WS.parse_tls_message T.Handshake fragment == None)
