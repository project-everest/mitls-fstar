module TLS13.Wire.Spec.Reveal.ServerHello.Parseback

module M = TLS13.Messages
module GSH = TLS13.Wire.Generated.ServerHello
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* If the wire image of [M.ServerHello sh] parses back as [M.ServerHello parsed_sh]
   then [parsed_sh == sh]: the generated codec round-trips exactly, so any field
   (in particular the x25519 key_share read via TLS13.Wire.Semantics) coincides.
   The requires additionally rules out the HelloRetryRequest body, whose wire image
   parses as [M.HelloRetryRequest] rather than an [M.ServerHello]. *)
val lemma_parse_tls_message_serialize_server_hello_key_share
  (sh:GSH.serverHello)
  (parsed_sh:GSH.serverHello)
  : Lemma
      (requires
        WS.parse_tls_message
          T.Handshake
          (WS.serialize_handshake (M.ServerHello sh)) ==
          Some (M.TlsHandshake (M.ServerHello parsed_sh)))
      (ensures parsed_sh == sh)
