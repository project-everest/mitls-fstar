module TLS13.Wire.Spec.Reveal.ServerHello.Parseback

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module WS = TLS13.Wire.Spec
module Seq = FStar.Seq

val lemma_parse_tls_message_serialize_server_hello_key_share
  (sh:M.server_hello{B.length sh.M.body == 0 /\
                     sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  (parsed_sh:M.server_hello)
  : Lemma
      (requires
        WS.parse_tls_message
          T.Handshake
          (WS.serialize_handshake (M.ServerHello sh)) ==
          Some (M.TlsHandshake (M.ServerHello parsed_sh)))
      (ensures Seq.equal parsed_sh.M.key_share sh.M.key_share)
