module TLS13.Wire.Spec.Reveal.ClientHello.Parseback

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module WS = TLS13.Wire.Spec

val lemma_parse_client_hello_serialize_client_hello
  (ch:M.client_hello{ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                     ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                     (match ch.M.server_name with
                      | None -> True
                      | Some hostname -> B.length hostname <= 255)})
  : Lemma
      (requires (match ch.M.server_name with
                 | None -> True
                 | Some hostname -> B.length hostname > 0))
      (ensures WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)
