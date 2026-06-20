module TLS13.Wire.Spec.Reveal.ClientHello.Parseback

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module WS = TLS13.Wire.Spec
module Seq = FStar.Seq

val lemma_parse_client_hello_serialize_client_hello
  (ch:M.client_hello{ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                     ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                     B.length ch.M.body == 0 /\
                     (match ch.M.server_name with
                      | None -> True
                      | Some hostname -> B.length hostname <= 255)})
  : Lemma
      (requires (match ch.M.server_name with
                 | None -> True
                 | Some hostname -> B.length hostname > 0))
      (ensures WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)

val lemma_parse_tls_message_serialize_client_hello
  (ch:M.client_hello{ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                      ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                      B.length ch.M.body == 0 /\
                      (match ch.M.server_name with
                       | None -> True
                       | Some hostname -> B.length hostname <= 255)})
  : Lemma
      (requires (match ch.M.server_name with
                 | None -> True
                 | Some hostname -> B.length hostname > 0))
      (ensures
        exists (parsed_ch:M.client_hello).
          WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.ClientHello ch)) ==
            Some (M.TlsHandshake (M.ClientHello parsed_ch)) /\
          Seq.equal ch.M.random parsed_ch.M.random /\
          ch.M.server_name == parsed_ch.M.server_name /\
          Seq.equal ch.M.key_share parsed_ch.M.key_share /\
          ch.M.cipher_suites == parsed_ch.M.cipher_suites /\
          ch.M.signature_schemes == parsed_ch.M.signature_schemes /\
          parsed_ch.M.body == WS.serialize_handshake (M.ClientHello ch))
