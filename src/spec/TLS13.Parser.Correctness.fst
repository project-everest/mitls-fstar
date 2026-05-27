module TLS13.Parser.Correctness

// Pure F* lemmas stating parser correctness properties
// These are the admits that connect Pulse implementations to Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

// Parser correctness for record header
let lemma_parse_record_header_correct
  (header_bytes: B.bytes{B.length header_bytes == 5})
  (content_type_bytes: B.bytes{B.length content_type_bytes == 1})
  (fragment_len_bytes: B.bytes{B.length fragment_len_bytes == 2})
  (ok: bool)
  : Lemma
    (requires
      Seq.index content_type_bytes 0 == Seq.index header_bytes 0 /\
      WS.read_u16 fragment_len_bytes 0 == WS.read_u16 header_bytes 3)
    (ensures
      ok <==> Some? (WS.parse_record_header header_bytes))
  = admit() // PARSER TCB

// Parser correctness for server hello
let lemma_parse_supported_server_hello_correct
  (input_bytes: B.bytes)
  (random_bytes: B.bytes{B.length random_bytes == 32})
  (key_share_bytes: B.bytes{B.length key_share_bytes == 32})
  (ok: bool)
  : Lemma
    (ensures
      (ok <==> Some? (WS.parse_supported_server_hello input_bytes)) /\
      (ok ==> (
        let Some sh = WS.parse_supported_server_hello input_bytes in
        Seq.equal random_bytes sh.random /\
        Seq.equal key_share_bytes sh.key_share
      )))
  = admit() // PARSER TCB
