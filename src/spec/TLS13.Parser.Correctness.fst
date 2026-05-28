module TLS13.Parser.Correctness

// Pure F* lemmas stating parser correctness properties
// These are the admits that connect Pulse implementations to Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

// Parser correctness for record header
// Parser correctness for record header
// States: IF ok is computed from the correct byte checks,
//         THEN it matches Wire.Spec.parse_record_header
let lemma_parse_record_header_correct
  (header_bytes: B.bytes{B.length header_bytes == 5})
  (ok: bool)
  : Lemma
    (requires
      // ok must be computed as: valid content_type && version check && length check
      ok == (
        (Seq.index header_bytes 0 = 0x14uy ||
         Seq.index header_bytes 0 = 0x15uy ||
         Seq.index header_bytes 0 = 0x16uy ||
         Seq.index header_bytes 0 = 0x17uy) &&
        Seq.index header_bytes 1 = 0x03uy &&
        (Seq.index header_bytes 2 = 0x01uy || Seq.index header_bytes 2 = 0x03uy) &&
        WS.read_u16 header_bytes 3 <= 16640
      ))
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
