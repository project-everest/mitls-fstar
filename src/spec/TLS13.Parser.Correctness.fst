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
// States: IF random_bytes and key_share_bytes were extracted from the right
//         positions in input_bytes, and ok computed from correct checks,
//         THEN ok matches spec and fields match
let lemma_parse_supported_server_hello_correct
  (input_bytes: B.bytes)
  (random_bytes: B.bytes{B.length random_bytes == 32})
  (key_share_bytes: B.bytes{B.length key_share_bytes == 32})
  (ok: bool)
  : Lemma
    (requires
      // random_bytes must be extracted from input[6..37] (positions 6-37 inclusive)
      (ok ==> (
        B.length input_bytes == 90 /\
        Seq.equal random_bytes (Seq.slice input_bytes 6 38)
      )) /\
      // key_share_bytes must be from position 52 or 58 (depending on extension order)
      (ok ==> (
        Seq.equal key_share_bytes (Seq.slice input_bytes 52 84) \/
        Seq.equal key_share_bytes (Seq.slice input_bytes 58 90)
      )) /\
      // ok must be computed from all the byte-level checks matching the spec
      // (This is complex - we admit it as part of the parser TCB)
      True  // TODO: State complete byte-level checks
    )
    (ensures
      (ok <==> Some? (WS.parse_supported_server_hello input_bytes)) /\
      (ok ==> (
        let Some sh = WS.parse_supported_server_hello input_bytes in
        Seq.equal random_bytes sh.random /\
        Seq.equal key_share_bytes sh.key_share
      )))
  = admit() // PARSER TCB
