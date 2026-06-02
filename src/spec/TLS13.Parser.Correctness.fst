module TLS13.Parser.Correctness

// Pure F* lemmas stating parser correctness properties
// These are the admits that connect Pulse implementations to Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module SHC = TLS13.ServerHello.Checks
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
        Seq.index header_bytes 2 = 0x03uy &&
        WS.read_u16 header_bytes 3 <= 16640
      ))
    (ensures
      ok <==> Some? (WS.parse_record_header header_bytes))
  =
    WS.lemma_parse_record_header_some_iff header_bytes

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
      // ok must be computed from the scoped byte-level ServerHello checks.
      ok == SHC.server_hello_ok input_bytes /\
      // random_bytes must be extracted from input[6..37] (positions 6-37 inclusive)
      (ok ==> (
        B.length input_bytes == 90 /\
        Seq.equal random_bytes (Seq.slice input_bytes 6 38)
      )) /\
      // key_share_bytes must correspond to the accepted extension order.
      (ok ==> (
        (SHC.server_hello_ok_52 input_bytes /\
         Seq.equal key_share_bytes (Seq.slice input_bytes 52 84)) \/
        (SHC.server_hello_ok_58 input_bytes /\
         Seq.equal key_share_bytes (Seq.slice input_bytes 58 90))
      ))
    )
    (ensures
      (ok <==> Some? (WS.parse_supported_server_hello input_bytes)) /\
      (ok ==> (
        let Some sh = WS.parse_supported_server_hello input_bytes in
        Seq.equal random_bytes sh.M.random /\
        Seq.equal key_share_bytes sh.M.key_share
      )))
  =
    WS.lemma_parse_supported_server_hello_ok input_bytes;
    if ok then
      begin
        WS.lemma_parse_supported_server_hello_fields input_bytes;
        match WS.parse_supported_server_hello input_bytes with
        | None -> ()
        | Some sh ->
          Seq.lemma_eq_elim random_bytes (Seq.slice input_bytes 6 38);
          Seq.lemma_eq_elim sh.M.random (Seq.slice input_bytes 6 38);
          Seq.lemma_eq_refl random_bytes sh.M.random;
          if SHC.server_hello_ok_52 input_bytes then
            begin
              Seq.lemma_eq_elim key_share_bytes (Seq.slice input_bytes 52 84);
              Seq.lemma_eq_elim sh.M.key_share (Seq.slice input_bytes 52 84);
              Seq.lemma_eq_refl key_share_bytes sh.M.key_share
            end
          else
            begin
              assert (SHC.server_hello_ok_58 input_bytes);
              Seq.lemma_eq_elim key_share_bytes (Seq.slice input_bytes 58 90);
              Seq.lemma_eq_elim sh.M.key_share (Seq.slice input_bytes 58 90);
              Seq.lemma_eq_refl key_share_bytes sh.M.key_share
            end
      end
    else ()
