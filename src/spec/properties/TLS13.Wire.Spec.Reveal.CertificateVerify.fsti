module TLS13.Wire.Spec.Reveal.CertificateVerify

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

val lemma_serialize_server_certificate_verify_input_reveal:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (H.certificate_verify_input transcript_hash))

val certificate_verify_context_with_zero:
  b:B.bytes{B.length b == 34}

val lemma_certificate_verify_context_with_zero_literal:
  unit ->
  Lemma (Seq.equal
    certificate_verify_context_with_zero
    (B.of_list [
      0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
      0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
      0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
      0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
      0x79uy; 0uy
    ]))

val certificate_verify_context_byte:
  i:nat{i < 34} ->
  GTot U8.t

val lemma_certificate_verify_context_byte:
  i:nat{i < 34} ->
  Lemma (Seq.index certificate_verify_context_with_zero i ==
         certificate_verify_context_byte i)

val lemma_certificate_verify_context_index_0: unit -> Lemma (Seq.index certificate_verify_context_with_zero 0 == 0x54uy)
val lemma_certificate_verify_context_index_1: unit -> Lemma (Seq.index certificate_verify_context_with_zero 1 == 0x4cuy)
val lemma_certificate_verify_context_index_2: unit -> Lemma (Seq.index certificate_verify_context_with_zero 2 == 0x53uy)
val lemma_certificate_verify_context_index_3: unit -> Lemma (Seq.index certificate_verify_context_with_zero 3 == 0x20uy)
val lemma_certificate_verify_context_index_4: unit -> Lemma (Seq.index certificate_verify_context_with_zero 4 == 0x31uy)
val lemma_certificate_verify_context_index_5: unit -> Lemma (Seq.index certificate_verify_context_with_zero 5 == 0x2euy)
val lemma_certificate_verify_context_index_6: unit -> Lemma (Seq.index certificate_verify_context_with_zero 6 == 0x33uy)
val lemma_certificate_verify_context_index_7: unit -> Lemma (Seq.index certificate_verify_context_with_zero 7 == 0x2cuy)
val lemma_certificate_verify_context_index_8: unit -> Lemma (Seq.index certificate_verify_context_with_zero 8 == 0x20uy)
val lemma_certificate_verify_context_index_9: unit -> Lemma (Seq.index certificate_verify_context_with_zero 9 == 0x73uy)
val lemma_certificate_verify_context_index_10: unit -> Lemma (Seq.index certificate_verify_context_with_zero 10 == 0x65uy)
val lemma_certificate_verify_context_index_11: unit -> Lemma (Seq.index certificate_verify_context_with_zero 11 == 0x72uy)
val lemma_certificate_verify_context_index_12: unit -> Lemma (Seq.index certificate_verify_context_with_zero 12 == 0x76uy)
val lemma_certificate_verify_context_index_13: unit -> Lemma (Seq.index certificate_verify_context_with_zero 13 == 0x65uy)
val lemma_certificate_verify_context_index_14: unit -> Lemma (Seq.index certificate_verify_context_with_zero 14 == 0x72uy)
val lemma_certificate_verify_context_index_15: unit -> Lemma (Seq.index certificate_verify_context_with_zero 15 == 0x20uy)
val lemma_certificate_verify_context_index_16: unit -> Lemma (Seq.index certificate_verify_context_with_zero 16 == 0x43uy)
val lemma_certificate_verify_context_index_17: unit -> Lemma (Seq.index certificate_verify_context_with_zero 17 == 0x65uy)
val lemma_certificate_verify_context_index_18: unit -> Lemma (Seq.index certificate_verify_context_with_zero 18 == 0x72uy)
val lemma_certificate_verify_context_index_19: unit -> Lemma (Seq.index certificate_verify_context_with_zero 19 == 0x74uy)
val lemma_certificate_verify_context_index_20: unit -> Lemma (Seq.index certificate_verify_context_with_zero 20 == 0x69uy)
val lemma_certificate_verify_context_index_21: unit -> Lemma (Seq.index certificate_verify_context_with_zero 21 == 0x66uy)
val lemma_certificate_verify_context_index_22: unit -> Lemma (Seq.index certificate_verify_context_with_zero 22 == 0x69uy)
val lemma_certificate_verify_context_index_23: unit -> Lemma (Seq.index certificate_verify_context_with_zero 23 == 0x63uy)
val lemma_certificate_verify_context_index_24: unit -> Lemma (Seq.index certificate_verify_context_with_zero 24 == 0x61uy)
val lemma_certificate_verify_context_index_25: unit -> Lemma (Seq.index certificate_verify_context_with_zero 25 == 0x74uy)
val lemma_certificate_verify_context_index_26: unit -> Lemma (Seq.index certificate_verify_context_with_zero 26 == 0x65uy)
val lemma_certificate_verify_context_index_27: unit -> Lemma (Seq.index certificate_verify_context_with_zero 27 == 0x56uy)
val lemma_certificate_verify_context_index_28: unit -> Lemma (Seq.index certificate_verify_context_with_zero 28 == 0x65uy)
val lemma_certificate_verify_context_index_29: unit -> Lemma (Seq.index certificate_verify_context_with_zero 29 == 0x72uy)
val lemma_certificate_verify_context_index_30: unit -> Lemma (Seq.index certificate_verify_context_with_zero 30 == 0x69uy)
val lemma_certificate_verify_context_index_31: unit -> Lemma (Seq.index certificate_verify_context_with_zero 31 == 0x66uy)
val lemma_certificate_verify_context_index_32: unit -> Lemma (Seq.index certificate_verify_context_with_zero 32 == 0x79uy)
val lemma_certificate_verify_context_index_33: unit -> Lemma (Seq.index certificate_verify_context_with_zero 33 == 0uy)

val lemma_serialize_server_certificate_verify_input_bytes:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (B.append
      (B.append (Seq.create 64 0x20uy) certificate_verify_context_with_zero)
      transcript_hash))
