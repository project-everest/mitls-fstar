module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Leaves

module B = TLS13.Bytes
module Seq = FStar.Seq
module LP = LowParse.Spec
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCS = TLS13.Wire.Generated.CipherSuite
module GCCS = TLS13.Wire.Generated.ClientHello_cipher_suites

val lemma_lp_pv_tls12 ()
  : Lemma (Seq.equal (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p2)
                     (B.of_list [0x03uy; 0x03uy]))

val lemma_lp_random (r:B.bytes{B.length r == 32})
  : Lemma (LP.serialize GRandom.random_serializer r == r)

val lemma_lp_session_id ()
  : Lemma (Seq.equal (LP.serialize GSID.clientHello_legacy_session_id_serializer B.empty)
                     (B.of_list [0uy]))

val lemma_lp_cipher_suites ()
  : Lemma (Seq.equal (LP.serialize GCCS.clientHello_cipher_suites_serializer
                                   [GCS.TLS_CHACHA20_POLY1305_SHA256])
                     (B.of_list [0uy; 2uy; 0x13uy; 0x03uy]))

val lemma_lp_compression ()
  : Lemma (Seq.equal (LP.serialize GComp.clientHello_legacy_compression_methods_serializer
                                   (B.of_list [0uy]))
                     (B.of_list [1uy; 0uy]))
