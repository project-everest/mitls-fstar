module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Low

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module LP = LowParse.Spec
module WS = TLS13.Wire.Spec
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GCHEXT = TLS13.Wire.Generated.ClientHello_extensions
module GCH = TLS13.Wire.Generated.ClientHello
module GNG = TLS13.Wire.Generated.NamedGroup
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry

val mk_ext_list_some
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : GCHEXT.clientHello_extensions

val mk_ext_list_none
  (key: B.bytes{B.length key == 32})
  : GCHEXT.clientHello_extensions

val mk_ch_low_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  : GCH.clientHello

val mk_ch_low_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32})
  : GCH.clientHello

val lemma_lp_ch_ext_ser_some
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GCHEXT.clientHello_extensions_serializer (mk_ext_list_some hostname key))
      (Seq.append
        (B.of_list [TLS13.Wire.Spec.Reveal.ClientHello.client_hello_byte (B.length (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_extensions_bytes hostname key) / 256);
                    TLS13.Wire.Spec.Reveal.ClientHello.client_hello_byte (B.length (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_extensions_bytes hostname key))])
        (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_extensions_bytes hostname key)))

val lemma_lp_ch_ext_ser_none
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GCHEXT.clientHello_extensions_serializer (mk_ext_list_none key))
      (Seq.append
        (B.of_list [TLS13.Wire.Spec.Reveal.ClientHello.client_hello_byte (B.length (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_common_extensions_bytes key) / 256);
                    TLS13.Wire.Spec.Reveal.ClientHello.client_hello_byte (B.length (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_common_extensions_bytes key))])
        (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_common_extensions_bytes key)))

val lemma_lp_ch_low_bytes_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       B.length ch.M.body == 0})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low : GCH.clientHello =
         { GCH.legacy_version = GPV.TLS_1p2;
           GCH.random = ch.M.random;
           GCH.legacy_session_id = B.empty;
           GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
           GCH.legacy_compression_methods = B.of_list [0uy];
           GCH.extensions = mk_ext_list_some hostname ch.M.key_share } in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes ch.M.random hostname ch.M.key_share) /\
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share) /\
       WS.synth_client_hello low == Some ch)

val lemma_lp_ch_low_bytes_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       ch.M.server_name == None /\
                       B.length ch.M.body == 0})
  : Lemma
      (let low : GCH.clientHello =
         { GCH.legacy_version = GPV.TLS_1p2;
           GCH.random = ch.M.random;
           GCH.legacy_session_id = B.empty;
           GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
           GCH.legacy_compression_methods = B.of_list [0uy];
           GCH.extensions = mk_ext_list_none ch.M.key_share } in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes ch.M.random B.empty ch.M.key_share) /\
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share) /\
       WS.synth_client_hello low == Some ch)

val lemma_lp_ch_low_body_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                      ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                      ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                      B.length ch.M.body == 0})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low = mk_ch_low_some ch hostname in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes
                  ch.M.random
                  (match ch.M.server_name with
                   | Some h -> h
                   | None -> B.empty)
                  ch.M.key_share))

val lemma_lp_ch_low_body_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                      ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                      ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                      ch.M.server_name == None /\
                      B.length ch.M.body == 0})
  : Lemma
      (let low = mk_ch_low_none ch in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_body_bytes
                  ch.M.random
                  (match ch.M.server_name with
                   | Some h -> h
                   | None -> B.empty)
                  ch.M.key_share))

val lemma_lp_ch_low_synth_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                      ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                      ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                      B.length ch.M.body == 0})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low = mk_ch_low_some ch hostname in
       WS.synth_client_hello low == Some ch)

val lemma_lp_ch_low_synth_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                      ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                      ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                      ch.M.server_name == None /\
                      B.length ch.M.body == 0})
  : Lemma
      (let low = mk_ch_low_none ch in
       WS.synth_client_hello low == Some ch)
