module TLS13.Wire.Spec.Reveal.ClientHello.Parseback
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.Random
friend TLS13.Wire.Generated.CipherSuite
friend TLS13.Wire.Generated.ClientHello_legacy_session_id
friend TLS13.Wire.Generated.ClientHello_cipher_suites
friend TLS13.Wire.Generated.ClientHello_legacy_compression_methods
friend TLS13.Wire.Generated.ExtensionClientHello
friend TLS13.Wire.Generated.ClientHello_extensions
friend TLS13.Wire.Generated.ClientHello
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module WS = TLS13.Wire.Spec
module LP = LowParse.Spec
module RCH = TLS13.Wire.Spec.Reveal.ClientHello
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCS = TLS13.Wire.Generated.CipherSuite
module GCH = TLS13.Wire.Generated.ClientHello
module PBL = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Low

let client_hello_body_bytes random hostname key_share = RCH.client_hello_body_bytes random hostname key_share
let lemma_client_hello_body_bytes_reveal hello = RCH.lemma_client_hello_body_bytes_reveal hello
let lemma_client_hello_extensions_len hostname key_share = RCH.lemma_client_hello_extensions_len hostname key_share

#push-options "--split_queries always --fuel 8 --ifuel 2 --z3rlimit 80"
let lemma_parse_client_hello_serialize_client_hello
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
=
  match ch.M.server_name with
  | Some hostname ->
    assert (B.length hostname <= 255);
    assert (B.length hostname > 0);
    lemma_client_hello_body_bytes_reveal ch;
    lemma_client_hello_extensions_len hostname ch.M.key_share;
    let low : GCH.clientHello =
      { GCH.legacy_version = GPV.TLS_1p2;
        GCH.random = ch.M.random;
        GCH.legacy_session_id = B.empty;
        GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
        GCH.legacy_compression_methods = B.of_list [0uy];
        GCH.extensions = PBL.mk_ext_list_some hostname ch.M.key_share } in
    PBL.lemma_lp_ch_low_bytes_some ch hostname;
    Seq.lemma_eq_elim
      (LP.serialize GCH.clientHello_serializer low)
      (client_hello_body_bytes ch.M.random hostname ch.M.key_share);
    Seq.lemma_eq_elim
      (WS.serialize_client_hello ch)
      (client_hello_body_bytes ch.M.random hostname ch.M.key_share);
    LP.parse_serialize GCH.clientHello_serializer low;
    assert_norm (WS.synth_client_hello low == Some ch);
    assert (WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)
  | None ->
    lemma_client_hello_body_bytes_reveal ch;
    lemma_client_hello_extensions_len B.empty ch.M.key_share;
    let low : GCH.clientHello =
      { GCH.legacy_version = GPV.TLS_1p2;
        GCH.random = ch.M.random;
        GCH.legacy_session_id = B.empty;
        GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
        GCH.legacy_compression_methods = B.of_list [0uy];
        GCH.extensions = PBL.mk_ext_list_none ch.M.key_share } in
    PBL.lemma_lp_ch_low_bytes_none ch;
    Seq.lemma_eq_elim
      (LP.serialize GCH.clientHello_serializer low)
      (client_hello_body_bytes ch.M.random B.empty ch.M.key_share);
    Seq.lemma_eq_elim
      (WS.serialize_client_hello ch)
      (client_hello_body_bytes ch.M.random B.empty ch.M.key_share);
    LP.parse_serialize GCH.clientHello_serializer low;
    assert_norm (WS.synth_client_hello low == Some ch);
    assert (WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)
#pop-options
