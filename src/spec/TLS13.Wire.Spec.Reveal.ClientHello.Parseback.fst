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

let lemma_seq_equal_sym (#a:Type) (x y:Seq.seq a)
  : Lemma
      (requires Seq.equal x y)
      (ensures Seq.equal y x)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_refl y x

let lemma_seq_equal_trans (#a:Type) (x y z:Seq.seq a)
  : Lemma
      (requires Seq.equal x y /\ Seq.equal y z)
      (ensures Seq.equal x z)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_elim y z;
  Seq.lemma_eq_refl x z

let lemma_parse_client_hello_seq_equal (x y:B.bytes)
  : Lemma
      (requires Seq.equal x y)
      (ensures WS.parse_client_hello x == WS.parse_client_hello y)
=
  Seq.lemma_eq_elim x y

let lemma_parse_client_hello_from_generated
  (ser:B.bytes)
  (low:GCH.clientHello)
  (ch:M.client_hello)
  : Lemma
      (requires
        LP.parse GCH.clientHello_parser ser == Some (low, Seq.length ser) /\
        WS.synth_client_hello low == Some ch)
      (ensures WS.parse_client_hello ser == Some ch)
=
  assert (B.length ser == Seq.length ser);
  assert (LP.parse GCH.clientHello_parser ser == Some (low, B.length ser));
  assert (WS.parse_client_hello ser == WS.synth_client_hello low);
  assert (WS.parse_client_hello ser == Some ch)

let lemma_parse_client_hello_transport_some
  (input ser:B.bytes)
  (ch:M.client_hello)
  : Lemma
      (requires Seq.equal input ser /\ WS.parse_client_hello ser == Some ch)
      (ensures WS.parse_client_hello input == Some ch)
=
  Seq.lemma_eq_elim input ser

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let lemma_serialize_client_hello_body_eq
  (ch:M.client_hello{B.length ch.M.random == 32 /\
                     B.length ch.M.key_share == 32 /\
                     (match ch.M.server_name with
                      | Some h -> B.length h <= 255
                      | None -> True)})
  : Lemma
      (WS.serialize_client_hello ch ==
       RCH.client_hello_body_bytes
         ch.M.random
         (match ch.M.server_name with
          | Some h -> h
          | None -> B.empty)
         ch.M.key_share)
=
  RCH.lemma_client_hello_body_bytes_reveal ch;
  Seq.lemma_eq_elim
    (WS.serialize_client_hello ch)
    (RCH.client_hello_body_bytes
      ch.M.random
      (match ch.M.server_name with
       | Some h -> h
       | None -> B.empty)
      ch.M.key_share)
#pop-options

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
    assert (ch.M.server_name == Some hostname);
    assert ((match ch.M.server_name with | Some h -> h | None -> B.empty) == hostname);
    lemma_serialize_client_hello_body_eq ch;
    lemma_client_hello_extensions_len hostname ch.M.key_share;
    let low : l:GCH.clientHello{l == PBL.mk_ch_low_some ch hostname} =
      PBL.mk_ch_low_some ch hostname in
    let body = RCH.client_hello_body_bytes
      ch.M.random
      (match ch.M.server_name with | Some h -> h | None -> B.empty)
      ch.M.key_share in
    PBL.lemma_lp_ch_low_body_some ch hostname;
    PBL.lemma_lp_ch_low_synth_some ch hostname;
    let ser = LP.serialize GCH.clientHello_serializer low in
    assert_spinoff (Seq.equal ser body);
    LP.parse_serialize GCH.clientHello_serializer low;
    assert (LP.parse GCH.clientHello_parser ser == Some (low, Seq.length ser));
    assert (WS.synth_client_hello low == Some ch);
    lemma_parse_client_hello_from_generated ser low ch;
    lemma_seq_equal_sym ser body;
    lemma_parse_client_hello_transport_some body ser ch;
    assert (WS.serialize_client_hello ch == body);
    assert (WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)
  | None ->
    assert (ch.M.server_name == None);
    assert ((match ch.M.server_name with | Some h -> h | None -> B.empty) == B.empty);
    lemma_serialize_client_hello_body_eq ch;
    lemma_client_hello_extensions_len B.empty ch.M.key_share;
    let low : l:GCH.clientHello{l == PBL.mk_ch_low_none ch} =
      PBL.mk_ch_low_none ch in
    let body = RCH.client_hello_body_bytes
      ch.M.random
      (match ch.M.server_name with | Some h -> h | None -> B.empty)
      ch.M.key_share in
    PBL.lemma_lp_ch_low_body_none ch;
    PBL.lemma_lp_ch_low_synth_none ch;
    let ser = LP.serialize GCH.clientHello_serializer low in
    assert_spinoff (Seq.equal ser body);
    LP.parse_serialize GCH.clientHello_serializer low;
    assert (LP.parse GCH.clientHello_parser ser == Some (low, Seq.length ser));
    assert (WS.synth_client_hello low == Some ch);
    lemma_parse_client_hello_from_generated ser low ch;
    lemma_seq_equal_sym ser body;
    lemma_parse_client_hello_transport_some body ser ch;
    assert (WS.serialize_client_hello ch == body);
    assert (WS.parse_client_hello (WS.serialize_client_hello ch) == Some ch)
#pop-options
