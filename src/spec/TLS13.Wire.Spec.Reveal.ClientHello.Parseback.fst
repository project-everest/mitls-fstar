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
friend TLS13.Wire.Generated.Handshake_body_client_hello
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = FStar.Endianness
module ML = FStar.Math.Lemmas
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal
module LP = LowParse.Spec
module RCH = TLS13.Wire.Spec.Reveal.ClientHello
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCS = TLS13.Wire.Generated.CipherSuite
module GCH = TLS13.Wire.Generated.ClientHello
module GHS = TLS13.Wire.Generated.Handshake
module HT = TLS13.Wire.Generated.HandshakeType
module PBL = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Low
module PBU = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util

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

#push-options "--split_queries always --fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_bounded_int_3_u24 (n:nat{n < 16777216})
  : Lemma (Seq.equal
      (LP.serialize (LP.serialize_bounded_integer 3) (U32.uint_to_t n))
      (WSR.u24 n))
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  assert (U32.fits n);
  let b0 = WSR.byte (n / 65536) in
  let b1 = WSR.byte (n / 256) in
  let b2 = WSR.byte n in
  WSR.lemma_byte_value (n / 65536);
  WSR.lemma_byte_value (n / 256);
  WSR.lemma_byte_value n;
  ML.lemma_div_lt n 24 16;
  assert (n / 65536 < 256);
  ML.small_mod (n / 65536) 256;
  assert (U8.v b0 == n / 65536);
  assert (U8.v b1 == (n / 256) % 256);
  assert (U8.v b2 == n % 256);
  let cand : Seq.seq U8.t = B.of_list [b0; b1; b2] in
  Seq.lemma_seq_of_list_induction [b0; b1; b2];
  SeqP.lemma_seq_of_list_index [b0; b1; b2] 0;
  SeqP.lemma_seq_of_list_index [b0; b1; b2] 1;
  SeqP.lemma_seq_of_list_index [b0; b1; b2] 2;
  assert_norm (FStar.List.Tot.index [b0; b1; b2] 0 == b0);
  assert_norm (FStar.List.Tot.index [b0; b1; b2] 1 == b1);
  assert_norm (FStar.List.Tot.index [b0; b1; b2] 2 == b2);
  assert (Seq.length cand == 3);
  assert (Seq.index cand 0 == b0);
  assert (Seq.index cand 1 == b1);
  assert (Seq.index cand 2 == b2);
  let prefix2 = B.of_list [b0; b1] in
  Seq.lemma_len_slice cand 0 2;
  Seq.lemma_eq_intro (Seq.slice cand 0 2) prefix2;
  Seq.lemma_eq_elim (Seq.slice cand 0 2) prefix2;
  Seq.lemma_seq_of_list_induction [b0; b1];
  SeqP.lemma_seq_of_list_index [b0; b1] 0;
  SeqP.lemma_seq_of_list_index [b0; b1] 1;
  assert_norm (FStar.List.Tot.index [b0; b1] 0 == b0);
  assert_norm (FStar.List.Tot.index [b0; b1] 1 == b1);
  assert (Seq.length prefix2 == 2);
  assert (Seq.index prefix2 0 == b0);
  assert (Seq.index prefix2 1 == b1);
  let prefix1 = B.of_list [b0] in
  Seq.lemma_len_slice prefix2 0 1;
  Seq.lemma_eq_intro (Seq.slice prefix2 0 1) prefix1;
  Seq.lemma_eq_elim (Seq.slice prefix2 0 1) prefix1;
  Seq.lemma_seq_of_list_induction [b0];
  SeqP.lemma_seq_of_list_index [b0] 0;
  assert_norm (FStar.List.Tot.index [b0] 0 == b0);
  assert (Seq.length prefix1 == 1);
  assert (Seq.index prefix1 0 == b0);
  Seq.lemma_len_slice prefix1 0 0;
  Seq.lemma_eq_intro (Seq.slice prefix1 0 0) B.empty;
  Seq.lemma_eq_elim (Seq.slice prefix1 0 0) B.empty;
  assert (Seq.last prefix1 == b0);
  assert (Seq.last prefix2 == b1);
  assert (Seq.last cand == b2);
  E.reveal_be_to_n cand;
  E.reveal_be_to_n prefix2;
  E.reveal_be_to_n prefix1;
  E.reveal_be_to_n B.empty;
  assert (E.be_to_n prefix1 == U8.v b0);
  assert (E.be_to_n prefix2 == U8.v b1 + 256 * U8.v b0);
  assert (E.be_to_n cand == U8.v b2 + 256 * E.be_to_n prefix2);
  ML.lemma_div_mod n 256;
  ML.lemma_div_mod (n / 256) 256;
  ML.division_multiplication_lemma n 256 256;
  assert (256 * 256 == 65536);
  assert ((n / 256) / 256 == n / 65536);
  assert (n / 256 == 256 * (n / 65536) + (n / 256) % 256);
  assert (n == 256 * (n / 256) + n % 256);
  assert (n == 256 * (256 * (n / 65536) + (n / 256) % 256) + n % 256);
  assert (E.be_to_n cand ==
    n % 256 + 256 * ((n / 256) % 256 + 256 * (n / 65536)));
  assert (n % 256 + 256 * ((n / 256) % 256 + 256 * (n / 65536)) ==
    256 * (256 * (n / 65536) + (n / 256) % 256) + n % 256);
  assert (E.be_to_n cand ==
    256 * (256 * (n / 65536) + (n / 256) % 256) + n % 256);
  assert (E.be_to_n cand == n);
  E.n_to_be_be_to_n 3 cand;
  LP.serialize_bounded_integer_spec 3 (U32.uint_to_t n);
  WSR.lemma_u24_reveal n;
  Seq.lemma_eq_elim (E.n_to_be 3 n) cand;
  Seq.lemma_eq_elim (WSR.u24 n) cand
#pop-options

#push-options "--split_queries always --fuel 8 --ifuel 2 --z3rlimit 80"
let lemma_parse_client_hello_serialize_client_hello
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

#push-options "--split_queries always --fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_ghs_serialize_client_hello_shape
  (low:GCH.clientHello)
  : Lemma
      (requires B.length (LP.serialize GCH.clientHello_serializer low) < 16777216)
      (ensures Seq.equal
        (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
        (B.append
          (B.of_list [1uy])
          (B.append
            (WSR.u24 (B.length (LP.serialize GCH.clientHello_serializer low)))
            (LP.serialize GCH.clientHello_serializer low))))
=
  let body = LP.serialize GCH.clientHello_serializer low in
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_client_hello low);
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Client_hello;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Client_hello == 1z);
  LP.serialize_u8_spec 1z;
  assert_norm (GHS.serialize_handshake_cases HT.Client_hello == GHS.handshake_body_client_hello_serializer);
  assert_norm (GHS.handshake_body_client_hello_serializer ==
               LP.serialize_bounded_vldata 0 16777215 GCH.clientHello_serializer);
  PBU.lemma_vldata_unfold_raw 0 16777215 GCH.clientHello_serializer low;
  assert_norm (LP.log256' 16777215 == 3);
  LP.serialize_length GCH.clientHello_serializer low;
  assert_norm (GCH.clientHello_parser_kind.LP.parser_kind_high == Some 131396);
  assert (B.length body <= 131396);
  assert (B.length body <= 16777215);
  assert_norm (pow2 32 == 4294967296);
  assert (U32.fits (B.length body));
  lemma_bounded_int_3_u24 (B.length body);
  Seq.lemma_seq_of_list_induction [1uy];
  let tag =
    LP.serialize
      (LP.serialize_enum_key HT.handshakeType_repr_parser HT.handshakeType_repr_serializer HT.handshakeType_enum)
      HT.Client_hello in
  let blen : n:nat{n < pow2 (8 * 3) /\ U32.fits n} = B.length body in
  let len0 : U32.t = U32.uint_to_t blen in
  U32.vu_inv blen;
  assert (U32.v len0 == blen);
  LP.bounded_integer_prop_equiv 3 len0;
  assert (LP.bounded_integer_prop 3 len0);
  let len : LP.bounded_integer 3 = len0 in
  let lenb =
    LP.serialize (LP.serialize_bounded_integer 3) len in
  assert (Seq.equal tag (B.of_list [1uy]));
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
    (B.append tag (B.append lenb body)));
  assert (Seq.equal lenb (WSR.u24 (B.length body)));
  Seq.lemma_eq_elim lenb (WSR.u24 (B.length body));
  assert (Seq.equal (B.append tag (B.append lenb body))
                    (B.append (B.of_list [1uy]) (B.append (WSR.u24 (B.length body)) body)));
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
    (B.append (B.of_list [1uy]) (B.append (WSR.u24 (B.length body)) body)))

let lemma_ghs_serialize_client_hello_eq_ws
  (low:GCH.clientHello)
  (ch:M.client_hello{B.length ch.M.random == 32 /\
                     B.length ch.M.key_share == 32 /\
                     B.length ch.M.body == 0 /\
                     (match ch.M.server_name with
                      | Some h -> B.length h <= 255
                      | None -> True)})
  : Lemma
      (requires
        Seq.equal (LP.serialize GCH.clientHello_serializer low)
                  (WS.serialize_client_hello ch))
      (ensures
        Seq.equal
          (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
          (WS.serialize_handshake (M.ClientHello ch)))
=
  let body = LP.serialize GCH.clientHello_serializer low in
  LP.serialize_length GCH.clientHello_serializer low;
  assert_norm (GCH.clientHello_parser_kind.LP.parser_kind_high == Some 131396);
  assert (B.length body <= 131396);
  assert (B.length body < 16777216);
  lemma_ghs_serialize_client_hello_shape low;
  Seq.lemma_eq_elim body (WS.serialize_client_hello ch);
  assert (B.length (WS.serialize_client_hello ch) < 16777216);
  lemma_bounded_int_3_u24 (B.length (WS.serialize_client_hello ch));
  WSR.lemma_serialize_client_hello_reveal ch;
  let rhs =
    B.append
      (B.of_list [1uy])
      (B.append
        (WSR.u24 (B.length (WS.serialize_client_hello ch)))
        (WS.serialize_client_hello ch)) in
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
    rhs);
  lemma_seq_equal_sym (WS.serialize_handshake (M.ClientHello ch)) rhs;
  lemma_seq_equal_trans
    (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low))
    rhs
    (WS.serialize_handshake (M.ClientHello ch))

let lemma_parse_tls_message_serialize_client_hello
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
=
  match ch.M.server_name with
  | Some hostname ->
    lemma_serialize_client_hello_body_eq ch;
    let low : l:GCH.clientHello{l == PBL.mk_ch_low_some ch hostname} =
      PBL.mk_ch_low_some ch hostname in
    PBL.lemma_lp_ch_low_body_some ch hostname;
    PBL.lemma_lp_ch_low_synth_some ch hostname;
    assert (Seq.equal (LP.serialize GCH.clientHello_serializer low)
                      (WS.serialize_client_hello ch));
    lemma_ghs_serialize_client_hello_eq_ws low ch;
    let gen = LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low) in
    let wire = WS.serialize_handshake (M.ClientHello ch) in
    GHS.handshake_bytesize_eq (GHS.Body_client_hello low);
    assert (B.length gen <= M.client_hello_max_len);
    LP.parse_serialize GHS.handshake_serializer (GHS.Body_client_hello low);
    Seq.lemma_eq_elim gen wire;
    assert (B.length wire <= M.client_hello_max_len);
    let parsed = { ch with M.body = wire } in
    WSR.lemma_handshake_synth_client_hello low;
    assert (WSR.handshake_synth (GHS.Body_client_hello low) == Some (M.ClientHello parsed));
    WSR.lemma_ptm_handshake_some wire (GHS.Body_client_hello low) (M.ClientHello parsed);
    introduce exists (parsed_ch:M.client_hello).
      WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.ClientHello ch)) ==
        Some (M.TlsHandshake (M.ClientHello parsed_ch)) /\
      Seq.equal ch.M.random parsed_ch.M.random /\
      ch.M.server_name == parsed_ch.M.server_name /\
      Seq.equal ch.M.key_share parsed_ch.M.key_share /\
      ch.M.cipher_suites == parsed_ch.M.cipher_suites /\
      ch.M.signature_schemes == parsed_ch.M.signature_schemes /\
      parsed_ch.M.body == WS.serialize_handshake (M.ClientHello ch)
    with parsed
    and (Seq.lemma_eq_refl ch.M.random parsed.M.random;
         Seq.lemma_eq_refl ch.M.key_share parsed.M.key_share)
  | None ->
    lemma_serialize_client_hello_body_eq ch;
    let low : l:GCH.clientHello{l == PBL.mk_ch_low_none ch} =
      PBL.mk_ch_low_none ch in
    PBL.lemma_lp_ch_low_body_none ch;
    PBL.lemma_lp_ch_low_synth_none ch;
    assert (Seq.equal (LP.serialize GCH.clientHello_serializer low)
                      (WS.serialize_client_hello ch));
    lemma_ghs_serialize_client_hello_eq_ws low ch;
    let gen = LP.serialize GHS.handshake_serializer (GHS.Body_client_hello low) in
    let wire = WS.serialize_handshake (M.ClientHello ch) in
    GHS.handshake_bytesize_eq (GHS.Body_client_hello low);
    assert (B.length gen <= M.client_hello_max_len);
    LP.parse_serialize GHS.handshake_serializer (GHS.Body_client_hello low);
    Seq.lemma_eq_elim gen wire;
    assert (B.length wire <= M.client_hello_max_len);
    let parsed = { ch with M.body = wire } in
    WSR.lemma_handshake_synth_client_hello low;
    assert (WSR.handshake_synth (GHS.Body_client_hello low) == Some (M.ClientHello parsed));
    WSR.lemma_ptm_handshake_some wire (GHS.Body_client_hello low) (M.ClientHello parsed);
    introduce exists (parsed_ch:M.client_hello).
      WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.ClientHello ch)) ==
        Some (M.TlsHandshake (M.ClientHello parsed_ch)) /\
      Seq.equal ch.M.random parsed_ch.M.random /\
      ch.M.server_name == parsed_ch.M.server_name /\
      Seq.equal ch.M.key_share parsed_ch.M.key_share /\
      ch.M.cipher_suites == parsed_ch.M.cipher_suites /\
      ch.M.signature_schemes == parsed_ch.M.signature_schemes /\
      parsed_ch.M.body == WS.serialize_handshake (M.ClientHello ch)
    with parsed
    and (Seq.lemma_eq_refl ch.M.random parsed.M.random;
         Seq.lemma_eq_refl ch.M.key_share parsed.M.key_share)
#pop-options
