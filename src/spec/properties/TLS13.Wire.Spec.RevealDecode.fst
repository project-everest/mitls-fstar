module TLS13.Wire.Spec.RevealDecode

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module WRU = TLS13.Wire.Spec.Reveal.Util
module GCCS = TLS13.Wire.Generated.ChangeCipherSpec
module GCTX = TLS13.Wire.Generated.TLSCiphertext
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GHS = TLS13.Wire.Generated.Handshake
module LP = LowParse.Spec

(* [RevealDecode] friends [TLS13.Wire.Spec], so it can unfold [parse_record_wire]
   here.  When [parse_record] fails but [parse_record_wire] succeeds, the wire
   result must come from the Handshake fallback arm (first byte 0x16, legacy
   version 0x0301), so the parsed content type is [T.Handshake].  This local
   reveal packages that fact so the (borderline) case analysis in
   [lemma_parse_record_wire_from_prefix] stays within default resource limits
   once the generated [Invalid] content type widens the byte-0 codec. *)
let lemma_parse_record_wire_fallback (input:B.bytes)
  : Lemma
    (requires WS.parse_record input == None /\ Some? (WS.parse_record_wire input))
    (ensures (
      B.length input >= 5 /\
      Seq.index input 0 == 0x16uy /\
      WS.read_u16 input 1 == 0x0301 /\
      (let flen = WS.read_u16 input 3 in
       flen <= 16640 /\ 5 + flen <= B.length input /\
       WS.parse_record_wire input ==
         Some (T.Handshake, Seq.slice input 5 (5 + flen), 5 + flen))))
= ()

let lemma_parse_record_from_header_as
  (raw:B.bytes)
  (content_type:T.content_type)
  (flen:nat)
  : Lemma
    (requires
      flen <= 16640 /\
      5 + flen <= B.length raw /\
      Seq.index raw 0 == WRU.content_type_byte content_type /\
      Seq.index raw 1 == 0x03uy /\
      Seq.index raw 2 == 0x03uy /\
      U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) == flen)
    (ensures
      WS.parse_record raw ==
        Some
          (content_type,
           Seq.slice raw 5 (5 + flen),
           5 + flen))
=
  let fragment = Seq.slice raw 5 (5 + flen) in
  let prefix = Seq.slice raw 0 (5 + flen) in
  Seq.lemma_len_slice raw 5 (5 + flen);
  Seq.lemma_len_slice raw 0 (5 + flen);
  assert (B.length fragment == flen);
  assert (B.length prefix == 5 + flen);
  WRU.lemma_serialize_record_prefix_from_header
    raw content_type flen;
  WS.lemma_parse_record_serialize_record content_type fragment;
  Seq.lemma_eq_elim
    (WS.serialize_record content_type fragment)
    prefix;
  assert (WS.parse_record prefix ==
    Some (content_type, fragment, 5 + flen));
  match LP.parse GCTX.tLSCiphertext_parser prefix with
  | Some (record, consumed) ->
    assert (record.GCTX.legacy_record_version == GPV.TLS_1p2);
    assert (record.GCTX.opaque_type == content_type);
    assert ((record.GCTX.encrypted_record <: B.bytes) == fragment);
    assert (consumed == 5 + flen);
    SeqP.slice_slice raw 0 (5 + flen) 0 (5 + flen);
    LP.parse_strong_prefix GCTX.tLSCiphertext_parser prefix raw;
    WS.lemma_parse_record_generated raw record consumed
  | None ->
    assert False

let lemma_parse_record_from_header raw =
  let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
  assert (WS.read_u16 raw 1 == 0x0303);
  assert (WS.read_u16 raw 3 == flen);
  let b0 = U8.v (Seq.index raw 0) in
  if b0 == 0x00 then (
    WRU.lemma_content_type_byte_value T.Invalid;
    U8.v_inj (Seq.index raw 0) (WRU.content_type_byte T.Invalid);
    lemma_parse_record_from_header_as raw T.Invalid flen
  ) else if b0 == 0x14 then (
    WRU.lemma_content_type_byte_value T.Change_cipher_spec;
    U8.v_inj
      (Seq.index raw 0)
      (WRU.content_type_byte T.Change_cipher_spec);
    lemma_parse_record_from_header_as raw T.Change_cipher_spec flen
  ) else if b0 == 0x15 then (
    WRU.lemma_content_type_byte_value T.Alert;
    U8.v_inj (Seq.index raw 0) (WRU.content_type_byte T.Alert);
    lemma_parse_record_from_header_as raw T.Alert flen
  ) else if b0 == 0x16 then (
    WRU.lemma_content_type_byte_value T.Handshake;
    U8.v_inj (Seq.index raw 0) (WRU.content_type_byte T.Handshake);
    lemma_parse_record_from_header_as raw T.Handshake flen
  ) else (
    assert (b0 == 0x17);
    WRU.lemma_content_type_byte_value T.Application_data;
    U8.v_inj
      (Seq.index raw 0)
      (WRU.content_type_byte T.Application_data);
    lemma_parse_record_from_header_as raw T.Application_data flen
  )

let lemma_parse_record_none_legacy_version (raw:B.bytes)
  : Lemma
    (requires
      B.length raw >= 5 /\
      Seq.index raw 1 == 0x03uy /\
      Seq.index raw 2 == 0x01uy)
    (ensures WS.parse_record raw == None)
=
  match WS.parse_record raw with
  | Some (content_type, fragment, consumed) ->
    WS.lemma_parse_record_fragment_bound raw;
    WS.lemma_parse_record_serializes raw;
    WRU.lemma_serialize_record_legacy_version content_type fragment;
    assert (consumed ==
      B.length (WS.serialize_record content_type fragment));
    assert (consumed >= 3);
    Seq.lemma_index_slice raw 0 consumed 2;
    assert False
  | None ->
    ()

let lemma_parse_record_from_prefix_strong
  (input:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  (consumed:nat)
  : Lemma
    (requires
      consumed <= B.length input /\
      WS.parse_record (Seq.slice input 0 consumed) ==
        Some (content_type, fragment, consumed))
    (ensures
      WS.parse_record input ==
        Some (content_type, fragment, consumed))
=
  let prefix = Seq.slice input 0 consumed in
  Seq.lemma_len_slice input 0 consumed;
  match LP.parse GCTX.tLSCiphertext_parser prefix with
  | Some (record, parsed_consumed) ->
    assert (record.GCTX.legacy_record_version == GPV.TLS_1p2);
    assert (record.GCTX.opaque_type == content_type);
    assert ((record.GCTX.encrypted_record <: B.bytes) == fragment);
    assert (parsed_consumed == consumed);
    SeqP.slice_slice input 0 consumed 0 consumed;
    LP.parse_strong_prefix GCTX.tLSCiphertext_parser prefix input;
    WS.lemma_parse_record_generated input record parsed_consumed
  | None ->
    assert False

let lemma_parse_record_wire_from_header raw =
  let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
  assert (WS.read_u16 raw 3 == flen);
  assert (WS.content_type_of_byte (Seq.index raw 0) ==
    (match U8.v (Seq.index raw 0) with
     | 0x14 -> Some T.Change_cipher_spec
     | 0x15 -> Some T.Alert
     | 0x16 -> Some T.Handshake
     | 0x17 -> Some T.Application_data
     | _ -> None));
  if U8.v (Seq.index raw 2) == 0x03 then (
    assert (WS.read_u16 raw 1 == 0x0303);
    lemma_parse_record_from_header raw;
    WS.lemma_parse_record_implies_parse_record_wire raw
  ) else (
    assert (U8.v (Seq.index raw 0) == 0x16);
    assert (U8.v (Seq.index raw 2) == 0x01);
    assert (WS.read_u16 raw 1 == 0x0301);
    assert (Seq.index raw 1 == 0x03uy);
    assert (Seq.index raw 2 == 0x01uy);
    lemma_parse_record_none_legacy_version raw;
    assert (Seq.equal (Seq.slice raw 5 (5 + flen)) (Seq.slice raw 5 (5 + flen)))
  )

let lemma_parse_record_wire_none_short raw =
  match WS.parse_record_wire raw with
  | Some (content_type, fragment, consumed) ->
    WS.lemma_parse_record_wire_some_consumed_positive
      raw content_type fragment consumed;
    assert False
  | None ->
    ()

let lemma_parse_record_wire_none_incomplete raw =
  let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
  assert (WS.read_u16 raw 3 == flen);
  (match WS.parse_record raw with
   | Some (content_type, fragment, consumed) ->
     WS.lemma_parse_record_fragment_bound raw;
     WS.lemma_parse_record_serializes raw;
     WS.lemma_parse_record_serialize_record content_type fragment;
     WRU.lemma_serialize_record_fragment_length content_type fragment;
     assert (consumed ==
       B.length (WS.serialize_record content_type fragment));
     assert (consumed == 5 + B.length fragment);
     assert (consumed >= 5);
     Seq.lemma_index_slice raw 0 consumed 3;
     Seq.lemma_index_slice raw 0 consumed 4;
     WS.lemma_read_u16_definition
       (WS.serialize_record content_type fragment)
       3;
     assert (B.length fragment == flen);
     assert False
   | None ->
     ());
  assert (WS.parse_record raw == None);
  assert (WS.parse_record_wire raw == None)

let lemma_parse_record_wire_prefix input content_type fragment consumed =
  WS.lemma_parse_record_wire_some_consumed_positive
    input
    content_type
    fragment
    consumed;
  let prefix = Seq.slice input 0 consumed in
  Seq.lemma_len_slice input 0 consumed;
  assert (B.length prefix == consumed);
  match WS.parse_record input with
  | Some (ct, frag, consumed') ->
    assert (content_type == ct);
    assert (fragment == frag);
    assert (consumed == consumed');
    WS.lemma_parse_record_serializes input;
    WS.lemma_parse_record_fragment_bound input;
    assert (B.length fragment <= 16640);
    assert (Seq.equal (WS.serialize_record content_type fragment) prefix);
    WS.lemma_parse_record_serialize_record content_type fragment;
    Seq.lemma_eq_elim prefix (WS.serialize_record content_type fragment);
    WS.lemma_parse_record_implies_parse_record_wire prefix;
    assert (WS.parse_record_wire prefix ==
     Some (content_type, fragment, B.length prefix))
  | None ->
    let flen = U8.v (Seq.index input 3) * 256 + U8.v (Seq.index input 4) in
    assert (B.length input >= 5);
    assert (Seq.index input 0 == 0x16uy);
    assert (WS.read_u16 input 1 == 0x0301);
    assert (flen <= 16640);
    assert (5 + flen <= B.length input);
    assert (consumed == 5 + flen);
    Seq.lemma_index_slice input 0 consumed 0;
    Seq.lemma_index_slice input 0 consumed 1;
    Seq.lemma_index_slice input 0 consumed 2;
    Seq.lemma_index_slice input 0 consumed 3;
    Seq.lemma_index_slice input 0 consumed 4;
    assert (B.length prefix >= 5);
    assert (U8.v (Seq.index prefix 0) == 0x16);
    assert (U8.v (Seq.index prefix 1) == 0x03);
    assert (U8.v (Seq.index prefix 2) == 0x01);
    assert (U8.v (Seq.index prefix 3) * 256 + U8.v (Seq.index prefix 4) == flen);
    lemma_parse_record_wire_from_header prefix;
    assert (content_type == T.Handshake);
    assert (Seq.equal fragment (Seq.slice input 5 (5 + flen)));
    SeqP.slice_slice input 0 consumed 5 (5 + flen);
    assert (Seq.equal (Seq.slice prefix 5 (5 + flen)) fragment);
    assert (WS.parse_record_wire prefix ==
     Some (content_type, fragment, consumed))

let lemma_parse_record_wire_from_prefix input content_type fragment consumed =
  let prefix = Seq.slice input 0 consumed in
  WS.lemma_parse_record_wire_some_consumed_positive
    prefix
    content_type
    fragment
    consumed;
  Seq.lemma_len_slice input 0 consumed;
  assert (B.length prefix == consumed);
  assert (consumed > 0);
  assert (B.length input >= 5);
  match WS.parse_record_wire prefix with
  | Some (ct, frag, consumed') ->
    assert (ct == content_type);
    assert (frag == fragment);
    assert (consumed' == consumed);
    if Some? (WS.parse_record prefix) then (
     match WS.parse_record prefix with
     | Some (pct, pfrag, pconsumed) ->
       assert (pct == content_type);
       assert (pfrag == fragment);
       assert (pconsumed == consumed);
       lemma_parse_record_from_prefix_strong
         input content_type fragment consumed;
       assert (WS.parse_record input == Some (content_type, fragment, consumed));
       WS.lemma_parse_record_implies_parse_record_wire input
     | None -> assert False
    ) else (
     lemma_parse_record_wire_fallback prefix;
     let flen = U8.v (Seq.index prefix 3) * 256 + U8.v (Seq.index prefix 4) in
     assert (Seq.index prefix 0 == 0x16uy);
     assert (WS.read_u16 prefix 1 == 0x0301);
     assert (flen <= 16640);
     assert (consumed == 5 + flen);
     Seq.lemma_index_slice input 0 consumed 0;
     Seq.lemma_index_slice input 0 consumed 1;
     Seq.lemma_index_slice input 0 consumed 2;
     Seq.lemma_index_slice input 0 consumed 3;
     Seq.lemma_index_slice input 0 consumed 4;
     assert (U8.v (Seq.index input 0) == 0x16);
     assert (U8.v (Seq.index input 1) == 0x03);
     assert (U8.v (Seq.index input 2) == 0x01);
     assert (U8.v (Seq.index input 3) * 256 + U8.v (Seq.index input 4) == flen);
     lemma_parse_record_wire_from_header input;
     assert (Seq.equal fragment (Seq.slice prefix 5 (5 + flen)));
     SeqP.slice_slice input 0 consumed 5 (5 + flen);
     assert (Seq.equal (Seq.slice input 5 (5 + flen)) fragment);
     assert (WS.parse_record_wire input ==
       Some (content_type, fragment, consumed))
    )
  | None ->
    assert False

let lemma_parse_record_wire_serialized_length input content_type fragment consumed =
  WS.lemma_parse_record_wire_some_consumed_positive
    input
    content_type
    fragment
    consumed;
  match WS.parse_record input with
  | Some (ct, frag, consumed') ->
    assert (content_type == ct);
    assert (fragment == frag);
    assert (consumed == consumed');
    WS.lemma_parse_record_serializes input;
    assert (consumed == B.length (WS.serialize_record content_type fragment))
  | None ->
    if B.length input < 5 then ()
    else if Seq.index input 0 <> 0x16uy || WS.read_u16 input 1 <> 0x0301 then ()
    else
      let fragment_len = WS.read_u16 input 3 in
      if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
      else
        match WS.take_range input 5 fragment_len with
        | Some parsed_fragment ->
          assert (content_type == T.Handshake);
          assert (fragment == parsed_fragment);
          assert (consumed == 5 + fragment_len);
          assert (B.length fragment == fragment_len);
          WS.lemma_parse_record_serialize_record T.Handshake fragment;
          assert (consumed == B.length (WS.serialize_record content_type fragment))
        | None -> ()

let lemma_parse_plaintext_some input =
  let cpos = B.length input - 1 in
  assert (WS.content_type_of_byte (Seq.index input cpos) ==
    (match U8.v (Seq.index input cpos) with
     | 0x14 -> Some T.Change_cipher_spec
     | 0x15 -> Some T.Alert
     | 0x16 -> Some T.Handshake
     | 0x17 -> Some T.Application_data
     | _ -> None));
  ()

let lemma_serialize_tls_message_handshake hs = ()

let lemma_serialize_tls_message_change_cipher_spec () = ()

let lemma_parse_tls_message_change_cipher_spec fragment =
  match LP.parse GCCS.changeCipherSpec_parser fragment with
  | Some (value, consumed) ->
    assert (value == 1uy);
    assert (consumed == B.length fragment);
    LP.parsed_data_is_serialize
      GCCS.changeCipherSpec_serializer
      fragment;
    assert (Seq.equal
      (LP.serialize GCCS.changeCipherSpec_serializer 1uy)
      (Seq.slice fragment 0 consumed));
    Seq.lemma_eq_elim fragment (Seq.slice fragment 0 consumed);
    assert (Seq.equal
      fragment
      (snd (WS.serialize_tls_message M.TlsChangeCipherSpec)))
  | None ->
    assert False
