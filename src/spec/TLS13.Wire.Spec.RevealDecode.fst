module TLS13.Wire.Spec.RevealDecode

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module LP = LowParse.Spec

let lemma_parse_record_from_header raw =
  let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
  assert (WS.read_u16 raw 1 == 0x0303);
  assert (WS.read_u16 raw 3 == flen);
  assert (WS.content_type_of_byte (Seq.index raw 0) ==
    (match U8.v (Seq.index raw 0) with
     | 0x00 -> Some T.Invalid
     | 0x14 -> Some T.Change_cipher_spec
     | 0x15 -> Some T.Alert
     | 0x16 -> Some T.Handshake
     | 0x17 -> Some T.Application_data
     | _ -> None));
  ()

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
    assert (WS.parse_record raw == None);
    assert (Seq.equal (Seq.slice raw 5 (5 + flen)) (Seq.slice raw 5 (5 + flen)))
  )

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
       WS.lemma_parse_record_serializes prefix;
       assert (Seq.equal
         (WS.serialize_record content_type fragment)
         (Seq.slice prefix 0 consumed));
       Seq.lemma_eq_elim prefix (Seq.slice prefix 0 consumed);
       WS.lemma_parse_record_serialize_record content_type fragment;
       Seq.lemma_index_slice input 0 consumed 0;
       Seq.lemma_index_slice input 0 consumed 1;
       Seq.lemma_index_slice input 0 consumed 2;
       Seq.lemma_index_slice input 0 consumed 3;
       Seq.lemma_index_slice input 0 consumed 4;
       lemma_parse_record_from_header input;
       assert (WS.parse_record input == Some (content_type, fragment, consumed));
       WS.lemma_parse_record_implies_parse_record_wire input
     | None -> assert False
    ) else (
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
  assert (Seq.length fragment == 1);
  assert (WS.nat_of_byte (Seq.index fragment 0) == 1);
  assert (U8.v (Seq.index fragment 0) == 1);
  let ccs = B.singleton (WS.byte 1) in
  WS.lemma_byte_v 1;
  assert (U8.v (Seq.index ccs 0) == 1);
  Seq.lemma_eq_intro fragment ccs
