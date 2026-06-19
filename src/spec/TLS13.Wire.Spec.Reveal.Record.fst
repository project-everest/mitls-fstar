module TLS13.Wire.Spec.Reveal.Record

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U = TLS13.Wire.Spec.Reveal.Util
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let byte n = WS.byte n

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let lemma_ptm_change_cipher_spec fragment =
  if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
  then assert (WS.nat_of_byte (Seq.index fragment 0) == 1)
  else ()
#pop-options

let lemma_ptm_application_data fragment = ()

#push-options "--fuel 8 --ifuel 2 --z3rlimit 20"
let lemma_parse_plaintext_fragment_len input =
  match WS.parse_plaintext input with
  | Some pt ->
    assert (B.length input > 0);
    let j : (n:nat{n <= B.length input}) = B.length input - 1 in
    Seq.lemma_len_slice input 0 j
  | None -> ()
#pop-options

let u8 n = WS.u8 n
let u16 n = WS.u16 n
let u24 n = WS.u24 n

let content_type_byte ct = WS.byte (WS.content_type_to_byte ct)

let lemma_content_type_byte_value ct =
  match ct with
  | T.ChangeCipherSpec -> WS.lemma_byte_v 20
  | T.Alert -> WS.lemma_byte_v 21
  | T.Handshake -> WS.lemma_byte_v 22
  | T.ApplicationData -> WS.lemma_byte_v 23

let serialize_record_header content_type fragment_len =
  B.append
    (u8 (WS.content_type_to_byte content_type))
    (B.append (u16 0x0303) (u16 fragment_len))

#push-options "--fuel 8 --ifuel 2 --z3rlimit 40"
let lemma_serialize_record_reveal content_type fragment = ()
#pop-options

let lemma_serialize_application_data_header_reveal fragment_len =
  let fragment = Seq.create fragment_len 0uy in
  let header = serialize_record_header T.ApplicationData fragment_len in
  lemma_serialize_record_reveal T.ApplicationData fragment;
  Seq.lemma_eq_elim
    (WS.serialize_record T.ApplicationData fragment)
    (B.append header fragment);
  U.lemma_slice_append_left header fragment;
  U.lemma_content_type_application_data_byte ();
  assert_norm (B.length header == 5);
  Seq.lemma_len_append header fragment;
  Seq.lemma_eq_elim (Seq.slice (B.append header fragment) 0 5) header;
  assert (Seq.equal (CS.application_data_record_header fragment_len) header)

let lemma_serialize_handshake_record_header_reveal fragment_len =
  let ct = u8 (WS.content_type_to_byte T.Handshake) in
  let ver = u16 0x0303 in
  let lenb = u16 fragment_len in
  let ver_bytes = B.of_list [byte (0x0303 / 256); byte 0x0303] in
  let lenb_bytes = B.of_list [byte (fragment_len / 256); byte fragment_len] in
  let tail = B.append ver lenb in
  let header = serialize_record_header T.Handshake fragment_len in
  let target =
    B.of_list [
      0x16uy; 0x03uy; 0x03uy;
      byte (fragment_len / 256);
      byte fragment_len
    ] in
  U.lemma_content_type_handshake_byte ();
  U.lemma_byte_3 ();
  U.lemma_byte_0303_lo ();
  U.lemma_u8_reveal (WS.content_type_to_byte T.Handshake);
  Seq.lemma_eq_elim ct (B.singleton (content_type_byte T.Handshake));
  U.lemma_u16_reveal 0x0303;
  Seq.lemma_eq_elim ver ver_bytes;
  U.lemma_u16_reveal fragment_len;
  Seq.lemma_eq_elim lenb lenb_bytes;
  assert (header == B.append ct tail);
  assert (B.singleton (content_type_byte T.Handshake) == B.singleton 0x16uy);
  U.lemma_singleton_of_list 0x16uy;
  Seq.lemma_eq_elim (B.singleton 0x16uy) (B.of_list [0x16uy]);
  assert_norm (0x0303 / 256 == 3);
  assert (byte (0x0303 / 256) == 0x03uy);
  assert (byte 0x0303 == 0x03uy);
  assert (ver_bytes == B.of_list [0x03uy; 0x03uy]);
  Seq.lemma_eq_elim ver (B.of_list [0x03uy; 0x03uy]);
  U.lemma_of_list_append
    [0x03uy; 0x03uy]
    [byte (fragment_len / 256); byte fragment_len];
  Seq.lemma_eq_elim tail
    (B.of_list [0x03uy; 0x03uy; byte (fragment_len / 256); byte fragment_len]);
  U.lemma_of_list_append
    [0x16uy]
    [0x03uy; 0x03uy; byte (fragment_len / 256); byte fragment_len];
  Seq.lemma_eq_elim header target

let lemma_application_data_record_aad fragment =
  let header = serialize_record_header T.ApplicationData (B.length fragment) in
  lemma_serialize_record_reveal T.ApplicationData fragment;
  Seq.lemma_eq_elim
    (WS.serialize_record T.ApplicationData fragment)
    (B.append header fragment);
  U.lemma_slice_append_left header fragment;
  lemma_serialize_application_data_header_reveal (B.length fragment);
  Seq.lemma_eq_elim
    header
    (CS.application_data_record_header (B.length fragment))

let lemma_serialize_application_data_record_reveal fragment =
  let header = serialize_record_header T.ApplicationData (B.length fragment) in
  lemma_serialize_record_reveal T.ApplicationData fragment;
  lemma_serialize_application_data_header_reveal (B.length fragment);
  Seq.lemma_eq_elim
    header
    (CS.application_data_record_header (B.length fragment))

let lemma_application_data_record_header fragment_len =
  lemma_serialize_application_data_header_reveal fragment_len;
  Seq.lemma_eq_elim
    (serialize_record_header T.ApplicationData fragment_len)
    (CS.application_data_record_header fragment_len)

let application_data_record_header_bytes fragment_len =
  B.of_list [
    0x17uy;
    0x03uy;
    0x03uy;
    byte (fragment_len / 256);
    byte fragment_len
  ]

private let lemma_serialize_application_data_header_bytes fragment_len
  : Lemma (Seq.equal
      (serialize_record_header T.ApplicationData fragment_len)
      (application_data_record_header_bytes fragment_len))
=
  let ct = u8 (WS.content_type_to_byte T.ApplicationData) in
  let ver = u16 0x0303 in
  let lenb = u16 fragment_len in
  let ver_bytes = B.of_list [byte (0x0303 / 256); byte 0x0303] in
  let lenb_bytes = B.of_list [byte (fragment_len / 256); byte fragment_len] in
  let tail = B.append ver lenb in
  let header = serialize_record_header T.ApplicationData fragment_len in
  let target = application_data_record_header_bytes fragment_len in
  U.lemma_content_type_application_data_byte ();
  U.lemma_byte_3 ();
  U.lemma_byte_0303_lo ();
  U.lemma_u8_reveal (WS.content_type_to_byte T.ApplicationData);
  Seq.lemma_eq_elim ct (B.singleton (content_type_byte T.ApplicationData));
  U.lemma_u16_reveal 0x0303;
  Seq.lemma_eq_elim ver ver_bytes;
  U.lemma_u16_reveal fragment_len;
  Seq.lemma_eq_elim lenb lenb_bytes;
  assert (header == B.append ct tail);
  assert (B.singleton (content_type_byte T.ApplicationData) == B.singleton 0x17uy);
  U.lemma_singleton_of_list 0x17uy;
  Seq.lemma_eq_elim (B.singleton 0x17uy) (B.of_list [0x17uy]);
  assert_norm (0x0303 / 256 == 3);
  assert (byte (0x0303 / 256) == 0x03uy);
  assert (byte 0x0303 == 0x03uy);
  assert (ver_bytes == B.of_list [0x03uy; 0x03uy]);
  Seq.lemma_eq_elim ver (B.of_list [0x03uy; 0x03uy]);
  U.lemma_of_list_append
    [0x03uy; 0x03uy]
    [byte (fragment_len / 256); byte fragment_len];
  Seq.lemma_eq_elim tail
    (B.of_list [0x03uy; 0x03uy; byte (fragment_len / 256); byte fragment_len]);
  U.lemma_of_list_append
    [0x17uy]
    [0x03uy; 0x03uy; byte (fragment_len / 256); byte fragment_len];
  Seq.lemma_eq_elim header target

let lemma_application_data_record_header_bytes fragment_len =
  lemma_application_data_record_header fragment_len;
  lemma_serialize_application_data_header_bytes fragment_len;
  Seq.lemma_eq_elim
    (serialize_record_header T.ApplicationData fragment_len)
    (application_data_record_header_bytes fragment_len)

let lemma_application_data_record_header_bytes_reveal fragment_len = ()

let lemma_serialize_plaintext_reveal pt = ()

private let lemma_slice_append_single (#a:eqtype) (s:Seq.seq a) (x:a)
  : Lemma (ensures Seq.equal (Seq.slice (Seq.append s (Seq.create 1 x)) 0 (Seq.length s)) s)
=
  U.lemma_slice_append_left s (Seq.create 1 x)

let lemma_plaintext_roundtrip_reveal ct fragment =
  let input = B.append fragment (B.singleton (content_type_byte ct)) in
  lemma_serialize_plaintext_reveal { M.content_type = ct; M.fragment = fragment };
  lemma_slice_append_single fragment (content_type_byte ct);
  Seq.lemma_eq_elim (Seq.slice input 0 (Seq.length fragment)) fragment;
  Seq.lemma_len_append fragment (B.singleton (content_type_byte ct));
  let content_type_pos = Seq.length fragment in
  assert (Seq.length input == content_type_pos + 1);
  assert (Seq.length input - 1 == content_type_pos);
  Seq.lemma_index_app2 fragment (B.singleton (content_type_byte ct)) content_type_pos;
  Seq.lemma_index_create 1 (content_type_byte ct) 0;
  assert (Seq.index input content_type_pos == content_type_byte ct);
  lemma_content_type_byte_value ct;
  match ct with
  | T.ChangeCipherSpec ->
    U.lemma_content_type_change_cipher_spec_byte ();
    assert (U8.v (content_type_byte T.ChangeCipherSpec) == 20);
    assert (WS.content_type_of_byte (content_type_byte T.ChangeCipherSpec) == Some T.ChangeCipherSpec);
    assert (WS.parse_plaintext input ==
      Some { M.content_type = T.ChangeCipherSpec; M.fragment = fragment })
  | T.Alert ->
    U.lemma_content_type_alert_byte ();
    assert (U8.v (content_type_byte T.Alert) == 21);
    assert (WS.content_type_of_byte (content_type_byte T.Alert) == Some T.Alert);
    assert (WS.parse_plaintext input ==
      Some { M.content_type = T.Alert; M.fragment = fragment })
  | T.Handshake ->
    U.lemma_content_type_handshake_byte ();
    assert (U8.v (content_type_byte T.Handshake) == 22);
    assert_norm (WS.content_type_of_byte 0x16uy == Some T.Handshake);
    assert (WS.content_type_of_byte (content_type_byte T.Handshake) == Some T.Handshake);
    assert (WS.parse_plaintext input ==
      Some { M.content_type = T.Handshake; M.fragment = fragment })
  | T.ApplicationData ->
    U.lemma_content_type_application_data_byte ();
    assert (U8.v (content_type_byte T.ApplicationData) == 23);
    assert_norm (WS.content_type_of_byte 0x17uy == Some T.ApplicationData);
    assert (WS.content_type_of_byte (content_type_byte T.ApplicationData) == Some T.ApplicationData);
    assert (WS.parse_plaintext input ==
      Some { M.content_type = T.ApplicationData; M.fragment = fragment })
