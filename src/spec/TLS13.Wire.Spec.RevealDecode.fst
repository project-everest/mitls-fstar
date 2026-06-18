module TLS13.Wire.Spec.RevealDecode

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
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
     | 0x14 -> Some T.ChangeCipherSpec
     | 0x15 -> Some T.Alert
     | 0x16 -> Some T.Handshake
     | 0x17 -> Some T.ApplicationData
     | _ -> None));
  ()

let lemma_parse_plaintext_some input =
  let cpos = B.length input - 1 in
  assert (WS.content_type_of_byte (Seq.index input cpos) ==
    (match U8.v (Seq.index input cpos) with
     | 0x14 -> Some T.ChangeCipherSpec
     | 0x15 -> Some T.Alert
     | 0x16 -> Some T.Handshake
     | 0x17 -> Some T.ApplicationData
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

let lemma_parse_tls_message_no_client_hello ct fragment ch =
  match ct with
  | T.Handshake ->
    (match LP.parse GHS.handshake_parser fragment with
     | None -> ()
     | Some (h, _) ->
       match h with
       | GHS.Body_client_hello _ -> ()
       | GHS.Body_server_hello _ -> ()
       | GHS.Body_encrypted_extensions _ -> ()
       | GHS.Body_certificate _ -> ()
       | GHS.Body_certificate_verify _ -> ()
       | GHS.Body_finished _ -> ()
       | GHS.Body_key_update _ -> ()
       | GHS.Body_new_session_ticket _ -> ())
  | T.ApplicationData -> ()
  | T.Alert -> ()
  | T.ChangeCipherSpec -> ()
