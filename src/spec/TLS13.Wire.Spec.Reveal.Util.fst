module TLS13.Wire.Spec.Reveal.Util

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let byte n = WS.byte n

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

#push-options "--fuel 8 --ifuel 2 --z3rlimit 80"
let lemma_slice_append_left (#a:eqtype) (prefix:Seq.seq a) (suffix:Seq.seq a)
  : Lemma (ensures Seq.equal (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix)
=
  Seq.lemma_len_append prefix suffix;
  Seq.lemma_len_slice (Seq.append prefix suffix) 0 (Seq.length prefix);
  assert (forall (i:nat{i < Seq.length prefix}).
    Seq.index (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) i ==
    Seq.index prefix i);
  Seq.lemma_eq_intro (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix
#pop-options

let lemma_singleton_of_list (b:U8.t)
  : Lemma (Seq.equal (B.singleton b) (B.of_list [b]))
=
  Seq.lemma_seq_of_list_induction [b]

let rec lemma_of_list_append (l1 l2: list U8.t)
  : Lemma (ensures Seq.equal (Seq.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))
          (decreases l1)
=
  match l1 with
  | [] ->
    Seq.lemma_seq_of_list_induction ([] <: list U8.t);
    Seq.append_empty_l (B.of_list l2)
  | hd :: tl ->
    lemma_of_list_append tl l2;
    Seq.lemma_seq_of_list_induction (hd :: (tl `FStar.List.Tot.append` l2));
    Seq.lemma_seq_of_list_induction (hd :: tl);
    Seq.append_assoc (Seq.create 1 hd) (B.of_list tl) (B.of_list l2)

let lemma_olcons (a b: list U8.t) (s: Seq.seq U8.t)
  : Lemma (Seq.equal (Seq.append (B.of_list a) (Seq.append (B.of_list b) s))
                     (Seq.append (B.of_list (FStar.List.Tot.append a b)) s))
=
  lemma_of_list_append a b;
  Seq.append_assoc (B.of_list a) (B.of_list b) s

let lemma_byte_0 () =
  WS.lemma_byte_v 0;
  assert_norm (U8.v 0uy == 0);
  assert (U8.v (WS.byte 0) == U8.v 0uy);
  U8.v_inj (WS.byte 0) 0uy

let lemma_byte_1 () =
  WS.lemma_byte_v 1;
  assert_norm (U8.v 1uy == 1);
  assert (U8.v (WS.byte 1) == U8.v 1uy);
  U8.v_inj (WS.byte 1) 1uy

let lemma_byte_3 () =
  WS.lemma_byte_v 3;
  assert_norm (U8.v 0x03uy == 3);
  assert (U8.v (WS.byte 3) == U8.v 0x03uy);
  U8.v_inj (WS.byte 3) 0x03uy

let lemma_byte_20 () =
  WS.lemma_byte_v 20;
  assert_norm (U8.v 20uy == 20);
  assert (U8.v (WS.byte 20) == U8.v 20uy);
  U8.v_inj (WS.byte 20) 20uy

let lemma_byte_32 () =
  WS.lemma_byte_v 32;
  assert_norm (U8.v 32uy == 32);
  assert (U8.v (WS.byte 32) == U8.v 32uy);
  U8.v_inj (WS.byte 32) 32uy

let lemma_byte_0303_lo () =
  WS.lemma_byte_v 0x0303;
  assert_norm (0x0303 % 256 == 3);
  assert_norm (U8.v 0x03uy == 3);
  assert (U8.v (WS.byte 0x0303) == U8.v 0x03uy);
  U8.v_inj (WS.byte 0x0303) 0x03uy

let lemma_content_type_change_cipher_spec_byte () =
  lemma_content_type_byte_value T.ChangeCipherSpec;
  assert_norm (U8.v 0x14uy == 20);
  assert (U8.v (content_type_byte T.ChangeCipherSpec) == U8.v 0x14uy);
  U8.v_inj (content_type_byte T.ChangeCipherSpec) 0x14uy

let lemma_content_type_alert_byte () =
  lemma_content_type_byte_value T.Alert;
  assert_norm (U8.v 0x15uy == 21);
  assert (U8.v (content_type_byte T.Alert) == U8.v 0x15uy);
  U8.v_inj (content_type_byte T.Alert) 0x15uy

let lemma_content_type_handshake_byte () =
  lemma_content_type_byte_value T.Handshake;
  assert_norm (U8.v 0x16uy == 22);
  assert (U8.v (content_type_byte T.Handshake) == U8.v 0x16uy);
  U8.v_inj (content_type_byte T.Handshake) 0x16uy

let lemma_content_type_application_data_byte () =
  lemma_content_type_byte_value T.ApplicationData;
  assert_norm (U8.v 0x17uy == 23);
  assert (U8.v (content_type_byte T.ApplicationData) == U8.v 0x17uy);
  U8.v_inj (content_type_byte T.ApplicationData) 0x17uy

let lemma_u8_reveal (n:nat)
  : Lemma (Seq.equal (u8 n) (B.singleton (byte n)))
= ()

let lemma_u16_reveal (n:nat)
  : Lemma (Seq.equal (u16 n) (B.of_list [byte (n / 256); byte n]))
= ()

let lemma_u24_reveal (n:nat)
  : Lemma (Seq.equal (u24 n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))
= ()
