module TLS13.Impl.Serializer.ProtectedRecord

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Serializer.Common
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal

let application_data_header_bytes (n:nat) : GTot (b:B.bytes{B.length b == 5}) =
  B.of_list [0x17uy; 0x03uy; 0x03uy; C.byte (n / 256); C.byte n]

let lemma_application_data_header_bytes (n:nat)
  : Lemma (ensures Seq.equal
      (application_data_header_bytes n)
      (WSR.application_data_record_header_bytes n))
=
  WSR.lemma_application_data_record_header_bytes_reveal n;
  WSR.lemma_byte_value (n / 256);
  WSR.lemma_byte_value n;
  C.lemma_byte_reveal (n / 256);
  C.lemma_byte_reveal n;
  assert_norm (U8.v (C.byte (n / 256)) == (n / 256) % 256);
  assert_norm (U8.v (C.byte n) == n % 256);
  U8.v_inj (WSR.byte (n / 256)) (C.byte (n / 256));
  U8.v_inj (WSR.byte n) (C.byte n);
  assert (WSR.byte (n / 256) == C.byte (n / 256));
  assert (WSR.byte n == C.byte n);
  Seq.lemma_eq_elim
    (WSR.application_data_record_header_bytes n)
    (B.of_list [0x17uy; 0x03uy; 0x03uy; C.byte (n / 256); C.byte n]);
  assert_norm (application_data_header_bytes n ==
    B.of_list [0x17uy; 0x03uy; 0x03uy; C.byte (n / 256); C.byte n]);
  Seq.lemma_eq_refl (application_data_header_bytes n) (WSR.application_data_record_header_bytes n)

let lemma_handshake_content_type_byte ()
  : Lemma (WSR.content_type_byte T.Handshake == 22uy)
=
  WSR.lemma_content_type_byte_value T.Handshake;
  assert (U8.v (WSR.content_type_byte T.Handshake) == 0x16);
  U8.v_inj (WSR.content_type_byte T.Handshake) 22uy

fn encode_handshake_inner_plaintext
  (#msg: erased M.handshake_msg)
  (handshake: array U8.t)
  (handshake_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  (#handshake_bytes: erased B.bytes)
  (#old_bytes: erased B.bytes)
  requires pts_to handshake (Ghost.reveal handshake_bytes) **
           pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal handshake_bytes) == SZ.v handshake_len /\
                 Seq.equal
                   (Ghost.reveal handshake_bytes)
                   (WS.serialize_handshake (Ghost.reveal msg)) /\
                 B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == SZ.v handshake_len + 1)
  ensures exists* out_bytes.
          pts_to handshake (Ghost.reveal handshake_bytes) **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                Seq.equal out_bytes
                  (CS.sent_tls_inner_plaintext_fragment
                    (M.TlsHandshake (Ghost.reveal msg))))
{
  C.copy_array_slice_to_array handshake handshake_len 0sz handshake_len out out_len 0sz;
  out.(handshake_len) <- 22uy;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v out_len == SZ.v handshake_len + 1));
  assert (pure (Seq.length out_bytes == SZ.v handshake_len + 1));
  assert (pure (Seq.equal
    (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v handshake_len))
    (Seq.slice (Ghost.reveal handshake_bytes) 0 (SZ.v handshake_len))));
  C.lemma_slice_all (Ghost.reveal handshake_bytes);
  Seq.lemma_eq_elim
    (Seq.slice (Ghost.reveal handshake_bytes) 0 (SZ.v handshake_len))
    (Ghost.reveal handshake_bytes);
  assert (pure (Seq.equal
    (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v handshake_len))
    (Ghost.reveal handshake_bytes)));
  assert (pure (Seq.length
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v handshake_len)
      (Seq.length (Ghost.reveal out_bytes))) == 1));
  assert (pure (Seq.index
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v handshake_len)
      (Seq.length (Ghost.reveal out_bytes)))
    0 == 22uy));
  Seq.lemma_eq_intro
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v handshake_len)
      (Seq.length (Ghost.reveal out_bytes)))
    (B.singleton 22uy);
  SeqP.lemma_split (Ghost.reveal out_bytes) (SZ.v handshake_len);
  Seq.lemma_eq_elim
    (Seq.slice (Ghost.reveal out_bytes) 0 (SZ.v handshake_len))
    (Ghost.reveal handshake_bytes);
  Seq.lemma_eq_elim
    (Seq.slice
      (Ghost.reveal out_bytes)
      (SZ.v handshake_len)
      (Seq.length (Ghost.reveal out_bytes)))
    (B.singleton 22uy);
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (B.append (Ghost.reveal handshake_bytes) (B.singleton 22uy))));
  lemma_handshake_content_type_byte ();
  Seq.lemma_eq_elim
    (B.singleton 22uy)
    (B.singleton (WSR.content_type_byte T.Handshake));
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (B.append
      (Ghost.reveal handshake_bytes)
      (B.singleton (WSR.content_type_byte T.Handshake)))));
  WSR.lemma_serialize_plaintext_reveal {
    M.content_type = T.Handshake;
    M.fragment = Ghost.reveal handshake_bytes;
  };
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (WS.serialize_plaintext {
      M.content_type = T.Handshake;
      M.fragment = Ghost.reveal handshake_bytes;
    })));
  Seq.lemma_eq_elim
    (Ghost.reveal handshake_bytes)
    (WS.serialize_handshake (Ghost.reveal msg));
  WS.lemma_serialize_tls_message_handshake (Ghost.reveal msg);
  assert (pure (Seq.equal
    (Ghost.reveal out_bytes)
    (CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg)))));
}

fn serialize_application_data_header
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5 /\
                 SZ.v fragment_len <= 16640)
  ensures exists* header_bytes.
          pts_to out header_bytes **
          pure (B.length header_bytes == 5 /\
                Seq.equal
                  (Ghost.reveal header_bytes)
                  (CS.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record_header (Ghost.reveal header_bytes) ==
                  Some (T.Application_data, SZ.v fragment_len))
{
  out.(0sz) <- 23uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  with header_prefix. assert (pts_to out header_prefix);
  pts_to_len out;
  assert (pure (B.length header_prefix == 5));
  assert (pure (B.length header_prefix == length out));
  out.(3sz) <- C.u8_of_sizet (SZ.div fragment_len 256sz);
  out.(4sz) <- C.u8_of_sizet fragment_len;
  with header_bytes. assert (pts_to out header_bytes);
  assert (pure (B.length header_bytes == 5));
  WSR.lemma_application_data_record_header_bytes (SZ.v fragment_len);
  lemma_application_data_header_bytes (SZ.v fragment_len);
  assert (pure (Seq.length (application_data_header_bytes (SZ.v fragment_len)) == 5));
  assert (pure (Seq.index header_bytes 0 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 0));
  assert (pure (Seq.index header_bytes 1 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 1));
  assert (pure (Seq.index header_bytes 2 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 2));
  assert (pure (Seq.index header_bytes 3 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 3));
  assert (pure (Seq.index header_bytes 4 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 4));
  Seq.lemma_eq_intro header_bytes (application_data_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    header_bytes
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CS.application_data_record_header (SZ.v fragment_len))
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  WSR.lemma_parse_application_data_record_header_bytes (SZ.v fragment_len);
  assert (pure (Seq.equal
    header_bytes
    (CS.application_data_record_header (SZ.v fragment_len))));
  assert (pure (WS.parse_record_header header_bytes ==
    Some (T.Application_data, SZ.v fragment_len)));
}

fn serialize_raw_application_data_record
  (fragment: array U8.t)
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to fragment 'fragment_bytes **
          pts_to out 'old_out **
          pure (B.length 'old_out == SZ.v out_len /\
                B.length 'fragment_bytes == SZ.v fragment_len /\
                SZ.v fragment_len <= 16640 /\
                SZ.v fragment_len + 5 <= SZ.v out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v fragment_len + 5 /\
               (let raw_prefix =
                  Seq.slice out_bytes 0 (SZ.v written) in
                Seq.equal raw_prefix (WS.serialize_record T.Application_data (Ghost.reveal 'fragment_bytes)) /\
                Seq.equal
                  (CS.record_header_aad raw_prefix)
                  (CS.application_data_record_header (SZ.v fragment_len)) /\
                WS.parse_record raw_prefix ==
                  Some (T.Application_data, (Ghost.reveal 'fragment_bytes), SZ.v written) /\
                CS.raw_records_exactly raw_prefix T.Application_data 1))
{
  out.(0sz) <- 23uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x03uy;
  with header_prefix. assert (pts_to out header_prefix);
  pts_to_len out;
  assert (pure (B.length header_prefix == SZ.v out_len));
  assert (pure (B.length header_prefix == length out));
  out.(3sz) <- C.u8_of_sizet (SZ.div fragment_len 256sz);
  out.(4sz) <- C.u8_of_sizet fragment_len;
  with header_written. assert (pts_to out header_written);
  assert (pure (B.length header_written == SZ.v out_len));
  WSR.lemma_application_data_record_header_bytes (SZ.v fragment_len);
  lemma_application_data_header_bytes (SZ.v fragment_len);
  Seq.lemma_len_slice header_written 0 5;
  assert (pure (Seq.length (CL.raw_slice header_written 0 5) == 5));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 0 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 0));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 1 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 1));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 2 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 2));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 3 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 3));
  assert (pure (Seq.index (CL.raw_slice header_written 0 5) 4 == Seq.index (application_data_header_bytes (SZ.v fragment_len)) 4));
  Seq.lemma_eq_intro (CL.raw_slice header_written 0 5) (application_data_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CL.raw_slice header_written 0 5)
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  Seq.lemma_eq_elim
    (CS.application_data_record_header (SZ.v fragment_len))
    (WSR.application_data_record_header_bytes (SZ.v fragment_len));
  C.copy_array_slice_to_array fragment fragment_len 0sz fragment_len out out_len 5sz;
  let written = SZ.add fragment_len 5sz;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == SZ.v out_len));
  assert (pure (SZ.v written == SZ.v fragment_len + 5));
  assert (pure (SZ.v written <= SZ.v out_len));
  C.lemma_raw_slice_all (Ghost.reveal 'fragment_bytes);
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes);
  SeqP.append_slices
    (CL.raw_slice header_written 0 5)
    (B.append
      (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
      (CL.raw_slice header_written (5 + SZ.v fragment_len) (SZ.v out_len)));
  SeqP.append_slices
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (CL.raw_slice header_written (5 + SZ.v fragment_len) (SZ.v out_len));
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (B.append
      (CL.raw_slice header_written 0 5)
      (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len)))));
  Seq.lemma_eq_elim
    (CL.raw_slice (Ghost.reveal 'fragment_bytes) 0 (SZ.v fragment_len))
    (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (B.append (CS.application_data_record_header (SZ.v fragment_len)) (Ghost.reveal 'fragment_bytes))));
  WSR.lemma_serialize_application_data_record_reveal (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (Seq.slice out_bytes 0 (SZ.v written))
    (WS.serialize_record T.Application_data (Ghost.reveal 'fragment_bytes))));
  Seq.lemma_eq_elim
    (Seq.slice out_bytes 0 (SZ.v written))
    (WS.serialize_record T.Application_data (Ghost.reveal 'fragment_bytes));
  WS.lemma_parse_record_serialize_record
    T.Application_data
    (Ghost.reveal 'fragment_bytes);
  assert (pure (B.length (Seq.slice out_bytes 0 (SZ.v written)) == SZ.v written));
  assert (pure (WS.parse_record (Seq.slice out_bytes 0 (SZ.v written)) ==
    Some (T.Application_data, (Ghost.reveal 'fragment_bytes), SZ.v written)));
  WSR.lemma_application_data_record_aad (Ghost.reveal 'fragment_bytes);
  assert (pure (Seq.equal
    (CS.record_header_aad (Seq.slice out_bytes 0 (SZ.v written)))
    (CS.application_data_record_header (SZ.v fragment_len))));
  assert (pure (CS.raw_records_exactly (Seq.slice out_bytes 0 (SZ.v written)) T.Application_data 1));
  written
}

fn serialize_protected_handshake_record
  (#msg: erased M.handshake_msg)
  (write_state: Rec.record_state)
  (handshake: array U8.t)
  (handshake_len: SZ.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  (#record_write: erased R.direction_state)
  (#handshake_bytes: erased B.bytes)
  (#old_network: erased B.bytes)
  requires Rec.is_record_state write_state (Ghost.reveal record_write) **
           pts_to handshake (Ghost.reveal handshake_bytes) **
           pts_to network_out (Ghost.reveal old_network) **
           pure (B.length (Ghost.reveal handshake_bytes) == SZ.v handshake_len /\
                 Seq.equal
                   (Ghost.reveal handshake_bytes)
                   (WS.serialize_handshake (Ghost.reveal msg)) /\
                 B.length (Ghost.reveal old_network) == SZ.v network_out_len /\
                 SZ.v handshake_len + 17 <= 16640 /\
                 SZ.v handshake_len + 22 <= SZ.v network_out_len /\
                 Some? (R.seal
                   (Ghost.reveal record_write)
                   (CS.application_data_record_header (SZ.v handshake_len + 17))
                   {
                     R.content_type = T.Application_data;
                     R.fragment =
                       CS.sent_tls_inner_plaintext_fragment
                         (M.TlsHandshake (Ghost.reveal msg));
                   }))
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* network_bytes.
          Rec.is_record_state write_state (Ghost.reveal record_write) **
          pts_to handshake (Ghost.reveal handshake_bytes) **
          pts_to network_out network_bytes **
          pure (B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == SZ.v handshake_len + 22 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.Application_data 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.Application_data, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.Application_data outer_fragment) /\
                   Seq.equal
                     (CS.record_header_aad raw_prefix)
                     (CS.application_data_record_header (SZ.v handshake_len + 17)) /\
                   R.seal
                     (Ghost.reveal record_write)
                     (CS.record_header_aad raw_prefix)
                     {
                       R.content_type = T.Application_data;
                       R.fragment =
                         CS.sent_tls_inner_plaintext_fragment
                           (M.TlsHandshake (Ghost.reveal msg));
                     } ==
                     Some (outer_fragment, R.next_seq (Ghost.reveal record_write)))))
{
  assert (pure (SZ.fits (SZ.v handshake_len + 1)));
  let inner_len = handshake_len `SZ.add` 1sz;
  assert (pure (SZ.v inner_len == SZ.v handshake_len + 1));
  assert (pure (SZ.fits (SZ.v inner_len + 16)));
  let ciphertext_len = inner_len `SZ.add` 16sz;
  assert (pure (SZ.v ciphertext_len == SZ.v handshake_len + 17));
  assert (pure (SZ.v ciphertext_len <= 16640));
  assert (pure (SZ.fits (SZ.v ciphertext_len + 5)));
  let written_len = ciphertext_len `SZ.add` 5sz;
  assert (pure (SZ.v written_len == SZ.v handshake_len + 22));
  assert (pure (SZ.v written_len <= SZ.v network_out_len));

  let inner_plaintext = V.alloc 0uy inner_len;
  V.to_array_pts_to inner_plaintext;
  encode_handshake_inner_plaintext
    #msg
    handshake
    handshake_len
    (V.vec_to_array inner_plaintext)
    inner_len;
  with inner_plaintext_bytes. assert (pts_to (V.vec_to_array inner_plaintext) inner_plaintext_bytes);
  assert (pure (B.length inner_plaintext_bytes == SZ.v inner_len));
  assert (pure (Seq.equal
    inner_plaintext_bytes
    (CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg)))));

  let mut aad = [| 0uy; 5sz |];
  serialize_application_data_header ciphertext_len aad 5sz;
  with aad_bytes. assert (pts_to aad aad_bytes);
  assert (pure (Seq.equal aad_bytes (CS.application_data_record_header (SZ.v ciphertext_len))));
  assert (pure (Seq.equal aad_bytes (CS.application_data_record_header (SZ.v handshake_len + 17))));

  let ciphertext = V.alloc 0uy ciphertext_len;
  V.to_array_pts_to ciphertext;
  let sealed =
    Rec.seal_application_no_update
      write_state
      aad
      5sz
      (V.vec_to_array inner_plaintext)
      inner_len
      (V.vec_to_array ciphertext);
  with ciphertext_bytes. assert (pts_to (V.vec_to_array ciphertext) ciphertext_bytes);
  if sealed {
    assert (pure (R.seal
      (Ghost.reveal record_write)
      aad_bytes
      { R.content_type = T.Application_data; R.fragment = inner_plaintext_bytes } ==
      Some (ciphertext_bytes, R.next_seq (Ghost.reveal record_write))));
    Seq.lemma_eq_elim
      aad_bytes
      (CS.application_data_record_header (SZ.v handshake_len + 17));
    Seq.lemma_eq_elim
      inner_plaintext_bytes
      (CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg)));
    assert (pure (R.seal
      (Ghost.reveal record_write)
      (CS.application_data_record_header (SZ.v handshake_len + 17))
      {
        R.content_type = T.Application_data;
        R.fragment =
          CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg));
      } ==
      Some (ciphertext_bytes, R.next_seq (Ghost.reveal record_write))));

    let written =
      serialize_raw_application_data_record
        (V.vec_to_array ciphertext)
        ciphertext_len
        network_out
        network_out_len;
    with network_bytes. assert (pts_to network_out network_bytes);
    assert (pure (SZ.v written == SZ.v ciphertext_len + 5));
    assert (pure (SZ.v written == SZ.v handshake_len + 22));
    assert (pure (SZ.v written == SZ.v written_len));
    assert (pure (B.length network_bytes == SZ.v network_out_len));
    assert (pure (CS.raw_records_exactly (Seq.slice network_bytes 0 (SZ.v written)) T.Application_data 1));
    assert (pure (Seq.equal
      (Seq.slice network_bytes 0 (SZ.v written))
      (WS.serialize_record T.Application_data ciphertext_bytes)));
    assert (pure (WS.parse_record (Seq.slice network_bytes 0 (SZ.v written)) ==
      Some (T.Application_data, ciphertext_bytes, SZ.v written)));
    assert (pure (Seq.equal
      (CS.record_header_aad (Seq.slice network_bytes 0 (SZ.v written)))
      (CS.application_data_record_header (SZ.v ciphertext_len))));
    assert (pure (Seq.equal
      (CS.record_header_aad (Seq.slice network_bytes 0 (SZ.v written)))
      (CS.application_data_record_header (SZ.v handshake_len + 17))));
    assert (pure (R.seal
      (Ghost.reveal record_write)
      (CS.record_header_aad (Seq.slice network_bytes 0 (SZ.v written)))
      {
        R.content_type = T.Application_data;
        R.fragment =
          CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg));
      } ==
      Some (ciphertext_bytes, R.next_seq (Ghost.reveal record_write))));
    V.to_vec_pts_to ciphertext;
    V.free ciphertext;
    V.to_vec_pts_to inner_plaintext;
    V.free inner_plaintext;
    written
  } else {
    assert (pure (R.seal
      (Ghost.reveal record_write)
      aad_bytes
      { R.content_type = T.Application_data; R.fragment = inner_plaintext_bytes } == None));
    Seq.lemma_eq_elim
      aad_bytes
      (CS.application_data_record_header (SZ.v handshake_len + 17));
    Seq.lemma_eq_elim
      inner_plaintext_bytes
      (CS.sent_tls_inner_plaintext_fragment (M.TlsHandshake (Ghost.reveal msg)));
    V.to_vec_pts_to ciphertext;
    V.free ciphertext;
    V.to_vec_pts_to inner_plaintext;
    V.free inner_plaintext;
    assert (pure False);
    0sz
  }
}
