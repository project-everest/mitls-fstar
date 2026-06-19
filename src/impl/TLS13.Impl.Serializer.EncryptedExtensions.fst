module TLS13.Impl.Serializer.EncryptedExtensions

friend TLS13.Wire.Spec

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module E = FStar.Endianness
module M = TLS13.Messages
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let empty_encrypted_extensions_bytes : B.bytes =
  B.of_list [8uy; 0uy; 0uy; 2uy; 0uy; 0uy]

let byte n = WS.byte n

let lemma_byte_0 () =
  WS.lemma_byte_v 0;
  assert_norm (U8.v 0uy == 0);
  assert (U8.v (byte 0) == U8.v 0uy);
  U8.v_inj (byte 0) 0uy

let lemma_byte_2 () =
  WS.lemma_byte_v 2;
  assert_norm (U8.v 2uy == 2);
  assert (U8.v (byte 2) == U8.v 2uy);
  U8.v_inj (byte 2) 2uy

let lemma_byte_8 () =
  WS.lemma_byte_v 8;
  assert_norm (U8.v 8uy == 8);
  assert (U8.v (byte 8) == U8.v 8uy);
  U8.v_inj (byte 8) 8uy

let lemma_u8_reveal (n:nat)
  : Lemma (Seq.equal (WS.u8 n) (B.singleton (byte n)))
=
  ()

let lemma_u16_reveal (n:nat)
  : Lemma (Seq.equal (WS.u16 n) (B.of_list [byte (n / 256); byte n]))
=
  ()

let lemma_u24_reveal (n:nat)
  : Lemma (Seq.equal (WS.u24 n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))
=
  ()

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

let lemma_empty_encrypted_extensions_bytes ()
  : Lemma (Seq.equal empty_encrypted_extensions_bytes (WS.serialize_empty_encrypted_extensions ()))
=
  assert_norm (empty_encrypted_extensions_bytes == B.of_list [8uy; 0uy; 0uy; 2uy; 0uy; 0uy]);
  let body = WS.serialize_encrypted_extensions { M.negotiated_alpn = None; M.body = B.empty } in
  assert (WS.serialize_empty_encrypted_extensions () ==
    B.append (WS.u8 8) (B.append (WS.u24 (B.length body)) body));
  assert (body == B.append (WS.u16 0) B.empty);
  lemma_u16_reveal 0;
  Seq.lemma_eq_elim (WS.u16 0) (B.of_list [byte 0; byte 0]);
  lemma_byte_0 ();
  assert (B.of_list [byte 0; byte 0] == B.of_list [0uy; 0uy]);
  Seq.lemma_eq_elim (WS.u16 0) (B.of_list [0uy; 0uy]);
  assert (Seq.equal body (B.of_list [0uy; 0uy]));
  assert (B.length body == 2);
  lemma_u8_reveal 8;
  TLS13.Wire.Spec.Reveal.Util.lemma_singleton_of_list 8uy;
  lemma_byte_8 ();
  Seq.lemma_eq_elim (WS.u8 8) (B.of_list [8uy]);
  lemma_u24_reveal 2;
  assert_norm (2 / 65536 == 0);
  assert_norm (2 / 256 == 0);
  lemma_byte_2 ();
  Seq.lemma_eq_elim (WS.u24 2) (B.of_list [0uy; 0uy; 2uy]);
  Seq.lemma_eq_elim body (B.of_list [0uy; 0uy]);
  lemma_olcons [8uy] [0uy; 0uy; 2uy] (B.of_list [0uy; 0uy]);
  lemma_olcons [8uy; 0uy; 0uy; 2uy] [0uy; 0uy] B.empty;
  Seq.append_empty_r (B.of_list [8uy; 0uy; 0uy; 2uy; 0uy; 0uy]);
  assert (Seq.equal
    (WS.serialize_empty_encrypted_extensions ())
    (B.of_list [8uy; 0uy; 0uy; 2uy; 0uy; 0uy]));
  Seq.lemma_eq_intro empty_encrypted_extensions_bytes (WS.serialize_empty_encrypted_extensions ())

let lemma_eq_empty_encrypted_extensions_bytes (s:B.bytes)
  : Lemma
      (requires B.length s == 6 /\
                Seq.index s 0 == 8uy /\
                Seq.index s 1 == 0uy /\
                Seq.index s 2 == 0uy /\
                Seq.index s 3 == 2uy /\
                Seq.index s 4 == 0uy /\
                Seq.index s 5 == 0uy)
      (ensures Seq.equal s empty_encrypted_extensions_bytes)
=
  assert (B.length empty_encrypted_extensions_bytes == 6);
  introduce forall (i:nat).
    i < B.length s ==>
    Seq.index s i == Seq.index empty_encrypted_extensions_bytes i
  with introduce _ ==> _
  with _. (
    if i = 0 then ()
    else if i = 1 then ()
    else if i = 2 then ()
    else if i = 3 then ()
    else if i = 4 then ()
    else if i = 5 then ()
    else assert False
  );
  Seq.lemma_eq_intro s empty_encrypted_extensions_bytes

fn serialize_empty_encrypted_extensions
  (out: array U8.t)
  (out_len: SZ.t)
  (#old_bytes: erased B.bytes)
  requires pts_to out (Ghost.reveal old_bytes) **
           pure (B.length (Ghost.reveal old_bytes) == SZ.v out_len /\
                 SZ.v out_len == 6)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to out out_bytes **
          pure (B.length out_bytes == 6 /\
                SZ.v written == 6 /\
                Seq.equal out_bytes (WS.serialize_empty_encrypted_extensions ()))
{
  out.(0sz) <- 8uy;
  out.(1sz) <- 0uy;
  out.(2sz) <- 0uy;
  out.(3sz) <- 2uy;
  out.(4sz) <- 0uy;
  out.(5sz) <- 0uy;
  with out_bytes. assert (pts_to out out_bytes);
  assert (pure (B.length out_bytes == 6));
  assert (pure (Seq.index out_bytes 0 == 8uy));
  assert (pure (Seq.index out_bytes 1 == 0uy));
  assert (pure (Seq.index out_bytes 2 == 0uy));
  assert (pure (Seq.index out_bytes 3 == 2uy));
  assert (pure (Seq.index out_bytes 4 == 0uy));
  assert (pure (Seq.index out_bytes 5 == 0uy));
  lemma_eq_empty_encrypted_extensions_bytes out_bytes;
  lemma_empty_encrypted_extensions_bytes ();
  Seq.lemma_eq_elim empty_encrypted_extensions_bytes (WS.serialize_empty_encrypted_extensions ());
  assert (pure (Seq.equal out_bytes (WS.serialize_empty_encrypted_extensions ())));
  6sz
}
