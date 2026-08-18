module YModem.Impl.Codec

friend YModem.Wire.Generated.Ymodem_tag
friend YModem.Wire.Generated.Ymodem_soh_body_data
friend YModem.Wire.Generated.Ymodem_soh_body
friend YModem.Wire.Generated.Ymodem_message

#lang-pulse

(**
  Verified Pulse implementation of the YMODEM data-block codec leaves, proved
  against the QuackyDucky/EverParse-generated tagged-union wire format
  `YModem.Wire.Generated.Ymodem_message.ymodem_message`.

  `ymodem_emit_data_block` frames a 128-byte file chunk into a full 133-byte
  YMODEM SOH packet  SOH | blk | ~blk | data[128] | CRC-16, and proves that the
  output holds `YModem.Wire.ymodem_serialize (Body_soh body)` for a
  `ymodem_soh_body` whose 128-byte payload is exactly the input `data` and whose
  block number is `blk`.

  `ymodem_recv_data_block` consumes a 133-byte SOH packet (leading byte 0x01),
  extracts the 128-byte payload, and proves that the input `ymodem_parse`s to
  some `Body_soh body` whose block number is the returned value and whose payload
  is exactly the extracted bytes.

  Proof strategy (mirroring the previous flat-record leaves, adapted to the SUM):
  the top-level serializer decomposes as
    serialize ymodem_message_serializer (Body_soh body)
      == Seq.cons 0x01uy (serialize ymodem_soh_body_serializer body)
  via `LowParse.Spec.Sum.serialize_sum_eq` + `serialize_enum_key_eq`, and the SOH
  body decomposes as  [blk][blk_complement][data(128)][crc(2 BE)]  via
  `serialize_synth_eq` + `serialize_nondep_then_eq`, exactly as the generated
  `ymodem_soh_body_bytesize_eqn` model does.  The bytes are written into `out` by
  hand and shown equal to this serialization; for recv we build the witness body
  from the raw bytes, show `serialize (Body_soh body) == inp`, and reuse the
  already-proven round-trip law `lemma_ymodem_parse_serialize_exact`.  This
  requires `friend`-ing the generated modules, hence the accompanying
  `YModem.Impl.Codec.fsti` interface.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module LP = LowParse.Spec
module LPI = LowParse.Spec.AllIntegers
module E = FStar.Endianness

open YModem.Wire.Generated.Ymodem_tag
open YModem.Wire.Generated.Ymodem_soh_body_data
open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire

(* ------------------------------------------------------------------------ *)
(* Pure serializer-layout lemmas (require friend-ing the generated modules). *)
(* ------------------------------------------------------------------------ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"

(* Flat append decomposition of the 132-byte SOH body serializer, mirroring the
   model proof `ymodem_soh_body_bytesize_eqn` in the generated module but at the
   level of byte CONTENT (serialize_nondep_then_eq) rather than length. *)
let ymodem_soh_body_serialize_flat (body: ymodem_soh_body)
  : Lemma (LP.serialize ymodem_soh_body_serializer body ==
      Seq.append
        (Seq.append (Seq.create 1 body.blk) (Seq.create 1 body.blk_complement))
        (Seq.append (body.data <: Seq.seq U8.t) (E.n_to_be 2 (U16.v body.crc))))
= let x = body in
  synth_ymodem_soh_body_injective ();
  synth_ymodem_soh_body_inverse ();
  assert_norm (ymodem_soh_body_parser_kind == ymodem_soh_body'_parser_kind);
  LP.serialize_synth_eq _ synth_ymodem_soh_body ymodem_soh_body'_serializer synth_ymodem_soh_body_recip () x;
  LP.serialize_nondep_then_eq LPI.serialize_u8 LPI.serialize_u8 (x.blk, x.blk_complement);
  LP.serialize_nondep_then_eq ymodem_soh_body_data_serializer LPI.serialize_u16 (x.data, x.crc);
  LP.serialize_nondep_then_eq
    (LPI.serialize_u8 `LP.serialize_nondep_then` LPI.serialize_u8)
    (ymodem_soh_body_data_serializer `LP.serialize_nondep_then` LPI.serialize_u16)
    ((x.blk, x.blk_complement), (x.data, x.crc));
  LP.serialize_u8_spec x.blk;
  LP.serialize_u8_spec x.blk_complement;
  LP.serialize_u16_spec_be x.crc;
  assert (LP.serialize ymodem_soh_body_data_serializer x.data == (x.data <: Seq.seq U8.t));
  ()

(* Sum decomposition: the tag byte 0x01 prepended to the SOH body bytes.  Uses
   `serialize_sum_eq` (tag ++ case-body) + `serialize_enum_key_eq` (tag repr is a
   single u8) + the concrete enum repr value for `Soh` (0x01). *)
let ymodem_serialize_soh_split (body: ymodem_soh_body)
  : Lemma (ymodem_serialize (Body_soh body) ==
      Seq.append (Seq.create 1 1uy) (LP.serialize ymodem_soh_body_serializer body))
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_soh body);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Soh;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Soh == 1uy);
  LP.serialize_u8_spec 1uy;
  ()

(* Combined flat layout: the full 133-byte serialization of a `Body_soh body`. *)
let ymodem_serialize_soh_bytes (body: ymodem_soh_body)
  : Lemma (ymodem_serialize (Body_soh body) ==
      Seq.append (Seq.create 1 1uy)
        (Seq.append
          (Seq.append (Seq.create 1 body.blk) (Seq.create 1 body.blk_complement))
          (Seq.append (body.data <: Seq.seq U8.t) (E.n_to_be 2 (U16.v body.crc)))))
= ymodem_serialize_soh_split body;
  ymodem_soh_body_serialize_flat body

(* Choose a `U16.t` crc whose 2-byte big-endian encoding is exactly the pair of
   bytes actually written into the packet.  Because the protocol spec never
   constrains crc, this lets the layout proof succeed for ANY pair of crc bytes
   (crc = 0, or a real CRC-16), decoupling the byte writes from the field. *)
let crc_of_bytes (hi lo: U8.t) : U16.t =
  let b = Seq.append (Seq.create 1 hi) (Seq.create 1 lo) in
  E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t (E.be_to_n b)

let crc_bytes_correct (hi lo: U8.t)
  : Lemma (E.n_to_be 2 (U16.v (crc_of_bytes hi lo)) ==
           Seq.append (Seq.create 1 hi) (Seq.create 1 lo))
= let b = Seq.append (Seq.create 1 hi) (Seq.create 1 lo) in
  E.lemma_be_to_n_is_bounded b;
  E.n_to_be_be_to_n 2 b;
  ()

#pop-options

(* The two byte-equality lemmas below each reduce (via `Seq.lemma_eq_intro`) to a
   133/128-element pointwise equality over a 4-nested `Seq.append`.  That VC is a
   large top-level conjunction that Z3 verifies most reliably by splitting into
   per-region subgoals, so we ask for that split DETERMINISTICALLY (rather than
   relying on F*'s implicit, seed-sensitive fallback — cf. Warning 349).  The
   packaging helpers underneath then discharge trivially. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(* Single heavy byte-equality lemma, shared by both leaves.  Its ONLY proof
   goal is one `Seq.lemma_eq_intro` (a 133-element pointwise forall), so the
   query is never split and the existential-packaging helpers below stay
   trivial.  `s` is the concrete 133-byte buffer (the emit output, or the recv
   input); the data payload is characterised pointwise (exactly as the emit
   path already does), so this lemma takes `body0` abstractly and needs no
   `Seq.slice` trigger of its own. *)
let serialize_soh_eq (body0: ymodem_soh_body) (s: Seq.seq U8.t) (chi clo: U8.t)
  : Lemma
    (requires
       Seq.length s == 133 /\
       Seq.index s 0 == 1uy /\
       Seq.index s 1 == body0.blk /\
       Seq.index s 2 == body0.blk_complement /\
       (forall (j:nat). j < 128 ==> Seq.index s (3 + j) == Seq.index (body0.data <: Seq.seq U8.t) j) /\
       Seq.index s 131 == chi /\
       Seq.index s 132 == clo /\
       body0.crc == crc_of_bytes chi clo)
    (ensures s == ymodem_serialize (Body_soh body0))
= ymodem_serialize_soh_bytes body0;
  crc_bytes_correct chi clo;
  Seq.lemma_eq_intro s (ymodem_serialize (Body_soh body0))

(* The other heavy pointwise forall, isolated as its own single-goal lemma: the
   recv payload equals the middle slice of the input.  `Seq.slice i 3 131` is
   written literally so its slice-index SMTPat fires. *)
let recv_data_eq (i o': Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length i == 133 /\ Seq.length o' == 128 /\
       (forall (j:nat). j < 128 ==> Seq.index o' j == Seq.index i (3 + j)))
    (ensures o' == Seq.slice i 3 131)
= Seq.lemma_eq_intro o' (Seq.slice i 3 131)

(* Classical existential-introduction helper for the EMIT post-condition.  All
   of the pure proof lives here (in ordinary F-star), driven only by the concrete
   byte facts the imperative code establishes about the output buffer `sf`.  The
   heavy byte equality is discharged by `serialize_soh_eq`, so this is just a
   trivial witness introduction. *)
let emit_block_serialize_exists (blk bc chi clo: U8.t) (d sf: Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length d == 128 /\ Seq.length sf == 133 /\
       Seq.index sf 0 == 1uy /\
       Seq.index sf 1 == blk /\
       Seq.index sf 2 == bc /\
       (forall (j:nat). j < 128 ==> Seq.index sf (3 + j) == Seq.index d j) /\
       Seq.index sf 131 == chi /\
       Seq.index sf 132 == clo)
    (ensures
       (exists (body:ymodem_soh_body).
          (body.data <: Seq.seq U8.t) == d /\ body.blk == blk /\ sf == ymodem_serialize (Body_soh body)))
= let dd : Seq.lseq U8.t 128 = d in
  let body0 : ymodem_soh_body =
    { blk = blk; blk_complement = bc; data = dd; crc = crc_of_bytes chi clo } in
  serialize_soh_eq body0 sf chi clo;
  introduce exists (body:ymodem_soh_body).
     (body.data <: Seq.seq U8.t) == d /\ body.blk == blk /\ sf == ymodem_serialize (Body_soh body)
  with body0
  and ()

(* Classical existential-introduction helper for the RECV post-condition.  We
   build the witness body from the raw input bytes, show that it serializes back
   to exactly the input (the leading 0x01 supplied by the caller) via
   `serialize_soh_eq`, then reuse the already-proven round-trip law to obtain the
   parse.  Both heavy pointwise foralls are discharged in the dedicated lemmas
   above, so this helper is a trivial packaging step. *)
let recv_block_parse_exists (i o': Seq.seq U8.t) (blk: U8.t)
  : Lemma
    (requires
       Seq.length i == 133 /\ Seq.length o' == 128 /\
       Seq.index i 0 == 1uy /\
       blk == Seq.index i 1 /\
       (forall (j:nat). j < 128 ==> Seq.index o' j == Seq.index i (3 + j)))
    (ensures
       (exists (body:ymodem_soh_body) (rest:Seq.seq U8.t).
          ymodem_parse i == Some (Body_soh body, rest) /\ blk == body.blk /\ o' == body.data))
= let body0 : ymodem_soh_body =
    { blk = Seq.index i 1; blk_complement = Seq.index i 2; data = Seq.slice i 3 131;
      crc = crc_of_bytes (Seq.index i 131) (Seq.index i 132) } in
  (* body0.data == Seq.slice i 3 131 (written literally), so the slice-index
     SMTPat pins each payload byte to inp[3+j] and drives both facts below. *)
  serialize_soh_eq body0 i (Seq.index i 131) (Seq.index i 132);
  recv_data_eq i o';
  lemma_ymodem_parse_serialize_exact (Body_soh body0);
  eliminate exists (parsed:ymodem_message).
     (ymodem_parse (ymodem_serialize (Body_soh body0)) == Some (parsed, Seq.empty) /\ parsed == Body_soh body0)
  with
  ( introduce exists (body:ymodem_soh_body) (rest:Seq.seq U8.t).
       ymodem_parse i == Some (Body_soh body, rest) /\ blk == body.blk /\ o' == body.data
    with body0 Seq.empty
    and () )

#pop-options

(* ------------------------------------------------------------------------ *)
(* Real YMODEM CRC-16/CCITT (a.k.a. CRC-16/XMODEM): poly 0x1021, init 0,      *)
(* MSB-first, no reflection, no final xor.  These are pure `U16.t` functions  *)
(* (the protocol spec does not constrain crc, so no value-correctness proof   *)
(* is needed — only type-safety, which is automatic), and inline into clean C.*)
(* ------------------------------------------------------------------------ *)

inline_for_extraction
let crc16_bit (crc: U16.t) : U16.t =
  let shifted = U16.shift_left crc 1ul in
  if U16.gt (U16.logand crc 0x8000us) 0us
  then U16.logxor shifted 0x1021us
  else shifted

inline_for_extraction
let crc16_update (crc: U16.t) (b: U8.t) : U16.t =
  let x0 = U16.logxor crc (U16.shift_left (Cast.uint8_to_uint16 b) 8ul) in
  let x1 = crc16_bit x0 in
  let x2 = crc16_bit x1 in
  let x3 = crc16_bit x2 in
  let x4 = crc16_bit x3 in
  let x5 = crc16_bit x4 in
  let x6 = crc16_bit x5 in
  let x7 = crc16_bit x6 in
  crc16_bit x7

(* ------------------------------------------------------------------------ *)
(* The verified leaves.                                                      *)
(* ------------------------------------------------------------------------ *)

(* BoundedIntegers is opened only here so its overloaded `+`/`<` apply to the
   SizeT loop arithmetic below, and do NOT hijack the Prims nat arithmetic in
   the pure lemmas above. *)
open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn ymodem_emit_data_block
  (blk: U8.t)
  (data: array U8.t)
  (out: array U8.t)
  requires
    pts_to data 'd **
    pts_to out 'o **
    pure (Seq.length 'd == 128 /\ Seq.length 'o == 133)
  ensures
    pts_to data 'd **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 133 /\
             (exists (body:ymodem_soh_body).
                (body.data <: Seq.seq U8.t) == 'd /\ body.blk == blk /\
                o' == ymodem_serialize (Body_soh body))))
{
  (* 1. Compute the real YMODEM CRC-16/CCITT over the 128 payload bytes.
        The protocol spec does not constrain crc, so the loop carries no
        value invariant — only the counter bound and data length. *)
  let mut crc = 0us;
  let mut c = 0sz;
  while (!c < 128sz)
  invariant exists* (cv:SZ.t) (cr:U16.t).
    R.pts_to crc cr **
    R.pts_to c cv **
    pts_to data 'd **
    pure (SZ.v cv <= 128 /\ Seq.length 'd == 128)
  decreases (Prims.op_Subtraction 128 (SZ.v (!c)))
  {
    let cv = !c;
    let b = data.(cv);
    let creg = !crc;
    crc := crc16_update creg b;
    c := cv + 1sz;
  };
  let cval = !crc;
  let chi = Cast.uint16_to_uint8 (U16.shift_right cval 8ul);  (* high byte *)
  let clo = Cast.uint16_to_uint8 cval;                        (* low byte  *)
  (* 2. Write the fixed header: SOH | blk | ~blk. *)
  let bc = 255uy `U8.sub` blk;
  out.(0sz) <- 1uy;
  out.(1sz) <- blk;
  out.(2sz) <- bc;
  (* 3. Blit the 128-byte payload into out[3 .. 130]. *)
  let mut i = 0sz;
  while (!i < 128sz)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to data 'd **
    pts_to out sv **
    pure (
      SZ.v vi <= 128 /\
      Seq.length 'd == 128 /\
      Seq.length sv == 133 /\
      Seq.index sv 0 == 1uy /\
      Seq.index sv 1 == blk /\
      Seq.index sv 2 == bc /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (3 + j) == Seq.index 'd j))
  decreases (Prims.op_Subtraction 128 (SZ.v (!i)))
  {
    let vi = !i;
    let dv = data.(vi);
    out.(3sz + vi) <- dv;
    i := vi + 1sz;
  };
  (* 4. Write the CRC-16 big-endian (high byte first). *)
  out.(131sz) <- chi;
  out.(132sz) <- clo;
  with sf. assert (pts_to out sf);
  emit_block_serialize_exists blk bc chi clo 'd sf;
  ()
}
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
fn ymodem_recv_data_block
  (inp: array U8.t)
  (out_data: array U8.t)
  requires
    pts_to inp 'i **
    pts_to out_data 'o **
    pure (Seq.length 'i == 133 /\ Seq.length 'o == 128 /\ Seq.index 'i 0 == 1uy)
  returns blk: U8.t
  ensures
    pts_to inp 'i **
    (exists* (o':Seq.seq U8.t).
       pts_to out_data o' **
       pure (Seq.length o' == 128 /\
             (exists (body:ymodem_soh_body) (rest:Seq.seq U8.t).
                ymodem_parse 'i == Some (Body_soh body, rest) /\
                blk == body.blk /\ o' == body.data)))
{
  (* Copy the 128-byte payload inp[3 .. 130] into out_data[0 .. 127]. *)
  let mut i = 0sz;
  while (!i < 128sz)
  invariant exists* (vi:SZ.t) (ov:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to inp 'i **
    pts_to out_data ov **
    pure (
      SZ.v vi <= 128 /\
      Seq.length 'i == 133 /\
      Seq.length ov == 128 /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index ov j == Seq.index 'i (3 + j)))
  decreases (Prims.op_Subtraction 128 (SZ.v (!i)))
  {
    let vi = !i;
    let dv = inp.(3sz + vi);
    out_data.(vi) <- dv;
    i := vi + 1sz;
  };
  (* Block number is the second byte. *)
  let blk = inp.(1sz);
  with ov. assert (pts_to out_data ov);
  recv_block_parse_exists 'i ov blk;
  blk
}
#pop-options
