module YModem.Impl.Server

friend YModem.Wire.Generated.Ymodem_packet_data
friend YModem.Wire.Generated.Ymodem_packet

#lang-pulse

(**
  Verified Pulse implementation of the YMODEM *sender* (server) leaf, the
  executable counterpart of the YModem.Protocol `YmodemSendBlock` step.

  `ymodem_server_emit_block` frames a 128-byte file chunk into a full 133-byte
  YMODEM packet SOH | blk | ~blk | data[128] | CRC-16.  It is proved against the
  QuackyDucky/EverParse-generated LowParse wire format: after the call, `out`
  holds `YModem.Wire.ymodem_serialize pkt` for a `ymodem_packet` whose 128-byte
  payload `pkt.data` is exactly the input `data` (the only field the protocol
  spec constrains; soh/blk/blk_complement/crc are unconstrained).

  Proof strategy: the bytes are written into `out` by hand and shown equal to the
  serializer output via a local layout lemma (`emit_block_serialize_exists`) that
  decomposes `ymodem_packet_serializer` with `serialize_synth_eq` +
  `serialize_nondep_then_eq`.  This requires `friend`-ing the generated modules,
  hence the accompanying `YModem.Impl.Server.fsti` interface.
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
module E = FStar.Endianness

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

(* ------------------------------------------------------------------------ *)
(* Pure serializer-layout lemmas (require friend-ing the generated modules). *)
(* ------------------------------------------------------------------------ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

(* Flat append decomposition of the 133-byte serializer, mirroring the model
   proof `ymodem_packet_bytesize_eqn` in the generated module. *)
let ymodem_serialize_flat (pkt: ymodem_packet)
  : Lemma (ymodem_serialize pkt ==
      Seq.append
        (Seq.append (Seq.append (Seq.create 1 pkt.soh) (Seq.create 1 pkt.blk))
                    (Seq.append (Seq.create 1 pkt.blk_complement) pkt.data))
        (E.n_to_be 2 (U16.v pkt.crc)))
= let x = pkt in
  synth_ymodem_packet_injective ();
  synth_ymodem_packet_inverse ();
  LP.serialize_synth_eq ymodem_packet'_parser synth_ymodem_packet ymodem_packet'_serializer synth_ymodem_packet_recip () x;
  LP.serialize_nondep_then_eq LP.serialize_u8 LP.serialize_u8 (x.soh, x.blk);
  LP.serialize_nondep_then_eq LP.serialize_u8 ymodem_packet_data_serializer (x.blk_complement, x.data);
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then LP.serialize_u8 LP.serialize_u8) (LP.serialize_nondep_then LP.serialize_u8 ymodem_packet_data_serializer) ((x.soh, x.blk), (x.blk_complement, x.data));
  LP.serialize_nondep_then_eq (LP.serialize_nondep_then (LP.serialize_nondep_then LP.serialize_u8 LP.serialize_u8) (LP.serialize_nondep_then LP.serialize_u8 ymodem_packet_data_serializer)) LP.serialize_u16 (((x.soh, x.blk), (x.blk_complement, x.data)), x.crc);
  LP.serialize_u8_spec x.soh;
  LP.serialize_u8_spec x.blk;
  LP.serialize_u8_spec x.blk_complement;
  LP.serialize_u16_spec_be x.crc;
  assert (LP.serialize ymodem_packet_data_serializer x.data == x.data);
  ()

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

(* Classical existential-introduction helper.  All of the pure proof lives here
   (in ordinary F-star), driven only by the concrete byte facts the imperative
   code establishes about the output buffer `sf`.  Keeping the witness packet
   `pkt0` inside this lemma avoids binding an (informative) `ymodem_packet` in
   the Pulse fn, where it would be inferred ghost.  The post-condition uses a
   single resource-linked `exists* o'` with the packet as an inner classical
   `exists` inside `pure`, because Pulse cannot supply a witness for a pure-only
   `exists*` binder. *)
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
       (exists (pkt:ymodem_packet). (pkt.data <: Seq.seq U8.t) == d /\ sf == ymodem_serialize pkt))
= let pkt0 : ymodem_packet =
    { soh = 1uy; blk = blk; blk_complement = bc; data = d; crc = crc_of_bytes chi clo } in
  ymodem_serialize_flat pkt0;
  crc_bytes_correct chi clo;
  Seq.lemma_eq_intro sf (ymodem_serialize pkt0);
  introduce exists (pkt:ymodem_packet). (pkt.data <: Seq.seq U8.t) == d /\ sf == ymodem_serialize pkt
  with pkt0
  and ()

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
(* The verified leaf.                                                        *)
(* ------------------------------------------------------------------------ *)

(* BoundedIntegers is opened only here so its overloaded `+`/`<` apply to the
   SizeT loop arithmetic below, and do NOT hijack the Prims nat arithmetic in
   the pure lemmas above. *)
open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
fn ymodem_server_emit_block
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
             (exists (pkt:ymodem_packet). (pkt.data <: Seq.seq U8.t) == 'd /\ o' == ymodem_serialize pkt)))
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
