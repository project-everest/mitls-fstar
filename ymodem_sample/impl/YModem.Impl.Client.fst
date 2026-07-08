module YModem.Impl.Client

friend YModem.Wire.Generated.Ymodem_packet_data
friend YModem.Wire.Generated.Ymodem_packet

#lang-pulse

(**
  Verified Pulse implementation of the YMODEM *receiver* (client) leaf, the
  executable counterpart of the YModem.Protocol client wire-input step.

  `ymodem_client_recv_block` consumes a full 133-byte YMODEM packet
  SOH | blk | ~blk | data[128] | CRC-16, extracts its 128-byte payload into
  `out_data`, and returns the block number.  It is proved against the
  QuackyDucky/EverParse-generated LowParse wire format: after the call, the
  input `inp` parses (via `YModem.Wire.ymodem_parse`) to some `ymodem_packet`
  `pkt` whose block number is the returned `blk` and whose payload `pkt.data`
  is exactly the bytes written into `out_data`.

  Proof strategy: because the format is total and constant-size 133 bytes, a
  133-byte input always parses to `Some (pkt, Seq.empty)` with
  `ymodem_serialize pkt == inp` (`ymodem_parse_133`).  The output fields are then
  read/copied by hand (`blk = inp[1]`, `out_data = inp[3..131]`) and related to
  `pkt.blk` / `pkt.data` through a serializer-layout lemma
  (`ymodem_serialize_layout`).  This requires `friend`-ing the generated
  modules, hence the accompanying `YModem.Impl.Client.fsti` interface.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module LP = LowParse.Spec
module E = FStar.Endianness

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

(* ------------------------------------------------------------------------ *)
(* Pure serializer/parser-layout lemmas (require friend-ing the generated    *)
(* modules).                                                                 *)
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

(* Index/slice form of the layout: pins each byte position of the 133-byte
   serialization to the corresponding packet field. *)
let ymodem_serialize_layout (pkt: ymodem_packet)
  : Lemma (
      let o = ymodem_serialize pkt in
      Seq.length o == 133 /\
      Seq.index o 0 == pkt.soh /\
      Seq.index o 1 == pkt.blk /\
      Seq.index o 2 == pkt.blk_complement /\
      Seq.slice o 3 131 == pkt.data /\
      Seq.slice o 131 133 == E.n_to_be 2 (U16.v pkt.crc))
= ymodem_serialize_flat pkt;
  let o = ymodem_serialize pkt in
  Seq.lemma_eq_intro (Seq.slice o 3 131) pkt.data;
  Seq.lemma_eq_intro (Seq.slice o 131 133) (E.n_to_be 2 (U16.v pkt.crc));
  ()

(* Totality: a 133-byte input always parses (the format is total constant-size
   133), and the parse result serializes back to exactly the input. *)
let ymodem_parse_133 (i: Seq.seq U8.t)
  : Lemma (requires Seq.length i == 133)
          (ensures (exists (pkt:ymodem_packet).
             ymodem_parse i == Some (pkt, Seq.empty) /\
             ymodem_serialize pkt == i))
= LP.parser_kind_prop_equiv ymodem_packet_parser_kind ymodem_packet_parser;
  assert (Some? (LP.parse ymodem_packet_parser i));
  let Some (pkt, consumed) = LP.parse ymodem_packet_parser i in
  assert (consumed == 133);
  LP.parsed_data_is_serialize ymodem_packet_serializer i;
  Seq.lemma_eq_elim (Seq.slice i consumed (Seq.length i)) Seq.empty;
  Seq.append_empty_r (LP.serialize ymodem_packet_serializer pkt);
  assert (ymodem_serialize pkt == i);
  lemma_ymodem_parse_serialize_exact pkt;
  ()

(* Package the byte facts the imperative code establishes about the input `i`
   and the extracted payload `o'` into the post-condition existential.  Kept as
   a pure F* lemma (like the Server's `emit_block_serialize_exists`) so the
   parse-witness packet lives in ordinary F*, not the Pulse fn. *)
let recv_block_parse_exists (i o': Seq.seq U8.t) (blk: U8.t)
  : Lemma
    (requires
       Seq.length i == 133 /\ Seq.length o' == 128 /\
       blk == Seq.index i 1 /\
       (forall (j:nat). j < 128 ==> Seq.index o' j == Seq.index i (3 + j)))
    (ensures
       (exists (pkt:ymodem_packet) (rest:Seq.seq U8.t).
          ymodem_parse i == Some (pkt, rest) /\ blk == pkt.blk /\ o' == pkt.data))
= ymodem_parse_133 i;
  eliminate exists (pkt:ymodem_packet).
    (ymodem_parse i == Some (pkt, Seq.empty) /\ ymodem_serialize pkt == i)
  returns (exists (pkt:ymodem_packet) (rest:Seq.seq U8.t).
             ymodem_parse i == Some (pkt, rest) /\ blk == pkt.blk /\ o' == pkt.data)
  with _hpf.
  ( ymodem_serialize_layout pkt;
    Seq.lemma_eq_intro o' pkt.data;
    introduce exists (pkt2:ymodem_packet) (rest:Seq.seq U8.t).
      ymodem_parse i == Some (pkt2, rest) /\ blk == pkt2.blk /\ o' == pkt2.data
    with pkt Seq.empty
    and () )

#pop-options

(* ------------------------------------------------------------------------ *)
(* The verified leaf.                                                        *)
(* ------------------------------------------------------------------------ *)

(* BoundedIntegers is opened only here so its overloaded `+`/`<` apply to the
   SizeT loop arithmetic below, and do NOT hijack the Prims nat arithmetic in
   the pure lemmas above. *)
open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
fn ymodem_client_recv_block
  (inp: array U8.t)
  (out_data: array U8.t)
  requires
    pts_to inp 'i **
    pts_to out_data 'o **
    pure (Seq.length 'i == 133 /\ Seq.length 'o == 128)
  returns blk: U8.t
  ensures
    pts_to inp 'i **
    (exists* (o':Seq.seq U8.t).
       pts_to out_data o' **
       pure (Seq.length o' == 128 /\
             (exists (pkt:ymodem_packet) (rest:Seq.seq U8.t).
                ymodem_parse 'i == Some (pkt, rest) /\ blk == pkt.blk /\ o' == pkt.data)))
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
