module YModem.Impl.Control

friend YModem.Wire.Generated.Ymodem_tag
friend YModem.Wire.Generated.Ymodem_message

(**
  Proofs of the CONTROL-message wire facts declared in the interface.

  Proof recipe (mirroring the SOH split `ymodem_serialize_soh_split` in
  `YModem.Impl.Codec.fst`, but SIMPLER because the control bodies are empty):

    serialize ymodem_message_serializer (Body_ack ())
      == serialize (serialize_enum_key _ ymodem_tag_repr_serializer ymodem_tag_enum) Ack
           `Seq.append`
         serialize ymodem_empty_serializer ()              -- [serialize_sum_eq]
      == serialize ymodem_tag_repr_serializer 0x06uy `Seq.append` Seq.empty
                                                           -- [serialize_enum_key_eq
                                                           --  + enum_repr_of_key ..Ack == 0x06]
      == Seq.create 1 0x06uy `Seq.append` Seq.empty        -- [serialize_u8_spec]
      == Seq.create 1 0x06uy                               -- [append_empty_r]

  The empty-body fact `serialize ymodem_empty_serializer () == Seq.empty` is
  obtained WITHOUT friend-ing the empty module, from the interface-exported
  `ymodem_empty_bytesize_eqn` (length 0) + `Seq.lemma_empty`.

  The parse facts combine (2) with the already-proven round-trip laws
  `YModem.Wire.lemma_ymodem_parse_serialize_{prefix,exact}`, rewriting
  `ymodem_serialize m` to the single control byte.
**)

module Seq = FStar.Seq
module U8 = FStar.UInt8
module TCP = Common.TCP
module WF = Common.WireFormat
module LP = LowParse.Spec
module LPI = LowParse.Spec.AllIntegers

open YModem.Wire.Generated.Ymodem_tag
open YModem.Wire.Generated.Ymodem_empty
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

(* The empty case body contributes zero bytes.  Uses only the interface-exported
   `ymodem_empty_bytesize_eqn` (which pins the serialized length to 0), so no
   `friend` of the empty module is needed. *)
noextract
let ymodem_empty_serialize_is_empty (x: ymodem_empty)
  : Lemma (LP.serialize ymodem_empty_serializer x == Seq.empty)
= ymodem_empty_bytesize_eqn x;
  Seq.lemma_empty (LP.serialize ymodem_empty_serializer x)

(* ---- Per-constructor sum-split lemmas (one enum repr each). --------------- *)

noextract
let ymodem_serialize_eot (u: ymodem_empty)
  : Lemma (ymodem_serialize (Body_eot u) == Seq.create 1 4uy)
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_eot u);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Eot;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Eot == 4uy);
  LP.serialize_u8_spec 4uy;
  ymodem_empty_serialize_is_empty u;
  Seq.append_empty_r (Seq.create 1 4uy)

noextract
let ymodem_serialize_ack (u: ymodem_empty)
  : Lemma (ymodem_serialize (Body_ack u) == Seq.create 1 6uy)
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_ack u);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Ack;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Ack == 6uy);
  LP.serialize_u8_spec 6uy;
  ymodem_empty_serialize_is_empty u;
  Seq.append_empty_r (Seq.create 1 6uy)

noextract
let ymodem_serialize_nak (u: ymodem_empty)
  : Lemma (ymodem_serialize (Body_nak u) == Seq.create 1 21uy)
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_nak u);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Nak;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Nak == 21uy);
  LP.serialize_u8_spec 21uy;
  ymodem_empty_serialize_is_empty u;
  Seq.append_empty_r (Seq.create 1 21uy)

noextract
let ymodem_serialize_can (u: ymodem_empty)
  : Lemma (ymodem_serialize (Body_can u) == Seq.create 1 24uy)
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_can u);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Can;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Can == 24uy);
  LP.serialize_u8_spec 24uy;
  ymodem_empty_serialize_is_empty u;
  Seq.append_empty_r (Seq.create 1 24uy)

noextract
let ymodem_serialize_crc_c (u: ymodem_empty)
  : Lemma (ymodem_serialize (Body_crc_c u) == Seq.create 1 67uy)
= assert_norm (LP.parse_sum_kind (LP.get_parser_kind ymodem_tag_repr_parser) ymodem_message_sum parse_ymodem_message_cases == ymodem_message_parser_kind);
  LP.serialize_sum_eq ymodem_message_sum ymodem_tag_repr_serializer serialize_ymodem_message_cases (Body_crc_c u);
  LP.serialize_enum_key_eq ymodem_tag_repr_serializer ymodem_tag_enum Crc_c;
  assert_norm (LP.enum_repr_of_key ymodem_tag_enum Crc_c == 67uy);
  LP.serialize_u8_spec 67uy;
  ymodem_empty_serialize_is_empty u;
  Seq.append_empty_r (Seq.create 1 67uy)

#pop-options

(* ---- (2) Generic serialize fact: dispatch to the per-constructor lemma. --- *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"

let lemma_serialize_control m =
  match m with
  | Body_eot u -> ymodem_serialize_eot u
  | Body_ack u -> ymodem_serialize_ack u
  | Body_nak u -> ymodem_serialize_nak u
  | Body_can u -> ymodem_serialize_can u
  | Body_crc_c u -> ymodem_serialize_crc_c u

(* ---- (3) Single-element serialize_all. ----------------------------------- *)

let lemma_serialize_all_control m =
  lemma_serialize_control m;
  calc (==) {
    WF.serialize_all ymodem_wire_format [m];
    == { (* unfold serialize_all/serialize_with_tail (fuel) + wf_serialize field *) }
    Seq.append (ymodem_serialize m) Seq.empty;
    == { Seq.append_empty_r (ymodem_serialize m) }
    ymodem_serialize m;
    == { lemma_serialize_control m }
    Seq.create 1 (ymodem_control_byte m);
  }

(* ---- (4) Parse facts: rewrite the serialized bytes to the control byte and
   reuse the already-proven round-trip laws. -------------------------------- *)

let lemma_parse_control m rest =
  lemma_serialize_control m;
  lemma_ymodem_parse_serialize_prefix m rest

let lemma_parse_control_exact m =
  lemma_serialize_control m;
  lemma_ymodem_parse_serialize_exact m

#pop-options
