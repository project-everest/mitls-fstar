module YModem.Impl.Control

(**
  Wire-encoding facts for the single-byte CONTROL messages of the YMODEM
  tagged-union wire format `YModem.Wire.Generated.Ymodem_message.ymodem_message`.

  The five control constructors — `Body_eot`, `Body_ack`, `Body_nak`,
  `Body_can`, `Body_crc_c` — all carry an EMPTY body (`ymodem_empty = unit`),
  whose LowParse serializer emits ZERO bytes.  Hence a control message
  serializes to a SINGLE tag byte:

    serialize ymodem_message_serializer (Body_ack ()) == Seq.create 1 0x06

  and, more generally, `ymodem_serialize m == Seq.create 1 (ymodem_control_byte m)`
  for any non-SOH `m`.  Both the client and server
  `Common.ProtocolImplementation.protocol_implementation` instances need these
  layout/round-trip facts to justify writing/comparing the literal control
  bytes directly (EOT 0x04, ACK 0x06, NAK 0x15, CAN 0x18, 'C' 0x43).

  NOTE (architecture): the accompanying `YModem.Impl.Control.fst` must `friend`
  the QuackyDucky/EverParse-generated wire modules
  (`YModem.Wire.Generated.Ymodem_{tag,message}`) so it can decompose the
  `serialize_sum`/`serialize_enum_key` serializer — `friend` is only permitted
  in modules that have an interface, hence this `.fsti`.

  This module is VERIFIED but NOT extracted to C — everything here is
  `noextract` pure specification (the `ymodem_control_byte` map is a spec
  helper, and all the exported facts are `Lemma`s, which produce no code).
**)

module Seq = FStar.Seq
module U8 = FStar.UInt8
module TCP = Common.TCP
module WF = Common.WireFormat

open YModem.Wire.Generated.Ymodem_message
open YModem.Wire

(* The single wire byte of a (non-SOH) control message: the enum repr of its
   tag (cf. `YModem.Wire.Generated.Ymodem_tag.ymodem_tag_enum`). *)
noextract
let ymodem_control_byte (m:ymodem_message{~(Body_soh? m)}) : U8.t =
  match m with
  | Body_eot _ -> 4uy
  | Body_ack _ -> 6uy
  | Body_nak _ -> 21uy
  | Body_can _ -> 24uy
  | Body_crc_c _ -> 67uy

(* (2) A control message serializes to exactly its single tag byte. *)
noextract
val lemma_serialize_control (m:ymodem_message{~(Body_soh? m)})
  : Lemma (ensures ymodem_serialize m == Seq.create 1 (ymodem_control_byte m))

(* (3) The single-element `Common.WireFormat.serialize_all` of a control
   message is the same single byte. *)
noextract
val lemma_serialize_all_control (m:ymodem_message{~(Body_soh? m)})
  : Lemma (ensures
      WF.serialize_all ymodem_wire_format [m] == Seq.create 1 (ymodem_control_byte m))

(* (4) Parsing the single control byte followed by an arbitrary `rest`
   residual recovers the message and leaves `rest` unconsumed. *)
noextract
val lemma_parse_control (m:ymodem_message{~(Body_soh? m)}) (rest:TCP.bytes)
  : Lemma (ensures
      ymodem_parse (Seq.append (Seq.create 1 (ymodem_control_byte m)) rest) == Some (m, rest))

(* (4, corollary) Parsing exactly the single control byte recovers the message
   with no residual. *)
noextract
val lemma_parse_control_exact (m:ymodem_message{~(Body_soh? m)})
  : Lemma (ensures
      ymodem_parse (Seq.create 1 (ymodem_control_byte m)) == Some (m, Seq.empty))
