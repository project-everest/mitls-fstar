module YModem.Impl.Codec

(**
  Interface for the verified YMODEM data-block codec leaves, proved against the
  new tagged-union wire format `YModem.Wire.Generated.Ymodem_message.ymodem_message`.

  NOTE (architecture): this `.fsti` is required so that `YModem.Impl.Codec.fst`
  may `friend` the QuackyDucky/EverParse-generated wire modules
  (`YModem.Wire.Generated.Ymodem_{tag,soh_body_data,soh_body,message}`) and
  decompose the `serialize_sum`/`serialize_synth`/`serialize_nondep_then`
  serializer in local layout lemmas — `friend` is only permitted in modules that
  have an interface.  Only the two executable leaves `ymodem_emit_data_block` and
  `ymodem_recv_data_block` are exported; all proof helpers stay private to the
  `.fst`.

  These are the codecs that the interop wrappers link against; they take/return
  plain `array U8.t` buffers and extract to clean C.  The control bytes (EOT
  0x04, ACK 0x06, NAK 0x15, CAN 0x18, C 0x43) carry an empty body, so the
  wrappers write/compare those literal bytes directly and need no codec.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Seq = FStar.Seq

open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire

(* Build a YMODEM SOH data block (block number `blk`) from a 128-byte file
   chunk; `out` receives the full 133-byte packet
   SOH | blk | ~blk | data[128] | CRC-16.  The post-condition proves that `out`
   holds the LowParse serialization of a `Body_soh body` message whose 128-byte
   payload `body.data` is exactly the input `data` and whose block number
   `body.blk` is exactly `blk`. *)
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

(* Extract the 128-byte payload of a 133-byte SOH data packet into `out_data`,
   returning the block number.  The caller guarantees (via the `'i.[0] == 0x01`
   pre-condition) that `inp` is a leading-SOH data packet — the wrapper only
   calls this after reading a 0x01 lead byte.  The post-condition proves that
   `inp` parses (via the LowParse `ymodem_parse`) to some `Body_soh body` whose
   block number is exactly the returned `blk` and whose 128-byte payload is
   exactly the bytes written into `out_data`. *)
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
