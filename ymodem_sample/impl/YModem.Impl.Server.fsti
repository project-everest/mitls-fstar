module YModem.Impl.Server

(**
  Interface for the verified YMODEM *sender* (server) leaf.

  NOTE (architecture): this `.fsti` is required so that `YModem.Impl.Server.fst`
  may `friend` the QuackyDucky/EverParse-generated wire modules
  (`YModem.Wire.Generated.Ymodem_packet[_data]`) and decompose the serializer in
  a local layout lemma — `friend` is only permitted in modules that have an
  interface.  Only the single executable leaf `ymodem_server_emit_block` is
  exported; all proof helpers stay private to the `.fst`.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Seq = FStar.Seq

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

(* Build a YMODEM data block (block number `blk`) from a 128-byte file chunk;
   `out` receives the full 133-byte packet SOH | blk | ~blk | data[128] | CRC-16.
   The post-condition proves that `out` holds the LowParse serialization of a
   `ymodem_packet` whose 128-byte payload is exactly the input `data`. *)
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
