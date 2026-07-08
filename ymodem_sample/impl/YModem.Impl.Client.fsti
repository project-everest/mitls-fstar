module YModem.Impl.Client

(**
  Interface for the verified YMODEM *receiver* (client) leaf.

  NOTE (architecture): this `.fsti` is required so that `YModem.Impl.Client.fst`
  may `friend` the QuackyDucky/EverParse-generated wire modules
  (`YModem.Wire.Generated.Ymodem_packet[_data]`) and decompose the parser in
  local layout/totality lemmas — `friend` is only permitted in modules that have
  an interface.  Only the single executable leaf `ymodem_client_recv_block` is
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

(* Validate a 133-byte YMODEM packet and extract its 128-byte payload into
   `out_data`, returning the packet's block number.  The post-condition proves
   that `inp` parses (via the LowParse `ymodem_parse`) to some `ymodem_packet`
   whose block number is exactly the returned `blk` and whose 128-byte payload
   is exactly the bytes written into `out_data`. *)
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
