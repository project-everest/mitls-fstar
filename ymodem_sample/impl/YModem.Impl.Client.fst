module YModem.Impl.Client

(**
  Skeleton Pulse implementation of the YMODEM *receiver* (client) side, the
  executable counterpart of the YModem.Protocol client state machine.

  This is the operational entry point a receiver driver (an `rb`-style program)
  calls to process each incoming YMODEM packet:

    * `ymodem_client_recv_block` validates a 133-byte packet
      (SOH | blk | ~blk | data[128] | CRC-16) and extracts its 128-byte payload
      into `out_data`, returning the packet's block number — the executable form
      of the client state machine's wire-input step.

  The driver interprets the returned block number: block 0 is the header (its
  payload holds the NUL-terminated file name and ASCII length), blocks 1, 2, ...
  are file data (accumulated and, at end-of-file, truncated to the declared
  length).  EOT (0x04) and the ACK/NAK/'C' handshake are single control bytes
  handled directly by the driver.

  This is a SKELETON: the body is `admit ()`, so the code type-checks and extracts
  to C with the intended signature, but the validation and extraction are not yet
  implemented or proved.  It exists to pin the C ABI for the interoperability
  wrappers; a verified implementation would replace the admit and strengthen the
  postcondition to relate `out_data` to the parsed `ymodem_packet` of
  YModem.Wire.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Seq = FStar.Seq

(* Validate a 133-byte YMODEM packet and extract its 128-byte payload into
   `out_data`, returning the packet's block number.  SKELETON: body admitted. *)
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
    (exists* o'. pts_to out_data o' ** pure (Seq.length o' == 128))
{
  admit()
}
