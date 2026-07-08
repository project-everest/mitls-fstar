module YModem.Impl.Server

(**
  Skeleton Pulse implementation of the YMODEM *sender* (server) side, the
  executable counterpart of the YModem.Protocol server state machine.

  These are the operational entry points a sender driver (an `sb`-style program)
  calls to frame a file into YMODEM packets:

    * `ymodem_server_emit_header` builds the header block (block 0), whose 128-byte
      payload carries the NUL-terminated file name followed by the ASCII file
      length — the YMODEM equivalent of the YmodemStart local event that declares
      the file name and length;
    * `ymodem_server_emit_block` builds a data block (block 1, 2, ...) from a
      128-byte file chunk — the executable form of the YmodemSendBlock step.

  Each builds a full 133-byte packet: SOH | blk | ~blk | data[128] | CRC-16.
  End-of-file (EOT, 0x04) and the ACK/NAK/'C' handshake are single control bytes
  handled directly by the driver.

  This is a SKELETON: the function bodies are `admit ()`, so the code type-checks
  and extracts to C with the intended signatures, but the packet construction
  (including the CRC) is not yet implemented or proved.  It exists to pin the C
  ABI for the interoperability wrappers; a verified implementation would replace
  the admits and strengthen the postconditions to relate `out` to the serialized
  `ymodem_packet` of YModem.Wire.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

(* Build the YMODEM header block (block 0): its 128-byte payload holds the
   NUL-terminated file name and the ASCII file length; `out` receives the full
   133-byte packet.  SKELETON: body admitted. *)
fn ymodem_server_emit_header
  (name: array U8.t)
  (name_len: SZ.t)
  (file_len: U32.t)
  (out: array U8.t)
  requires
    pts_to name 'n **
    pts_to out 'o **
    pure (SZ.v name_len <= Seq.length 'n /\ Seq.length 'o == 133)
  ensures
    pts_to name 'n **
    (exists* o'. pts_to out o' ** pure (Seq.length o' == 133))
{
  admit()
}

(* Build a YMODEM data block (block number `blk`) from a 128-byte file chunk;
   `out` receives the full 133-byte packet.  SKELETON: body admitted. *)
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
    (exists* o'. pts_to out o' ** pure (Seq.length o' == 133))
{
  admit()
}
