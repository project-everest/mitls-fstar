module YModem.Impl.Server.CanonicalProtocol

(**
  YMODEM *server* (sender) as an instance of the state-machine implementation
  type class `Common.ProtocolImplementation.protocol_implementation`, the
  executable refinement of the `YModem.Protocol.ymodem_server_wfsm` specification
  state machine.

  This is the operational counterpart of the server state machine: its
  `pi_process_local` handler dispatches on the server local events and drives the
  packet-framing helpers of `YModem.Impl.Server`:

    * `YmodemStart` (header block 0, whose 128-byte payload declares the file
      name and length) calls `ymodem_server_emit_block 0uy`;
    * `YmodemSendBlock` (a 128-byte data block) calls `ymodem_server_emit_block`;
    * `YmodemEot` / `YmodemAbort` emit no data packet (EOT / CAN are single
      control bytes handled by the driver).

  In the download model the sender consumes no wire input, so `pi_process_network`
  is a stub.

  This is a SKELETON mirroring the shape of `Calc.Server.CanonicalProtocol`: the
  invariant and snapshot are `emp`, the ghost obligations and the process-function
  postconditions are discharged with `admit ()`.  Its purpose is to place the
  packet-framing helpers *inside* a genuine `protocol_implementation` instance
  (rather than as free-standing functions), pinning the refinement structure and
  the extracted C ABI for the interoperability wrappers.  A verified
  implementation would replace the `emp` invariants with a reachable-trace
  invariant (as `canonical_server_exactly` does) and the `admit ()`s with real
  proofs relating `out` to the serialized `ymodem_packet`.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module SM = Common.StateMachine
module SZ = FStar.SizeT
module TCP = Common.TCP
module WFSM = Common.WireFormatStateMachine
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_packet
open YModem.Impl.Server

(* The sender implementation handle.  A verified implementation would carry the
   concrete sender state and a ghost progress witness (cf. calc's
   `canonical_server`); the skeleton threads the spec state ghostly and needs
   nothing at runtime. *)
type ymodem_server_impl = unit

(* SKELETON invariant / snapshot: `emp`.  A verified implementation would tie the
   heap resources to the reachable-trace invariant, as calc's
   `canonical_server_exactly` / `canonical_server_snapshot` do. *)
[@@pulse_unfold]
let ymodem_server_inv
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop = emp

[@@pulse_unfold]
let ymodem_server_snap
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop = emp

(* Network frame: the sender consumes no wire input in this download model. *)
type ymodem_server_network_frame = unit

[@@pulse_unfold]
let ymodem_server_network_frame_pre
  (frame:ymodem_server_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop = emp

[@@pulse_unfold]
let ymodem_server_network_frame_post
  (frame:ymodem_server_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop = emp

(* Local frame: the 128-byte payload buffer (the NUL-terminated file name for the
   header block 0, or a file chunk for a data block) plus the header parameters
   and the block number.  `pi_process_local` hands this buffer to the emit
   helpers. *)
noeq
type ymodem_server_local_frame = {
  yslf_buf      : array U8.t;   // 128-byte payload
  yslf_blk      : U8.t;         // block number (data blocks)
  yslf_name_len : SZ.t;         // file-name length (header)
  yslf_file_len : U32.t;        // declared file length (header)
}

[@@pulse_unfold]
let ymodem_server_local_frame_pre
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (st0:YP.ymodem_server_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.yslf_buf d **
     pure (Seq.length d == 128 /\ SZ.v frame.yslf_name_len <= 128)) **
  pure (Seq.length old_out == 133)

[@@pulse_unfold]
let ymodem_server_local_frame_post
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop = emp

(* ── ghost obligations (SKELETON: admitted) ──────────────────────────────── *)

ghost fn ymodem_server_invariant_valid
  (i:ymodem_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased YP.ymodem_server_state)
requires ymodem_server_inv i received sent st
ensures
  ymodem_server_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (YP.ymodem_server_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  admit()
}

ghost fn ymodem_server_take_snapshot
  (i:ymodem_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased YP.ymodem_server_state)
requires ymodem_server_inv i received sent st
ensures
  ymodem_server_inv i received sent st **
  ymodem_server_snap i received sent st
{
  admit()
}

ghost fn ymodem_server_recall_snapshot
  (i:ymodem_server_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased YP.ymodem_server_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased YP.ymodem_server_state)
requires
  ymodem_server_snap i snapshot_received snapshot_sent snapshot_state **
  ymodem_server_inv i current_received current_sent current_state
ensures
  ymodem_server_snap i snapshot_received snapshot_sent snapshot_state **
  ymodem_server_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (YP.ymodem_server_wfsm)
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  admit()
}

(* ── network processing (SKELETON stub: the sender has no wire input) ─────── *)

fn ymodem_server_process_network
  (i:ymodem_server_impl)
  (frame:ymodem_server_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased YP.ymodem_server_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  ymodem_server_inv i received0 sent0 st0 **
  ymodem_server_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_server_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list ymodem_packet)
                (local_outputs:list unit).
  ymodem_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  ymodem_server_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (YP.ymodem_server_wfsm)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      out_contents
      out_len
      received0
      sent0
      st0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs)
{
  admit()
}

(* ── local processing: drive the packet-framing helpers ──────────────────── *)

fn ymodem_server_process_local
  (i:ymodem_server_impl)
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased YP.ymodem_server_state)
  (old_out:erased TCP.bytes)
requires
  ymodem_server_inv i received0 sent0 st0 **
  ymodem_server_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (SZ.v out_len == Seq.length old_out)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_server_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list ymodem_packet)
                (local_outputs:list unit).
  ymodem_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  ymodem_server_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1)
    wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (YP.ymodem_server_wfsm)
      ev
      old_out
      out_contents
      out_len
      received0
      sent0
      st0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
{
  match ev {
    YP.YmodemStart _ _ _ -> {
      ymodem_server_emit_block 0uy frame.yslf_buf out;
      admit()
    }
    YP.YmodemSendBlock -> {
      ymodem_server_emit_block frame.yslf_blk frame.yslf_buf out;
      admit()
    }
    YP.YmodemEot -> {
      admit()
    }
    YP.YmodemAbort -> {
      admit()
    }
  }
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let ymodem_server_protocol_implementation
  : CPI.protocol_implementation
      ymodem_server_impl
      YP.ymodem_server_state
      ymodem_packet
      YP.ymodem_server_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> YP.ymodem_server_wfsm);
    CPI.pi_invariant = ymodem_server_inv;
    CPI.pi_snapshot = ymodem_server_snap;
    CPI.pi_network_frame = ymodem_server_network_frame;
    CPI.pi_network_frame_pre = ymodem_server_network_frame_pre;
    CPI.pi_network_frame_post = ymodem_server_network_frame_post;
    CPI.pi_local_frame = ymodem_server_local_frame;
    CPI.pi_local_frame_pre = ymodem_server_local_frame_pre;
    CPI.pi_local_frame_post = ymodem_server_local_frame_post;
    CPI.pi_invariant_valid = ymodem_server_invariant_valid;
    CPI.pi_take_snapshot = ymodem_server_take_snapshot;
    CPI.pi_recall_snapshot = ymodem_server_recall_snapshot;
    CPI.pi_process_network = ymodem_server_process_network;
    CPI.pi_process_local = ymodem_server_process_local;
  }
