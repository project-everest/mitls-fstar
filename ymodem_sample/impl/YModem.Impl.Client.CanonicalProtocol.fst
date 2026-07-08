module YModem.Impl.Client.CanonicalProtocol

(**
  YMODEM *client* (receiver) as an instance of the state-machine implementation
  type class `Common.ProtocolImplementation.protocol_implementation`, the
  executable refinement of the `YModem.Protocol.ymodem_client_wfsm` specification
  state machine.

  This is the operational counterpart of the client state machine: its
  `pi_process_network` handler validates an incoming 133-byte YMODEM packet and
  extracts its 128-byte payload by driving the packet parser of
  `YModem.Impl.Client`:

    * `pi_process_network` calls `ymodem_client_recv_block`, whose returned block
      number the driver interprets (block 0 = header carrying the file name and
      declared length; blocks 1, 2, ... = file data, reassembled and truncated to
      the declared length at end-of-file).

  The receiver's local events (`YmodemClientStart`, declaring the file name and
  length learned from the header, and `YmodemClientEot`, completion) produce no
  wire output, so `pi_process_local` is a stub.

  This is a SKELETON mirroring `Calc.Server.CanonicalProtocol`: the invariant and
  snapshot are `emp`, and the ghost obligations and the process-function
  postconditions are discharged with `admit ()`.  Its purpose is to place the
  packet-parsing helper *inside* a genuine `protocol_implementation` instance
  (rather than as a free-standing function), pinning the refinement structure and
  the extracted C ABI for the interoperability wrappers.  A verified
  implementation would replace the `emp` invariants with a reachable-trace
  invariant and the `admit ()`s with real proofs relating `out_data` to the
  parsed `ymodem_packet`.
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
module Seq = FStar.Seq

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_packet
open YModem.Impl.Client

(* The receiver implementation handle.  A verified implementation would carry the
   concrete receiver state and a ghost progress witness; the skeleton threads the
   spec state ghostly and needs nothing at runtime. *)
type ymodem_client_impl = unit

(* SKELETON invariant / snapshot: `emp`. *)
[@@pulse_unfold]
let ymodem_client_inv
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop = emp

[@@pulse_unfold]
let ymodem_client_snap
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop = emp

(* Network frame: a 128-byte scratch buffer that `pi_process_network` fills with
   the extracted packet payload. *)
noeq
type ymodem_client_network_frame = {
  ycnf_data : array U8.t;   // 128-byte extracted payload
}

[@@pulse_unfold]
let ymodem_client_network_frame_pre
  (frame:ymodem_client_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.ycnf_data d ** pure (Seq.length d == 128)) **
  pure (Seq.length input_contents == 133)

[@@pulse_unfold]
let ymodem_client_network_frame_post
  (frame:ymodem_client_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_client_state) (st1:YP.ymodem_client_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop = emp

(* Local frame: the receiver's local events (start / EOT) emit no packet. *)
type ymodem_client_local_frame = unit

[@@pulse_unfold]
let ymodem_client_local_frame_pre
  (ev:YP.ymodem_client_local)
  (frame:ymodem_client_local_frame)
  (st0:YP.ymodem_client_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop = emp

[@@pulse_unfold]
let ymodem_client_local_frame_post
  (ev:YP.ymodem_client_local)
  (frame:ymodem_client_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_client_state) (st1:YP.ymodem_client_state)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop = emp

(* ── ghost obligations (SKELETON: admitted) ──────────────────────────────── *)

ghost fn ymodem_client_invariant_valid
  (i:ymodem_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased YP.ymodem_client_state)
requires ymodem_client_inv i received sent st
ensures
  ymodem_client_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (YP.ymodem_client_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  admit()
}

ghost fn ymodem_client_take_snapshot
  (i:ymodem_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased YP.ymodem_client_state)
requires ymodem_client_inv i received sent st
ensures
  ymodem_client_inv i received sent st **
  ymodem_client_snap i received sent st
{
  admit()
}

ghost fn ymodem_client_recall_snapshot
  (i:ymodem_client_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased YP.ymodem_client_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased YP.ymodem_client_state)
requires
  ymodem_client_snap i snapshot_received snapshot_sent snapshot_state **
  ymodem_client_inv i current_received current_sent current_state
ensures
  ymodem_client_snap i snapshot_received snapshot_sent snapshot_state **
  ymodem_client_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (YP.ymodem_client_wfsm)
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

(* ── network processing: drive the packet-parsing helper ─────────────────── *)

fn ymodem_client_process_network
  (i:ymodem_client_impl)
  (frame:ymodem_client_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased YP.ymodem_client_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  ymodem_client_inv i received0 sent0 st0 **
  ymodem_client_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_client_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list ymodem_packet)
                (local_outputs:list unit).
  ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  ymodem_client_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (YP.ymodem_client_wfsm)
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
  let blk = ymodem_client_recv_block input frame.ycnf_data;
  admit()
}

(* ── local processing (SKELETON stub: receiver local events emit no packet) ─ *)

fn ymodem_client_process_local
  (i:ymodem_client_impl)
  (ev:YP.ymodem_client_local)
  (frame:ymodem_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased YP.ymodem_client_state)
  (old_out:erased TCP.bytes)
requires
  ymodem_client_inv i received0 sent0 st0 **
  ymodem_client_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (SZ.v out_len == Seq.length old_out)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_client_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list ymodem_packet)
                (local_outputs:list unit).
  ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  ymodem_client_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1)
    wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (YP.ymodem_client_wfsm)
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
  admit()
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let ymodem_client_protocol_implementation
  : CPI.protocol_implementation
      ymodem_client_impl
      YP.ymodem_client_state
      ymodem_packet
      YP.ymodem_client_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> YP.ymodem_client_wfsm);
    CPI.pi_invariant = ymodem_client_inv;
    CPI.pi_snapshot = ymodem_client_snap;
    CPI.pi_network_frame = ymodem_client_network_frame;
    CPI.pi_network_frame_pre = ymodem_client_network_frame_pre;
    CPI.pi_network_frame_post = ymodem_client_network_frame_post;
    CPI.pi_local_frame = ymodem_client_local_frame;
    CPI.pi_local_frame_pre = ymodem_client_local_frame_pre;
    CPI.pi_local_frame_post = ymodem_client_local_frame_post;
    CPI.pi_invariant_valid = ymodem_client_invariant_valid;
    CPI.pi_take_snapshot = ymodem_client_take_snapshot;
    CPI.pi_recall_snapshot = ymodem_client_recall_snapshot;
    CPI.pi_process_network = ymodem_client_process_network;
    CPI.pi_process_local = ymodem_client_process_local;
  }
