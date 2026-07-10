module YModem.Impl.Client.CanonicalProtocol

(**
  YMODEM *client* (receiver) as a verified instance of the state-machine
  implementation type class `Common.ProtocolImplementation.protocol_implementation`,
  the executable refinement of the *reliable-delivery (ARQ)* specification state
  machine `YModem.Protocol.ymodem_client_wfsm`.

  Unlike the prior download-only receiver, the ARQ receiver both CONSUMES a mix
  of wire frames and EMITS wire output:

    * `pi_process_network` dispatches on the framed message in its input buffer
      (the network frame precondition bounds the buffer — a complete 1-byte
      control frame or 133-byte SOH frame — but does NOT assume it is well
      formed; the message identity is recovered from the verified reader / the
      observed lead byte, so an unrecognized frame is handled soundly):
        - a 133-byte SOH data block (lead byte 0x01) is a genuine `StepOk`: it
          drives the verified `YModem.Impl.Codec.ymodem_recv_data_block` leaf to
          extract the 128-byte payload, appends it to the abstract `ycs_received`,
          and EMITS a single ACK byte (0x06);
        - a 1-byte EOT control frame (0x04) is a genuine `StepOk`: it flips the
          status to `FT_Completed` and EMITS an ACK;
        - a 1-byte CAN control frame (0x18) is a genuine `StepOk`: it flips the
          status to `FT_Aborted` and emits NOTHING;
        - anything else (an ACK/NAK/'C' that parses but is not enabled, or any
          frame once the transfer is finished) is a sound `IllegalTransition`
          no-op (the third disjunct of `network_error_refines_state_machine`).

    * `pi_process_local` drives the sole local event `Client_start` faithfully:
      from the freshly-created (un-started) state it is a genuine `StepOk` that
      sets the filename and initialises the receiver; once a filename is known it
      is a sound `IllegalTransition` no-op.

  The instance is backed by a `Pulse.Lib.MonotonicGhostRef` over the reflexive-
  transitive closure of a `WireEvent`-or-`LocalEvent` step relation
  (`YModem.Impl.Client.Log`); the invariant folds the canonical reachable-trace
  predicate (`Log.client_trace_ok`), which refines the (received, sent) byte
  history into a valid state-machine trace via `WFSM.valid_byte_trace`.

  The handle carries a concrete single-cell status vector with FOUR runtime
  values — `0uy` not-yet-started, `1uy` receiving, `2uy` completed, `3uy`
  aborted — tied to the abstract `ycs_status`/`ycs_filename` by the invariant
  (`Log.yc_status_flag_ok`).  This lets both handlers branch on the runtime
  status (and on whether a filename is known) — necessary because the class
  exposes the erased abstract state to a handler only through `pi_invariant`.

  Verified but NOT extracted (a `protocol_implementation` dictionary is not Low-star).
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module SM = Common.StateMachine
module SZ = FStar.SizeT
module TCP = Common.TCP
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module FT = Common.FileTransfer
module U8 = FStar.UInt8
module Seq = FStar.Seq
module L = FStar.List.Tot
module MR = Pulse.Lib.MonotonicGhostRef
module RTC = FStar.ReflexiveTransitiveClosure
module Vec = Pulse.Lib.Vec

module YP = YModem.Protocol
module Log = YModem.Impl.Client.Log
module Codec = YModem.Impl.Codec

open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire
open YModem.Impl.Control

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* ───────────────────────────────────────────────────────────────────────────
   Implementation handle
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_impl = {
  status   : Vec.vec U8.t;                        // single cell: 0/1/2/3 status flag
  progress : MR.mref Log.yc_state_ahead_preorder; // ghost history under the RTC preorder
}

(* The reachable-trace invariant.  The concrete `status` cell carries the runtime
   status flag (both handlers branch on it, and — crucially — on whether a
   filename is known, which the initial `0uy` value encodes); the ghost reference
   holds the log determined by the (received, sent, state) triple; and the byte
   history refines a valid state-machine trace. *)
let ymodem_client_inv
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t).
     Vec.pts_to i.status svs **
     pure (Seq.length svs == 1 /\ Log.yc_status_flag_ok (Seq.index svs 0) st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.client_trace_ok received sent (Log.mk_log received sent st))

(* A monotone snapshot of the progress at a past history. *)
let ymodem_client_snap
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* Network frame: a 128-byte scratch buffer that the SOH case fills with the
   extracted payload.  The frame precondition bounds the input to one complete
   framed message (a 1-byte control or 133-byte SOH frame) and leaves room for
   the 1-byte ACK in the output buffer, but does NOT assume the input is well
   formed. *)
noeq
type ymodem_client_network_frame = {
  ycnf_data : array U8.t;   // 128-byte extracted payload scratch
}

let ymodem_client_network_frame_pre
  (frame:ymodem_client_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.ycnf_data d ** pure (Seq.length d == 128)) **
  pure (
    SZ.v input_len == Seq.length input_contents /\
    SZ.v input_len >= 1 /\
    SZ.v out_len >= 1)

let ymodem_client_network_frame_post
  (frame:ymodem_client_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_client_state) (st1:YP.ymodem_client_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_message) (local_outputs:list unit)
  : slprop =
  (exists* o'. pts_to frame.ycnf_data o' ** pure (Seq.length o' == 128)) **
  pure (
    (wire_outputs == Log.no_wire_outputs \/ wire_outputs == Log.ack_wire_outputs) /\
    local_outputs == Log.no_local_outputs)

(* Local frame: the receiver's local event (start) emits no wire message and
   touches no buffer. *)
type ymodem_client_local_frame = unit

let ymodem_client_local_frame_pre
  (ev:YP.ymodem_client_local)
  (frame:ymodem_client_local_frame)
  (st0:YP.ymodem_client_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop = emp

let ymodem_client_local_frame_post
  (ev:YP.ymodem_client_local)
  (frame:ymodem_client_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_client_state) (st1:YP.ymodem_client_state)
  (wire_outputs:list ymodem_message) (local_outputs:list unit)
  : slprop = emp

(* ── ghost obligations ────────────────────────────────────────────────────── *)

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
  unfold (ymodem_client_inv i received sent st);
  with svs. _;
  Log.lemma_client_trace_ok_valid received sent (Log.mk_log received sent st);
  fold (ymodem_client_inv i received sent st)
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
  unfold (ymodem_client_inv i received sent st);
  with svs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
  fold (ymodem_client_snap i received sent st);
  fold (ymodem_client_inv i received sent st)
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
  unfold (ymodem_client_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (ymodem_client_inv i current_received current_sent current_state);
  with svs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_yc_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_yc_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (ymodem_client_snap i snapshot_received snapshot_sent snapshot_state);
  fold (ymodem_client_inv i current_received current_sent current_state)
}

(* ── network processing: dispatch on the single serialized message ────────── *)

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
                (wire_outputs:list ymodem_message)
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
  unfold (ymodem_client_inv i received0 sent0 st0);
  with svs. _;
  let s = Vec.op_Array_Access i.status 0sz;
  unfold (ymodem_client_network_frame_pre frame input input_len out out_len input_contents old_out);
  with d0. _;
  let lead = input.(0sz);
  if (s = 1uy && input_len = 133sz && lead = 1uy) {
    (* SOH data block: StepOk — extract payload, append it, and emit an ACK. *)
    let blk = Codec.ymodem_recv_data_block input frame.ycnf_data;
    with o'. _;
    Log.lemma_soh_parsed (Ghost.reveal input_contents);
    let body = Ghost.hide (Log.ymodem_parsed_soh_body (Ghost.reveal input_contents));
    let st1 = Ghost.hide (Log.soh_next_state (Ghost.reveal st0) (Ghost.reveal body));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Seq.create 1 6uy));
    out.(0sz) <- 6uy;
    with out_contents. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
    Log.lemma_yc_soh_advance received0 sent0 st0 (Ghost.reveal body);
    RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
    fold (ymodem_client_network_frame_post
      frame Log.soh_result input_contents input_len old_out (Ghost.reveal out_contents)
      st0 (Ghost.reveal st1) (Ghost.reveal input_contents)
      Log.ack_wire_outputs Log.no_local_outputs);
    Log.lemma_yc_network_soh_step_ok
      input_contents input_len old_out (Ghost.reveal out_contents) out_len
      received0 sent0 st0 received1 sent1 st1 (Ghost.reveal body);
    Log.soh_result
  } else if (s = 1uy && input_len = 1sz && lead = 4uy) {
    (* EOT: StepOk — flip status to Completed, emit an ACK. *)
    Log.lemma_input_is_serialize_eot (Ghost.reveal input_contents);
    let st1 = Ghost.hide (Log.eot_next_state (Ghost.reveal st0));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Seq.create 1 6uy));
    out.(0sz) <- 6uy;
    with out_contents. _;
    Vec.op_Array_Assignment i.status 0sz 2uy;
    with svs2. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
    Log.lemma_yc_eot_advance received0 sent0 st0;
    RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
    fold (ymodem_client_network_frame_post
      frame Log.eot_result input_contents input_len old_out (Ghost.reveal out_contents)
      st0 (Ghost.reveal st1) (Ghost.reveal input_contents)
      Log.ack_wire_outputs Log.no_local_outputs);
    Log.lemma_yc_network_eot_step_ok
      input_contents input_len old_out (Ghost.reveal out_contents) out_len
      received0 sent0 st0 received1 sent1 st1;
    Log.eot_result
  } else if (s = 1uy && input_len = 1sz && lead = 24uy) {
    (* CAN: StepOk — flip status to Aborted, emit nothing. *)
    Log.lemma_input_is_serialize_can (Ghost.reveal input_contents);
    let st1 = Ghost.hide (Log.can_next_state (Ghost.reveal st0));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    Vec.op_Array_Assignment i.status 0sz 3uy;
    with svs2. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_yc_can_advance received0 sent0 st0;
    RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    fold (ymodem_client_network_frame_post
      frame Log.can_result input_contents input_len old_out (Ghost.reveal old_out)
      st0 (Ghost.reveal st1) (Ghost.reveal input_contents)
      Log.no_wire_outputs Log.no_local_outputs);
    Log.lemma_yc_network_can_step_ok
      input_contents input_len old_out (Ghost.reveal old_out) out_len
      received0 sent0 st0 received1 sent0 st1;
    Log.can_result
  } else {
    (* Not enabled: a sound IllegalTransition no-op. *)
    Log.lemma_yc_network_noop
      input_contents input_len old_out (Ghost.reveal old_out) out_len received0 sent0 st0;
    fold (ymodem_client_inv i received0 sent0 st0);
    fold (ymodem_client_network_frame_post
      frame Log.illegal_result input_contents input_len old_out (Ghost.reveal old_out)
      st0 (Ghost.reveal st0) Seq.empty
      Log.no_wire_outputs Log.no_local_outputs);
    Log.illegal_result
  }
}

(* ── local processing: drive Client_start faithfully ──────────────────────── *)

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
                (wire_outputs:list ymodem_message)
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
  unfold (ymodem_client_local_frame_pre ev frame st0 out out_len old_out);
  unfold (ymodem_client_inv i received0 sent0 st0);
  with svs. _;
  let s = Vec.op_Array_Access i.status 0sz;
  match ev {
    YP.Client_start filename len -> {
      if (s = 0uy) {
        (* Not-yet-started (filename == None): a genuine StepOk that initialises
           the receiver and flips the status cell to 1uy (receiving). *)
        let st1 = Ghost.hide (Log.start_next_state filename len);
        Vec.op_Array_Assignment i.status 0sz 1uy;
        with svs2. _;
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_yc_start_advance received0 sent0 st0 filename len;
        RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (ymodem_client_inv i received0 sent0 (Ghost.reveal st1));
        Log.lemma_yc_local_start_step_ok
          old_out old_out out_len received0 sent0 st0 st1 filename len;
        fold (ymodem_client_local_frame_post
          ev frame Log.start_result old_out (Ghost.reveal old_out)
          st0 (Ghost.reveal st1) Log.no_wire_outputs Log.no_local_outputs);
        Log.start_result
      } else {
        (* A filename is already known: a sound IllegalTransition no-op. *)
        Log.lemma_yc_local_illegal ev old_out old_out out_len received0 sent0 st0;
        fold (ymodem_client_inv i received0 sent0 st0);
        fold (ymodem_client_local_frame_post
          ev frame Log.illegal_result old_out (Ghost.reveal old_out)
          st0 (Ghost.reveal st0) Log.no_wire_outputs Log.no_local_outputs);
        Log.illegal_result
      }
    }
  }
}

(* ── constructor: a freshly-created, un-started receiver ──────────────────── *)

fn new_ymodem_client ()
requires emp
returns i:ymodem_client_impl
ensures ymodem_client_inv i Seq.empty Seq.empty YP.ymodem_client_initial **
        pure (Vec.is_full_vec i.status)
{
  let status = Vec.alloc 0uy 1sz;
  let progress =
    MR.alloc #_ #Log.yc_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty YP.ymodem_client_initial);
  let i = { status; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty YP.ymodem_client_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty YP.ymodem_client_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  Log.lemma_initial_trace_ok ();
  fold (ymodem_client_inv i Seq.empty Seq.empty YP.ymodem_client_initial);
  assert (pure (Vec.is_full_vec i.status));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let ymodem_client_protocol_implementation
  : CPI.protocol_implementation
      ymodem_client_impl
      YP.ymodem_client_state
      ymodem_message
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
