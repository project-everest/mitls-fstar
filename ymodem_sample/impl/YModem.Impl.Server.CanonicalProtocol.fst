module YModem.Impl.Server.CanonicalProtocol

(**
  YMODEM *server* (sender) as an instance of the state-machine implementation
  type class `Common.ProtocolImplementation.protocol_implementation`, the
  executable refinement of the `YModem.Protocol.ymodem_server_wfsm` specification
  state machine.

  This is the operational counterpart of the server state machine.  Its
  `pi_process_local` handler dispatches on the server local events and drives the
  packet-framing helper `YModem.Impl.Server.ymodem_server_emit_block`:

    * `YmodemStart` (header block 0, whose 128-byte payload declares the file
      name and length) calls `ymodem_server_emit_block 0uy`; the spec models this
      transition as producing *no* wire output (the header is not part of the
      tracked `sent` stream), so the reported produced length is 0;
    * `YmodemSendBlock` (a 128-byte data block) calls `ymodem_server_emit_block`;
      the emitted 133-byte packet is the single wire output;
    * `YmodemEot` / `YmodemAbort` emit no data packet.

  In the download model the sender consumes NO wire input (`ymodem_server_step`
  maps every `WireEvent` to `False`), so `pi_process_network` is a genuine no-op:
  it reports an `IllegalTransition` that consumes nothing, produces nothing and
  changes no abstract state (the "no progress" disjunct of
  `Common.ProtocolImplementation.network_error_refines_state_machine`).

  Unlike the skeleton it replaces, the invariant / snapshot are the real
  reachable-trace invariant of `YModem.Impl.Server.Log`, and every ghost / process
  obligation is discharged by a genuine proof (no `admit` / `assume`).  All the
  pure trace / monotonic-log / closure reasoning lives in the ordinary-F* helper
  module `YModem.Impl.Server.Log`; this module is the thin Pulse shell that binds
  the heap resources to it, mirroring `Calc.Server.CanonicalProtocol`.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module SM = Common.StateMachine
module SZ = FStar.SizeT
module TCP = Common.TCP
module WFSM = Common.WireFormatStateMachine
module WF = Common.WireFormat
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot
module MR = Pulse.Lib.MonotonicGhostRef
module RTC = FStar.ReflexiveTransitiveClosure
module ID = FStar.IndefiniteDescription
module FT = Common.FileTransfer
module Log = YModem.Impl.Server.Log

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire
open YModem.Impl.Server

(* ── the sender implementation handle ─────────────────────────────────────────

   The sender emit is stateless (`ymodem_server_emit_block` needs no persistent
   concrete state), so the only field is a monotonic ghost reference tracking the
   server *log* (received / sent bytes and abstract state), whose preorder is the
   reflexive-transitive closure of a single local-step relation. *)
noeq
type ymodem_server_impl = {
  ysi_progress : MR.mref Log.ys_log_evolves;
}

(* ── invariant / snapshot ─────────────────────────────────────────────────────

   The invariant owns the ghost log at full permission at the value
   `mk_log received sent st`, together with the pure reachable-trace fact
   `server_trace_ok` (which `Log.lemma_server_trace_ok_valid` turns into the
   framework's `valid_byte_trace`).  The snapshot is a duplicable observation of
   the same log; because `mk_log`'s fields *are* `received / sent / st`, no extra
   pure clause is needed. *)
let ymodem_server_inv
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop =
  MR.pts_to i.ysi_progress #1.0R (Log.mk_log received sent st) **
  pure (Log.server_trace_ok received sent st)

let ymodem_server_snap
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop =
  MR.snapshot i.ysi_progress (Log.mk_log received sent st)

(* ── network frame: the sender consumes no wire input ─────────────────────── *)
type ymodem_server_network_frame = unit

[@@pulse_unfold]
let ymodem_server_network_frame_pre
  (frame:ymodem_server_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop = emp

(* NOTE: deliberately NOT `pulse_unfold`.  Although the body is `emp`, keeping it
   folded lets Pulse pin the `consumed / wire_outputs / local_outputs` existential
   witnesses of `pi_process_network` by matching this application argument-wise. *)
let ymodem_server_network_frame_post
  (frame:ymodem_server_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop = emp

(* ── local frame: the 128-byte payload buffer + the block number ──────────────

   `pi_process_local` hands `yslf_buf` (the header/file chunk) to the emit
   helper.  `local_pre_ok` is the per-event precondition guarding the
   corresponding `ymodem_server_step` transition (e.g. for `YmodemSendBlock` the
   buffer must equal the next pending 128-byte block).  The buffer is returned in
   the frame post. *)
noeq
type ymodem_server_local_frame = {
  yslf_buf : array U8.t;   // 128-byte payload
  yslf_blk : U8.t;         // block number (data blocks)
}

unfold
let local_pre_ok (ev:YP.ymodem_server_local) (st0:YP.ymodem_server_state) (d:TCP.bytes) : prop =
  match ev with
  | YP.YmodemStart filename len plan ->
    st0.yss_filename == None /\ YP.plan_wf plan
  | YP.YmodemSendBlock ->
    Some? st0.yss_filename /\
    st0.yss_status == FT.FT_InProgress /\
    Cons? st0.yss_pending /\
    YP.plan_wf st0.yss_pending /\
    Seq.equal (L.hd st0.yss_pending) d
  | YP.YmodemEot ->
    Some? st0.yss_filename /\
    st0.yss_status == FT.FT_InProgress /\
    st0.yss_pending == []
  | YP.YmodemAbort -> True

let ymodem_server_local_frame_pre
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (st0:YP.ymodem_server_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.yslf_buf d **
     pure (Seq.length d == 128 /\ local_pre_ok ev st0 d)) **
  pure (Seq.length old_out == 133)

let ymodem_server_local_frame_post
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop =
  exists* (d:Seq.seq U8.t). pts_to frame.yslf_buf d

(* ── ghost obligations ────────────────────────────────────────────────────── *)

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
  unfold (ymodem_server_inv i received sent st);
  Log.lemma_server_trace_ok_valid received sent st;
  fold (ymodem_server_inv i received sent st)
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
  unfold (ymodem_server_inv i received sent st);
  MR.take_snapshot i.ysi_progress (Log.mk_log received sent st);
  fold (ymodem_server_snap i received sent st);
  fold (ymodem_server_inv i received sent st)
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
  unfold (ymodem_server_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (ymodem_server_inv i current_received current_sent current_state);
  MR.recall_snapshot i.ysi_progress;
  Log.lemma_ys_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_ys_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  assert (pure (CPI.histories_ahead
    (Ghost.reveal snapshot_received)
    (Ghost.reveal snapshot_sent)
    (Ghost.reveal current_received)
    (Ghost.reveal current_sent)));
  fold (ymodem_server_snap i snapshot_received snapshot_sent snapshot_state);
  fold (ymodem_server_inv i current_received current_sent current_state)
}

(* ── the ghost engine of a local step ─────────────────────────────────────────

   Given the current invariant resource and a proof that `ev` steps `st0` to
   `st1` producing `out`, advance the monotonic log by one step and re-establish
   the invariant at the extended `sent`. *)
ghost fn advance_and_fold_step
  (i:ymodem_server_impl)
  (received:erased TCP.bytes) (sent0:erased TCP.bytes) (st0:erased YP.ymodem_server_state)
  (ev:erased YP.ymodem_server_local) (st1:erased YP.ymodem_server_state)
  (out:erased (SM.step_output ymodem_packet unit))
requires
  MR.pts_to i.ysi_progress #1.0R (Log.mk_log received sent0 st0) **
  pure (Log.server_trace_ok received sent0 st0 /\
        YP.ymodem_server_step (reveal st0) (SM.LocalEvent (reveal ev)) (reveal st1) (reveal out))
ensures
  ymodem_server_inv i received
    (Seq.append sent0 (WF.serialize_all ymodem_wire_format (reveal out).SM.so_wire_outputs))
    st1
{
  Log.lemma_ys_step_rel_intro
    (Log.mk_log received sent0 st0)
    (Log.mk_log received
       (Seq.append (reveal sent0)
          (WF.serialize_all ymodem_wire_format (reveal out).SM.so_wire_outputs))
       st1)
    ev out;
  RTC.closure_step Log.ys_step_rel
    (Log.mk_log received sent0 st0)
    (Log.mk_log received
       (Seq.append (reveal sent0)
          (WF.serialize_all ymodem_wire_format (reveal out).SM.so_wire_outputs))
       st1);
  MR.update i.ysi_progress
    (Log.mk_log received
       (Seq.append (reveal sent0)
          (WF.serialize_all ymodem_wire_format (reveal out).SM.so_wire_outputs))
       st1);
  Log.lemma_server_trace_ok_step received sent0 st0 ev st1 out;
  fold (ymodem_server_inv i received
          (Seq.append (reveal sent0)
             (WF.serialize_all ymodem_wire_format (reveal out).SM.so_wire_outputs))
          st1)
}

(* ── extract the emitted packet from the leaf's post ──────────────────────── *)
ghost fn extract_pkt (d o':erased TCP.bytes)
requires pure (exists (pkt:ymodem_packet).
                 (pkt.data <: Seq.seq U8.t) == reveal d /\ reveal o' == ymodem_serialize pkt)
returns pkt : erased ymodem_packet
ensures pure (Seq.equal ((reveal pkt).data <: Seq.seq U8.t) (reveal d) /\
              reveal o' == ymodem_serialize (reveal pkt))
{
  let pkt = ID.indefinite_description_ghost ymodem_packet
    (fun (pkt:ymodem_packet) ->
      (pkt.data <: Seq.seq U8.t) == reveal d /\ reveal o' == ymodem_serialize pkt);
  hide pkt
}

(* ── network processing: a genuine no-op (no wire input) ──────────────────── *)

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
  Log.lemma_network_noop
    (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
    received0 sent0 st0;
  let result = Log.ys_result CPI.IllegalTransition 0sz;
  fold (ymodem_server_network_frame_post
          frame result input_contents input_len old_out old_out
          st0 st0 Seq.empty [] []);
  result
}

(* ── local processing: drive the packet-framing helper ────────────────────── *)

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
  unfold (ymodem_server_inv i received0 sent0 st0);
  unfold (ymodem_server_local_frame_pre ev frame st0 out out_len old_out);
  with d. _;
  match ev {
    YP.YmodemStart filename len plan -> {
      ymodem_server_emit_block 0uy frame.yslf_buf out;
      with o'. _;
      Log.lemma_ymodem_start_step st0 filename len plan;
      let st1 : erased YP.ymodem_server_state = hide (Log.ymodem_start_result filename len plan);
      advance_and_fold_step i received0 sent0 st0 ev st1 (hide Log.no_wire_output);
      Log.lemma_output_written_empty_wire o';
      Log.lemma_local_stepok ev old_out o' out_len received0 sent0 st0
        0sz st1 [] (WF.serialize_all ymodem_wire_format []);
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz)
              old_out o' st0 st1 [] []);
      Log.ys_result CPI.StepOk 0sz
    }
    YP.YmodemSendBlock -> {
      ymodem_server_emit_block frame.yslf_blk frame.yslf_buf out;
      with o'. _;
      let pkt = extract_pkt d o';
      Log.lemma_ymodem_send_result_ok st0 pkt;
      Log.lemma_ymodem_sendblock_step st0 (Log.ymodem_send_result st0) pkt;
      let st1 : erased YP.ymodem_server_state = hide (Log.ymodem_send_result st0);
      let out_e : erased (SM.step_output ymodem_packet unit) =
        hide ({ SM.so_wire_outputs = [reveal pkt]; SM.so_local_outputs = [] });
      advance_and_fold_step i received0 sent0 st0 ev st1 out_e;
      Log.lemma_output_written_block o' pkt;
      Log.lemma_local_stepok ev old_out o' out_len received0 sent0 st0
        133sz st1 [reveal pkt] (WF.serialize_all ymodem_wire_format [reveal pkt]);
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 133sz)
              old_out o' st0 st1 [reveal pkt] []);
      Log.ys_result CPI.StepOk 133sz
    }
    YP.YmodemEot -> {
      Log.lemma_ymodem_eot_step st0;
      let st1 : erased YP.ymodem_server_state = hide (Log.ymodem_eot_result st0);
      advance_and_fold_step i received0 sent0 st0 ev st1 (hide Log.no_wire_output);
      Log.lemma_output_written_empty_wire old_out;
      Log.lemma_local_stepok ev old_out old_out out_len received0 sent0 st0
        0sz st1 [] (WF.serialize_all ymodem_wire_format []);
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz)
              old_out old_out st0 st1 [] []);
      Log.ys_result CPI.StepOk 0sz
    }
    YP.YmodemAbort -> {
      Log.lemma_ymodem_abort_step st0;
      let st1 : erased YP.ymodem_server_state = hide (Log.ymodem_abort_result st0);
      advance_and_fold_step i received0 sent0 st0 ev st1 (hide Log.no_wire_output);
      Log.lemma_output_written_empty_wire old_out;
      Log.lemma_local_stepok ev old_out old_out out_len received0 sent0 st0
        0sz st1 [] (WF.serialize_all ymodem_wire_format []);
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz)
              old_out old_out st0 st1 [] []);
      Log.ys_result CPI.StepOk 0sz
    }
  }
}

(* ── initialization ───────────────────────────────────────────────────────── *)

fn new_ymodem_server ()
requires emp
returns i:ymodem_server_impl
ensures ymodem_server_inv i Seq.empty Seq.empty YP.ymodem_server_initial
{
  let progress = MR.alloc #_ #Log.ys_log_evolves Log.initial_ys_log;
  let i = { ysi_progress = progress };
  rewrite (MR.pts_to progress #1.0R Log.initial_ys_log) as
    (MR.pts_to i.ysi_progress #1.0R (Log.mk_log Seq.empty Seq.empty YP.ymodem_server_initial));
  Log.lemma_server_trace_ok_initial ();
  fold (ymodem_server_inv i Seq.empty Seq.empty YP.ymodem_server_initial);
  i
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
