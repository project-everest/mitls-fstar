module YModem.Impl.Client.CanonicalProtocol

(**
  YMODEM *client* (receiver) as a verified instance of the state-machine
  implementation type class `Common.ProtocolImplementation.protocol_implementation`,
  the executable refinement of the `YModem.Protocol.ymodem_client_wfsm`
  specification state machine.

  This is the receiver analogue of `Calc.Server.CanonicalProtocol` (the calc
  *server* is the wire-input-driven template): its `pi_process_network` handler
  validates an incoming 133-byte YMODEM data packet, extracts its 128-byte
  payload by driving the verified `YModem.Impl.Client.ymodem_client_recv_block`
  leaf, appends the payload to the abstract `ycs_received` list, extends a ghost
  reachable-trace over the wire history, and advances a monotonic ghost
  reference.

  The instance is backed by a `Pulse.Lib.MonotonicGhostRef` over the reflexive-
  transitive closure of a `WireEvent`-or-`LocalEvent` step relation
  (`YModem.Impl.Client.Log`); the invariant folds the canonical reachable-trace
  predicate (`Log.client_trace_ok`, which refines the byte history into a valid
  state machine trace via `WFSM.valid_byte_trace`).  The receiver emits no wire
  output, so `sent` is always `Seq.empty`.

  The handle also carries a concrete single-cell status vector (`1uy` =
  in progress, `2uy` = completed), tied to the abstract `ycs_status` by the
  invariant (`Log.yc_status_flag_ok`).  This lets both process handlers branch on
  the transfer status at runtime — necessary because the class exposes the
  current abstract state to a handler only through `pi_invariant` (never through
  the frame precondition), so a handler cannot inspect the erased state directly:

    * `pi_process_local` drives the receiver's local events *faithfully*.  From
      the in-progress state, `YmodemClientEot` is a genuine `StepOk` completion
      transition — it flips the concrete status cell to `2uy`, sets the abstract
      `ycs_status` to `FT_Completed`, and advances the ghost log by a local
      (Eot) step.  `YmodemClientStart` (a client is "born started", so its
      filename is always known) and a second `YmodemClientEot` (already
      completed) are genuine `IllegalTransition` no-ops.
    * `pi_process_network` reads the status cell: in progress, every well-formed
      133-byte packet is a genuine `StepOk`; once completed, a further data
      packet is a sound `IllegalTransition` no-op (a valid state-machine
      refinement that consumes nothing and leaves the state unchanged).

  A client is "born started" via `new_ymodem_client`.
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

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire
open YModem.Impl.Client

(* ───────────────────────────────────────────────────────────────────────────
   Implementation handle: a monotonic ghost reference tracking the receiver's
   progress (its wire/abstract history) under the RTC-closure preorder.  The
   receiver has no concrete runtime state (recv_block writes into a caller
   buffer), so this is the whole handle.
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_impl = {
  status   : Vec.vec U8.t;                       // single element: 1uy=InProgress, 2uy=Completed
  progress : MR.mref Log.yc_state_ahead_preorder;
}

(* The reachable-trace invariant.  The concrete `status` cell carries the runtime
   completion flag (so both process fns can branch on it); the ghost reference
   holds the log determined by the (received, sent, state) triple; its byte
   history refines a valid state-machine trace; and the filename is known.  Note
   the WireEvent guard (`ycs_status == FT_InProgress`) is NO LONGER pinned here —
   the invariant admits FT_Completed so it can be re-established after the EOT
   step; the runtime source of truth for "in progress" is the `status` cell,
   tied to the abstract status by `Log.yc_status_flag_ok`. *)
let ymodem_client_inv
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t).
     Vec.pts_to i.status svs **
     pure (Seq.length svs == 1 /\ Log.yc_status_flag_ok (Seq.index svs 0) st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (
    Log.client_trace_ok received sent (Log.mk_log received sent st) /\
    Some? st.YP.ycs_filename)

(* A monotone snapshot of the progress at a past history. *)
let ymodem_client_snap
  (i:ymodem_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_client_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* Network frame: a 128-byte scratch buffer that `pi_process_network` fills with
   the extracted packet payload. *)
noeq
type ymodem_client_network_frame = {
  ycnf_data : array U8.t;   // 128-byte extracted payload
}

let ymodem_client_network_frame_pre
  (frame:ymodem_client_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.ycnf_data d ** pure (Seq.length d == 128)) **
  pure (Seq.length input_contents == 133 /\ SZ.v input_len == 133)

let ymodem_client_network_frame_post
  (frame:ymodem_client_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_client_state) (st1:YP.ymodem_client_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
  : slprop =
  (exists* o'. pts_to frame.ycnf_data o' ** pure (Seq.length o' == 128)) **
  pure (
    wire_outputs == Log.ymodem_no_wire_outputs /\
    local_outputs == Log.ymodem_no_local_outputs)

(* Local frame: the receiver's local events (start / EOT) emit no packet and
   touch no buffer. *)
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
  (wire_outputs:list ymodem_packet) (local_outputs:list unit)
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

(* ── network processing: drive the verified packet-parsing leaf ───────────── *)

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
  unfold (ymodem_client_inv i received0 sent0 st0);
  with svs. _;
  (* read the concrete completion flag: 1uy = in progress, 2uy = completed *)
  let s = Vec.op_Array_Access i.status 0sz;
  unfold (ymodem_client_network_frame_pre frame input input_len out out_len input_contents old_out);
  with d0. _;
  if (s = 1uy) {
    (* InProgress: the flag agrees `st0.ycs_status == FT_InProgress`, so a
       well-formed 133-byte packet is a genuine StepOk (the original body). *)
    let blk = ymodem_client_recv_block input frame.ycnf_data;
    with o'. _;
    Log.lemma_recv_block_packet input_contents o';
    let pkt = Ghost.hide (Log.ymodem_parsed_packet (Ghost.reveal input_contents));
    Seq.lemma_eq_elim (Ghost.reveal input_contents) (ymodem_serialize (Ghost.reveal pkt));
    let st1 = Ghost.hide (Log.wire_next_state (Ghost.reveal st0) (Ghost.reveal pkt));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_wire_step_ok received0 sent0 st0 pkt received1 sent0 st1;
    Log.lemma_client_trace_ok_network_step received0 sent0 log0 pkt log1;
    assert (pure (Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1)));
    RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    (* the status cell is untouched (still 1uy) and st1 is still InProgress *)
    assert (pure (Log.yc_status_flag_ok (Seq.index svs 0) (Ghost.reveal st1)));
    fold (ymodem_client_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    fold (ymodem_client_network_frame_post
      frame Log.ymodem_client_step_ok_result input_contents input_len old_out (Ghost.reveal old_out)
      st0 (Ghost.reveal st1) (Ghost.reveal input_contents)
      Log.ymodem_no_wire_outputs Log.ymodem_no_local_outputs);
    Log.lemma_ym_network_process_correct_step_ok
      input_contents input_len old_out old_out out_len
      received0 sent0 st0 received1 sent0 st1 pkt;
    Log.ymodem_client_step_ok_result
  } else {
    (* Completed: a genuine no-op — do NOT call recv_block, consume nothing.
       `frame.ycnf_data` is returned untouched (still `d0`). *)
    Log.lemma_ym_network_process_correct_noop
      input_contents input_len old_out out_len received0 sent0 st0;
    fold (ymodem_client_inv i received0 sent0 st0);
    fold (ymodem_client_network_frame_post
      frame Log.ymodem_client_illegal_result input_contents input_len old_out (Ghost.reveal old_out)
      st0 (Ghost.reveal st0) Seq.empty
      Log.ymodem_no_wire_outputs Log.ymodem_no_local_outputs);
    Log.ymodem_client_illegal_result
  }
}

(* ── local processing: refuse local events (sound IllegalTransition no-op) ─── *)

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
  unfold (ymodem_client_local_frame_pre ev frame st0 out out_len old_out);
  match ev {
    YP.YmodemClientStart _ _ -> {
      (* `Start` requires `ycs_filename == None`, but the invariant pins
         `Some? ycs_filename` (a client is born started), so this is a genuine
         IllegalTransition no-op; the invariant is untouched. *)
      Log.lemma_ym_local_process_correct_illegal ev old_out old_out out_len received0 sent0 st0;
      fold (ymodem_client_local_frame_post
        ev frame Log.ymodem_client_illegal_result old_out (Ghost.reveal old_out)
        st0 (Ghost.reveal st0) Log.ymodem_no_wire_outputs Log.ymodem_no_local_outputs);
      Log.ymodem_client_illegal_result
    }
    YP.YmodemClientEot -> {
      unfold (ymodem_client_inv i received0 sent0 st0);
      with svs. _;
      let s = Vec.op_Array_Access i.status 0sz;
      if (s = 1uy) {
        (* InProgress: FAITHFUL StepOk — drive the EOT completion transition,
           flipping the concrete status cell to 2uy (Completed) and advancing the
           monotonic ghost log by a local (Eot) step. *)
        let st1 = Ghost.hide (Log.eot_next_state (Ghost.reveal st0));
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
        Vec.op_Array_Assignment i.status 0sz 2uy;
        with svs2. _;
        Log.lemma_eot_step_ok received0 sent0 st0 received0 sent0 st1;
        Log.lemma_client_trace_ok_local_step received0 sent0 log0 log1;
        assert (pure (Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1)));
        RTC.closure_step Log.yc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        assert (pure (Log.yc_status_flag_ok (Seq.index svs2 0) (Ghost.reveal st1)));
        fold (ymodem_client_inv i received0 sent0 st1);
        Log.lemma_ym_local_process_correct_step_ok
          old_out old_out out_len received0 sent0 st0 st1;
        fold (ymodem_client_local_frame_post
          ev frame Log.ymodem_client_local_stepok_result old_out (Ghost.reveal old_out)
          st0 (Ghost.reveal st1) Log.ymodem_no_wire_outputs Log.ymodem_no_local_outputs);
        Log.ymodem_client_local_stepok_result
      } else {
        (* already Completed: a further EOT is a genuine IllegalTransition no-op. *)
        Log.lemma_ym_local_process_correct_illegal ev old_out old_out out_len received0 sent0 st0;
        fold (ymodem_client_inv i received0 sent0 st0);
        fold (ymodem_client_local_frame_post
          ev frame Log.ymodem_client_illegal_result old_out (Ghost.reveal old_out)
          st0 (Ghost.reveal st0) Log.ymodem_no_wire_outputs Log.ymodem_no_local_outputs);
        Log.ymodem_client_illegal_result
      }
    }
  }
}

(* ── constructor: born started ────────────────────────────────────────────── *)

fn new_ymodem_client (filename:erased TCP.bytes) (len:erased nat)
requires emp
returns i:ymodem_client_impl
ensures ymodem_client_inv i Seq.empty Seq.empty (Log.started_log filename len).Log.ycl_state
{
  let status = Vec.alloc 1uy 1sz;
  let progress = MR.alloc #_ #Log.yc_state_ahead_preorder (Log.started_log filename len);
  let i = { status; progress };
  rewrite (MR.pts_to progress #1.0R (Log.started_log filename len)) as
          (MR.pts_to i.progress #1.0R (Log.started_log filename len));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  Log.lemma_started_trace_ok filename len;
  fold (ymodem_client_inv i Seq.empty Seq.empty (Log.started_log filename len).Log.ycl_state);
  i
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
