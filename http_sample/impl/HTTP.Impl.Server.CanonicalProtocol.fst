module HTTP.Impl.Server.CanonicalProtocol

(**
  The HTTP/1.1 Content-Length **response sender** as a verified instance of
  `Common.ProtocolImplementation.protocol_implementation`, refining the spec
  state machine `HTTP.Protocol.Length.http_server_wfsm`.

  This is the Pulse shell over the pure trace machinery in
  `HTTP.Impl.Server.Log`; it is a verified-but-NOT-extracted refinement witness
  (a `protocol_implementation` dictionary is not Low-star).  It mirrors
  `TFTP.Impl.Server.CanonicalProtocol` / `YModem.Impl.Server.CanonicalProtocol`.

    * `pi_process_local` drives the four local events faithfully:
        - `Server_start`    binds the target and queues the pre-framed body plan,
                            emits nothing;
        - `Server_send`     copies the next body segment into the output buffer
                            (a body segment serializes to *itself*, `ser_body p
                            == p`), moving one block from `pending` to `sent`;
        - `Server_complete` flips the status to Completed, emits nothing;
        - `Server_abort`    flips the status to Aborted, emits nothing.

    * `pi_process_network` is a TOTAL no-op returning `IllegalTransition`.  This
      is not a shortcut: `http_server_step` maps every `SM.WireEvent` to `False`,
      so the response sender provably cannot be advanced by any wire input at
      all, and the no-progress disjunct of
      `CPI.network_error_refines_state_machine` is the only sound answer —
      unconditionally, whatever bytes arrive.  (Compare TFTP, whose sender must
      dispatch ACK / ERROR datagrams.)  `Log.lemma_network_noop` discharges it.

  The handle carries a concrete single-cell status flag (tied to the abstract
  state by `Log.hs_status_flag_ok`) and a monotonic ghost reference tracking the
  server log — received / sent bytes plus abstract state — under the
  reflexive-transitive closure `Log.hs_state_ahead_preorder` of the single-step
  relation.  Because `hss_pending` is ghost, the local frame carries a concrete
  `hslf_more` bit saying whether body segments remain after the event; the real
  server knows this (it is `remaining > 0`), and it is what lets the handler
  maintain the 0uy/1uy split of the status flag.
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
module R = Pulse.Lib.Reference
module MR = Pulse.Lib.MonotonicGhostRef
module RTC = FStar.ReflexiveTransitiveClosure
module ID = FStar.IndefiniteDescription
module Vec = Pulse.Lib.Vec

module HP = HTTP.Protocol.Length
module Log = HTTP.Impl.Server.Log

open HTTP.Wire.Length

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* ── emit a body segment ──────────────────────────────────────────────────────

   A body segment serializes to itself (`ser_body p == p`), so "emitting" it is a
   copy into the output buffer.  The post recovers the `body_payload` refinement
   witness so the caller can name the emitted `Msg_body`. *)
fn http_emit_body
  (data: array U8.t)
  (data_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to data 'd **
    pts_to out 'o **
    pure (Seq.length 'd == SZ.v data_len /\ Seq.length 'o == SZ.v data_len /\ body_ok 'd)
  ensures
    pts_to data 'd **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == SZ.v data_len /\ Seq.equal o' 'd /\ body_ok o'))
{
  let mut i = 0sz;
  while (SZ.lt !i data_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to data 'd **
    pts_to out sv **
    pure (
      SZ.v vi <= SZ.v data_len /\
      Seq.length 'd == SZ.v data_len /\
      Seq.length sv == SZ.v data_len /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv j == Seq.index 'd j))
  decreases (Prims.op_Subtraction (SZ.v data_len) (SZ.v (!i)))
  {
    let vi = !i;
    let dv = data.(vi);
    out.(vi) <- dv;
    i := SZ.add vi 1sz;
  };
  with sf. assert (pts_to out sf);
  Seq.lemma_eq_elim sf (Ghost.reveal 'd);
  ()
}

(* ── the sender implementation handle ─────────────────────────────────────── *)

noeq
type http_server_impl = {
  status   : Vec.vec U8.t;                        // single cell: 0/1/2/3 status flag
  progress : MR.mref Log.hs_state_ahead_preorder; // ghost history under the RTC preorder
}

(* ── invariant / snapshot ─────────────────────────────────────────────────── *)

let http_server_inv
  (i:http_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:HP.http_server_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t).
     Vec.pts_to i.status svs **
     pure (Seq.length svs == 1 /\ Log.hs_status_flag_ok (Seq.index svs 0) st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.server_trace_ok received sent (Log.mk_log received sent st))

let http_server_snap
  (i:http_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:HP.http_server_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* ── network frame ────────────────────────────────────────────────────────────

   The sender consumes no wire input, so the frame needs no scratch space and the
   post records the strongest possible fact: a network event NEVER changes the
   abstract state. *)
noeq
type http_server_network_frame = { hsnf_unit : unit }

let http_server_network_frame_pre
  (frame:http_server_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  pure (
    SZ.v input_len == Seq.length input_contents /\
    Seq.length old_out == SZ.v out_len)

let http_server_network_frame_post
  (frame:http_server_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:HP.http_server_state) (st1:HP.http_server_state)
  (consumed:TCP.bytes)
  (wire_outputs:list http_message) (local_outputs:list unit)
  : slprop =
  pure (local_outputs == [] /\ wire_outputs == [] /\ st1 == st0)

(* ── local frame ──────────────────────────────────────────────────────────────

   `hslf_buf` holds the body segment to emit (`Server_send`); `hslf_more` is the
   concrete "segments remain after this event" bit that keeps the status flag in
   sync with the ghost `hss_pending`. *)
noeq
type http_server_local_frame = {
  hslf_buf  : array U8.t;   // body segment payload
  hslf_len  : SZ.t;         // its length
  hslf_more : bool;         // body segments remain AFTER this event
}

unfold
let local_pre_ok
  (ev:HP.http_server_local) (st0:HP.http_server_state)
  (d:TCP.bytes) (len:SZ.t) (more:bool) : prop =
  match ev with
  | HP.Server_start filename plan ->
    st0.HP.hss_filename == None /\ HP.plan_wf plan /\ more == Cons? plan
  | HP.Server_send ->
    Some? st0.HP.hss_filename /\
    st0.HP.hss_status == FT.FT_InProgress /\
    Cons? st0.HP.hss_pending /\
    HP.plan_wf st0.HP.hss_pending /\
    Seq.equal (L.hd st0.HP.hss_pending) d /\
    body_ok d /\
    more == Cons? (L.tl st0.HP.hss_pending)
  | HP.Server_complete ->
    Some? st0.HP.hss_filename /\
    st0.HP.hss_status == FT.FT_InProgress /\
    st0.HP.hss_pending == []
  | HP.Server_abort ->
    st0.HP.hss_status == FT.FT_InProgress

let http_server_local_frame_pre
  (ev:HP.http_server_local)
  (frame:http_server_local_frame)
  (st0:HP.http_server_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.hslf_buf d **
     pure (Seq.length d == SZ.v frame.hslf_len /\
           local_pre_ok ev st0 d frame.hslf_len frame.hslf_more)) **
  pure (Seq.length old_out == SZ.v frame.hslf_len)

(* Deterministic post-transition witness for the LOCAL handler. *)
unfold
let hs_local_post_ok
  (ev:HP.http_server_local) (st0 st1:HP.http_server_state) : prop =
  match ev with
  | HP.Server_start filename plan -> st1 == Log.start_next_state filename plan
  | HP.Server_send -> Cons? st0.HP.hss_pending /\ st1 == Log.send_next_state st0
  | HP.Server_complete -> st1 == Log.complete_next_state st0
  | HP.Server_abort -> st1 == Log.abort_next_state st0

let http_server_local_frame_post
  (ev:HP.http_server_local)
  (frame:http_server_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:HP.http_server_state) (st1:HP.http_server_state)
  (wire_outputs:list http_message) (local_outputs:list unit)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.hslf_buf d **
     pure (Seq.length d == SZ.v frame.hslf_len)) **
  pure (local_outputs == [] /\ hs_local_post_ok ev st0 st1)

(* ── ghost obligations ────────────────────────────────────────────────────── *)

ghost fn http_server_invariant_valid
  (i:http_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased HP.http_server_state)
requires http_server_inv i received sent st
ensures
  http_server_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (HP.http_server_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (http_server_inv i received sent st);
  with svs. _;
  Log.lemma_server_trace_ok_valid received sent (Log.mk_log received sent st);
  fold (http_server_inv i received sent st)
}

ghost fn http_server_take_snapshot
  (i:http_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased HP.http_server_state)
requires http_server_inv i received sent st
ensures
  http_server_inv i received sent st **
  http_server_snap i received sent st
{
  unfold (http_server_inv i received sent st);
  with svs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
  fold (http_server_snap i received sent st);
  fold (http_server_inv i received sent st)
}

ghost fn http_server_recall_snapshot
  (i:http_server_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased HP.http_server_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased HP.http_server_state)
requires
  http_server_snap i snapshot_received snapshot_sent snapshot_state **
  http_server_inv i current_received current_sent current_state
ensures
  http_server_snap i snapshot_received snapshot_sent snapshot_state **
  http_server_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (HP.http_server_wfsm)
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  unfold (http_server_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (http_server_inv i current_received current_sent current_state);
  with svs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_hs_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_hs_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (http_server_snap i snapshot_received snapshot_sent snapshot_state);
  fold (http_server_inv i current_received current_sent current_state)
}

(* ── recover the emitted segment's `body_payload` refinement ──────────────── *)
ghost fn extract_body_payload (o':erased TCP.bytes)
requires pure (body_ok (reveal o'))
returns pl : erased body_payload
ensures pure ((reveal pl <: Seq.seq U8.t) == reveal o')
{
  let b : body_payload = reveal o';
  hide b
}

(* ── network processing: a total no-op ────────────────────────────────────────

   `http_server_step _ (SM.WireEvent _) _ _` is `False`, so the response sender
   can never be advanced by wire input.  Every call therefore returns the
   no-progress `IllegalTransition` result, leaving state and both byte histories
   untouched — sound unconditionally. *)
fn http_server_process_network
  (i:http_server_impl)
  (frame:http_server_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased HP.http_server_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  http_server_inv i received0 sent0 st0 **
  http_server_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased HP.http_server_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list http_message)
                (local_outputs:list unit).
  http_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  http_server_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (HP.http_server_wfsm)
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
  unfold (http_server_network_frame_pre frame input input_len out out_len input_contents old_out);
  Log.lemma_network_noop
    (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
    (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
  fold (http_server_network_frame_post
    frame (Log.hs_result CPI.IllegalTransition 0sz 0sz) input_contents input_len
    old_out (Ghost.reveal old_out)
    (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
  Log.hs_result CPI.IllegalTransition 0sz 0sz
}

(* ── local processing: the four sender events ─────────────────────────────── *)

fn http_server_process_local
  (i:http_server_impl)
  (ev:HP.http_server_local)
  (frame:http_server_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased HP.http_server_state)
  (old_out:erased TCP.bytes)
requires
  http_server_inv i received0 sent0 st0 **
  http_server_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (
    SZ.v out_len == Seq.length (Ghost.reveal old_out) /\
    ~ (CPI.no_internal_events #HP.http_server_local ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased HP.http_server_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list http_message)
                (local_outputs:list unit).
  http_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  http_server_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1) wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (HP.http_server_wfsm)
      ev
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
      wire_outputs
      local_outputs)
{
  unfold (http_server_inv i received0 sent0 st0);
  with svs. _;
  unfold (http_server_local_frame_pre ev frame st0 out out_len old_out);
  with d. _;
  match ev {
    HP.Server_start filename plan -> {
      (* StepOk — bind the target and queue the plan; nothing is emitted. *)
      Log.lemma_start_step (Ghost.reveal st0) filename plan;
      let st1 = Ghost.hide (Log.start_next_state filename plan);
      let flag = (if frame.hslf_more then 0uy else 1uy);
      Vec.op_Array_Assignment i.status 0sz flag;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_start_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) filename plan;
      RTC.closure_step Log.hs_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (http_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (http_server_local_frame_post ev frame (Log.hs_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.hs_result CPI.StepOk 0sz 0sz
    }
    HP.Server_send -> {
      (* StepOk — copy the next body segment out; a segment serializes to itself. *)
      http_emit_body frame.hslf_buf frame.hslf_len out;
      with o'. assert (pts_to out o');
      let pl = extract_body_payload o';
      Log.lemma_send_step (Ghost.reveal st0) (Ghost.reveal pl);
      let st1 = Ghost.hide (Log.send_next_state (Ghost.reveal st0));
      let flag = (if frame.hslf_more then 0uy else 1uy);
      Vec.op_Array_Assignment i.status 0sz flag;
      with svs2. _;
      let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Ghost.reveal pl <: TCP.bytes));
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_send_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) (Ghost.reveal pl);
      RTC.closure_step Log.hs_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (http_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_body_output_written (Ghost.reveal o') frame.hslf_len (Ghost.reveal pl);
      Log.lemma_serialize_all_body (Ghost.reveal pl);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        frame.hslf_len (Ghost.reveal st1) (Log.body_wire_outputs (Ghost.reveal pl))
        (Ghost.reveal pl <: TCP.bytes);
      fold (http_server_local_frame_post ev frame (Log.hs_result CPI.StepOk 0sz frame.hslf_len)
        old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st1)
        (Log.body_wire_outputs (Ghost.reveal pl)) []);
      Log.hs_result CPI.StepOk 0sz frame.hslf_len
    }
    HP.Server_complete -> {
      (* StepOk — the declared Content-Length has been written. *)
      Log.lemma_complete_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.complete_next_state (Ghost.reveal st0));
      Vec.op_Array_Assignment i.status 0sz 2uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_complete_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.hs_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (http_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (http_server_local_frame_post ev frame (Log.hs_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.hs_result CPI.StepOk 0sz 0sz
    }
    HP.Server_abort -> {
      (* StepOk — the connection was torn down mid-body. *)
      Log.lemma_abort_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.abort_next_state (Ghost.reveal st0));
      Vec.op_Array_Assignment i.status 0sz 3uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_abort_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.hs_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (http_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (http_server_local_frame_post ev frame (Log.hs_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.hs_result CPI.StepOk 0sz 0sz
    }
  }
}

(* ── constructor: a freshly-created, un-started sender ────────────────────── *)

fn new_http_server ()
requires emp
returns i:http_server_impl
ensures http_server_inv i Seq.empty Seq.empty HP.http_server_initial **
        pure (Vec.is_full_vec i.status)
{
  let status = Vec.alloc 1uy 1sz;
  let progress =
    MR.alloc #_ #Log.hs_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty HP.http_server_initial);
  let i = { status; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty HP.http_server_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty HP.http_server_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  Log.lemma_initial_trace_ok ();
  fold (http_server_inv i Seq.empty Seq.empty HP.http_server_initial);
  assert (pure (Vec.is_full_vec i.status));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let http_server_protocol_implementation
  : CPI.protocol_implementation
      http_server_impl
      HP.http_server_state
      http_message
      HP.http_server_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> HP.http_server_wfsm);
    CPI.pi_internal = CPI.no_internal_events #HP.http_server_local;
    CPI.pi_internal_pending = CPI.nothing_pending #HP.http_server_state;
    CPI.pi_invariant = http_server_inv;
    CPI.pi_snapshot = http_server_snap;
    CPI.pi_network_frame = http_server_network_frame;
    CPI.pi_network_frame_pre = http_server_network_frame_pre;
    CPI.pi_network_frame_post = http_server_network_frame_post;
    CPI.pi_local_frame = http_server_local_frame;
    CPI.pi_local_frame_pre = http_server_local_frame_pre;
    CPI.pi_local_frame_post = http_server_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #http_server_local_frame #HP.http_server_state;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #http_server_local_frame #HP.http_server_state #http_message #unit;
    CPI.pi_invariant_valid = http_server_invariant_valid;
    CPI.pi_take_snapshot = http_server_take_snapshot;
    CPI.pi_recall_snapshot = http_server_recall_snapshot;
    CPI.pi_process_network = http_server_process_network;
    CPI.pi_process_local = http_server_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #HP.http_server_state #http_message #HP.http_server_local #unit #http_server_local_frame
        http_server_inv
        (fun _ -> HP.http_server_wfsm);
  }
