module YModem.Impl.Server.CanonicalProtocol

(**

  The YMODEM *server* (sender) as a verified instance of the reliable-delivery
  (ARQ) state machine `YModem.Protocol.ymodem_server_wfsm`, refining
  `Common.ProtocolImplementation.protocol_implementation`.  This is a
  verified-but-NOT-extracted refinement witness (a `protocol_implementation`
  dictionary is not Low-star).

    * `pi_process_local` drives the six local events faithfully:
        - `Server_start`   initialises the transfer (filename/len/plan), emits
          nothing, sets the status cell to "idle";
        - `Server_send`    frames + emits the next 128-byte block (SOH), moving
          into the "one-outstanding" state;
        - `Server_eot`     writes the 1-byte EOT (enter the handshake);
        - `Server_complete`flips the status to Completed, emits nothing;
        - `Server_timeout` retransmits the outstanding data block (data phase)
          or re-emits the EOT (EOT phase), leaving the abstract state unchanged;
        - `Server_abort`   flips the status to Aborted, emits nothing.

    * `pi_process_network` dispatches on the single serialized control message
      in its input (ACK / NAK / CAN):
        - ACK  (0x06) in the one-outstanding state: advance `acked`, emit nothing;
        - NAK  (0x15) in the EOT handshake: re-emit the EOT;
        - CAN  (0x18) while InProgress: flip the status to Aborted;
        - everything else (including NAK in the data phase — see below): a sound
          IllegalTransition no-op (the third "no progress" disjunct of
          `network_error_refines_state_machine`).

  NAK-in-data-phase (the *network* data retransmit) falls back to the SOUND
  no-op.  A *faithful* network NAK retransmit would need the frame precondition
  to couple the emit source to `st0.yss_sent[st0.yss_acked]`, but the class
  field `pi_network_frame_pre` has NO `state` parameter (unlike
  `pi_local_frame_pre`, which does), so that coupling is not expressible through
  the network frame.  The retransmit *capability* is preserved faithfully by the
  `Server_timeout` local event, whose `pi_local_frame_pre` DOES receive `st0`.
  See the report.

  The pure ARQ trace / monotonic-log / closure reasoning lives in the
  ordinary-F* helper module `YModem.Impl.Server.Log`; this module is the thin
  Pulse shell binding the heap resources to it, mirroring the freshly-built
  CLIENT instance `YModem.Impl.Client.CanonicalProtocol`.

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
module ID = FStar.IndefiniteDescription
module Vec = Pulse.Lib.Vec

module YP = YModem.Protocol
module Log = YModem.Impl.Server.Log
module Codec = YModem.Impl.Codec

open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire
open YModem.Impl.Control

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* ── the sender implementation handle ─────────────────────────────────────────

   A concrete single-cell status vector carrying a FIVE-valued runtime status
   flag (idle / one-outstanding / EOT-handshake / completed / aborted — tied to
   the abstract state by `Log.ys_status_flag_ok`); and a monotonic ghost
   reference tracking the server *log* (received / sent bytes and abstract
   state) under the reflexive-transitive-closure preorder of the single-step
   relation.  Both handlers branch on the status cell (necessary because the
   class hands the network handler no `st0`, and the local `Server_timeout`
   handler must choose its output by phase without reading the erased state). *)
noeq
type ymodem_server_impl = {
  status   : Vec.vec U8.t;                        // single cell: 0/1/2/3/4 status flag
  progress : MR.mref Log.ys_state_ahead_preorder; // ghost history under the RTC preorder
}

(* ── invariant / snapshot ─────────────────────────────────────────────────── *)

let ymodem_server_inv
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t).
     Vec.pts_to i.status svs **
     pure (Seq.length svs == 1 /\ Log.ys_status_flag_ok (Seq.index svs 0) st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.server_trace_ok received sent (Log.mk_log received sent st))

let ymodem_server_snap
  (i:ymodem_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:YP.ymodem_server_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* ── network frame: matches the task's designed shape (a 128-byte scratch +
   block number), threaded unused because network NAK-data falls back to the
   sound no-op.  The frame precondition CANNOT couple the scratch to
   `st0.yss_sent[st0.yss_acked]` because the class field `pi_network_frame_pre`
   has no `state` parameter. *)
noeq
type ymodem_server_network_frame = {
  ysnf_buf : array U8.t;   // 128-byte outstanding-block scratch
  ysnf_blk : U8.t;         // block number
}

let ymodem_server_network_frame_pre
  (frame:ymodem_server_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.ysnf_buf d ** pure (Seq.length d == 128)) **
  pure (
    SZ.v input_len == Seq.length input_contents /\
    SZ.v input_len >= 1 /\
    SZ.v out_len >= 133 /\
    Seq.length old_out == SZ.v out_len)

(* Deterministic post-transition witness for the NETWORK handler: the endpoint's
   state-dependent `pe_frame_ready` coupling is re-established by
   `pe_finish_network_action`, which receives only this post (NOT
   `network_process_correct`, whose IllegalTransition disjunct is too lossy to
   pin `st1`).  Every `pi_process_network` branch lands in one of these three. *)
unfold
let ys_network_post_ok (st0 st1:YP.ymodem_server_state) : prop =
  st1 == st0 \/
  st1 == Log.ack_next_state st0 \/
  st1 == Log.abort_next_state st0

let ymodem_server_network_frame_post
  (frame:ymodem_server_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (consumed:TCP.bytes)
  (wire_outputs:list ymodem_message) (local_outputs:list unit)
  : slprop =
  (exists* o'. pts_to frame.ysnf_buf o' ** pure (Seq.length o' == 128)) **
  pure (local_outputs == [] /\ ys_network_post_ok st0 st1)

(* ── local frame: the 128-byte payload buffer + the block number.  Its
   precondition DOES receive `st0`, so it faithfully supplies the outstanding
   block for `Server_send` (== `hd pending`) and `Server_timeout` in the data
   phase (== `sent[acked]`). *)
noeq
type ymodem_server_local_frame = {
  yslf_buf : array U8.t;   // 128-byte payload
  yslf_blk : U8.t;         // block number
}

unfold
let local_pre_ok (ev:YP.ymodem_server_local) (st0:YP.ymodem_server_state) (d:TCP.bytes) : prop =
  match ev with
  | YP.Server_start filename len plan ->
    st0.YP.yss_filename == None /\ YP.plan_wf plan
  | YP.Server_send ->
    Some? st0.YP.yss_filename /\
    st0.YP.yss_status == FT.FT_InProgress /\
    st0.YP.yss_phase == YP.SP_Data /\
    L.length st0.YP.yss_sent == st0.YP.yss_acked /\
    Cons? st0.YP.yss_pending /\
    YP.plan_wf st0.YP.yss_pending /\
    Seq.equal (L.hd st0.YP.yss_pending) d
  | YP.Server_eot ->
    Some? st0.YP.yss_filename /\
    st0.YP.yss_status == FT.FT_InProgress /\
    st0.YP.yss_phase == YP.SP_Data /\
    st0.YP.yss_pending == [] /\
    st0.YP.yss_acked == L.length st0.YP.yss_sent
  | YP.Server_complete ->
    Some? st0.YP.yss_filename /\
    st0.YP.yss_status == FT.FT_InProgress /\
    st0.YP.yss_phase == YP.SP_Eot /\
    st0.YP.yss_pending == [] /\
    st0.YP.yss_acked == L.length st0.YP.yss_sent
  | YP.Server_timeout ->
    st0.YP.yss_status == FT.FT_InProgress /\
    (st0.YP.yss_phase == YP.SP_Data ==>
       st0.YP.yss_acked < L.length st0.YP.yss_sent /\
       Seq.equal (L.index st0.YP.yss_sent st0.YP.yss_acked) d)
  | YP.Server_abort ->
    st0.YP.yss_status == FT.FT_InProgress

let ymodem_server_local_frame_pre
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (st0:YP.ymodem_server_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.yslf_buf d **
     pure (Seq.length d == 128 /\ local_pre_ok ev st0 d)) **
  pure (Seq.length old_out == 133)

(* Deterministic post-transition witness for the LOCAL handler: like the network
   case, `pe_finish_local_action` re-establishes the coupling from this post
   alone.  Each scheduled event lands on its `*_next_state` (Server_send needs a
   non-empty pending list, supplied by `local_pre_ok`). *)
unfold
let ys_local_post_ok (ev:YP.ymodem_server_local) (st0 st1:YP.ymodem_server_state) : prop =
  match ev with
  | YP.Server_start filename len plan -> st1 == Log.start_next_state filename len plan
  | YP.Server_send -> Cons? st0.YP.yss_pending /\ st1 == Log.send_next_state st0
  | YP.Server_eot -> st1 == Log.eot_next_state st0
  | YP.Server_complete -> st1 == Log.complete_next_state st0
  | YP.Server_abort -> st1 == Log.abort_next_state st0
  | YP.Server_timeout -> st1 == st0

let ymodem_server_local_frame_post
  (ev:YP.ymodem_server_local)
  (frame:ymodem_server_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:YP.ymodem_server_state) (st1:YP.ymodem_server_state)
  (wire_outputs:list ymodem_message) (local_outputs:list unit)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.yslf_buf d ** pure (Seq.length d == 128)) **
  pure (ys_local_post_ok ev st0 st1)

(* ── ghost obligations (copied from the client, re-threading the status cell) ─ *)

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
  with svs. _;
  Log.lemma_server_trace_ok_valid received sent (Log.mk_log received sent st);
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
  with svs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
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
  with svs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_ys_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_ys_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (ymodem_server_snap i snapshot_received snapshot_sent snapshot_state);
  fold (ymodem_server_inv i current_received current_sent current_state)
}

(* ── extract the emitted SOH body from the emit leaf's post ────────────────── *)
ghost fn extract_soh_body (d o':erased TCP.bytes) (blk:U8.t)
requires pure (exists (body:ymodem_soh_body).
                 (body.data <: Seq.seq U8.t) == reveal d /\ body.blk == blk /\
                 reveal o' == ymodem_serialize (Body_soh body))
returns body : erased ymodem_soh_body
ensures pure (((reveal body).data <: Seq.seq U8.t) == reveal d /\ (reveal body).blk == blk /\
              reveal o' == ymodem_serialize (Body_soh (reveal body)))
{
  let body = ID.indefinite_description_ghost ymodem_soh_body
    (fun (body:ymodem_soh_body) ->
      (body.data <: Seq.seq U8.t) == reveal d /\ body.blk == blk /\
      reveal o' == ymodem_serialize (Body_soh body));
  hide body
}

(* ── network processing: dispatch on the single serialized control message ── *)

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
                (wire_outputs:list ymodem_message)
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
  unfold (ymodem_server_inv i received0 sent0 st0);
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  unfold (ymodem_server_network_frame_pre frame input input_len out out_len input_contents old_out);
  with d0. _;
  let lead = input.(0sz);
  if (s = 1uy && input_len = 1sz && lead = 6uy) {
    (* ACK in the one-outstanding state: StepOk — advance acked, emit nothing. *)
    Log.lemma_input_is_serialize_ack (Ghost.reveal input_contents);
    lemma_serialize_control (Body_ack ());
    assert (pure (Ghost.reveal input_contents == Seq.create 1 6uy));
    Log.lemma_ack_step (Ghost.reveal st0);
    let st1 = Ghost.hide (Log.ack_next_state (Ghost.reveal st0));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 0uy;
    with svs2. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_ack_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_server_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_output_written_empty (Ghost.reveal old_out);
    Seq.append_empty_r (Ghost.reveal sent0);
    Log.lemma_network_stepok
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      (Body_ack ()) (Ghost.reveal st1) 0sz [] Seq.empty;
    fold (ymodem_server_network_frame_post
      frame (Log.ys_result CPI.StepOk input_len 0sz) input_contents input_len old_out old_out
      (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
    Log.ys_result CPI.StepOk input_len 0sz
  } else if (s = 2uy && input_len = 1sz && lead = 21uy) {
    (* NAK in the EOT handshake: StepOk — re-emit the 1-byte EOT. *)
    Log.lemma_input_is_serialize_nak (Ghost.reveal input_contents);
    lemma_serialize_control (Body_nak ());
    assert (pure (Ghost.reveal input_contents == Seq.create 1 21uy));
    Log.lemma_nak_eot_step (Ghost.reveal st0);
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Seq.create 1 4uy));
    out.(0sz) <- 4uy;
    with out_contents. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st0));
    Log.lemma_nak_eot_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st0));
    Log.lemma_eot_produced ();
    Log.lemma_eot_output_written (Ghost.reveal out_contents);
    Log.lemma_network_stepok
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal out_contents) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      (Body_nak ()) (Ghost.reveal st0) 1sz [Body_eot ()] (Seq.create 1 4uy);
    fold (ymodem_server_network_frame_post
      frame (Log.ys_result CPI.StepOk input_len 1sz) input_contents input_len old_out (Ghost.reveal out_contents)
      (Ghost.reveal st0) (Ghost.reveal st0) (Ghost.reveal input_contents) [Body_eot ()] []);
    Log.ys_result CPI.StepOk input_len 1sz
  } else if ((s = 0uy || s = 1uy || s = 2uy) && input_len = 1sz && lead = 24uy) {
    (* CAN while InProgress: StepOk — flip the status to Aborted, emit nothing. *)
    Log.lemma_input_is_serialize_can (Ghost.reveal input_contents);
    lemma_serialize_control (Body_can ());
    assert (pure (Ghost.reveal input_contents == Seq.create 1 24uy));
    Log.lemma_can_step (Ghost.reveal st0);
    let st1 = Ghost.hide (Log.abort_next_state (Ghost.reveal st0));
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
    Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 4uy;
    with svs2. _;
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_can_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (ymodem_server_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_output_written_empty (Ghost.reveal old_out);
    Seq.append_empty_r (Ghost.reveal sent0);
    Log.lemma_network_stepok
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      (Body_can ()) (Ghost.reveal st1) 0sz [] Seq.empty;
    fold (ymodem_server_network_frame_post
      frame (Log.ys_result CPI.StepOk input_len 0sz) input_contents input_len old_out old_out
      (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
    Log.ys_result CPI.StepOk input_len 0sz
  } else {
    (* Not enabled (incl. NAK-in-data-phase): a sound IllegalTransition no-op. *)
    Log.lemma_network_noop
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    fold (ymodem_server_network_frame_post
      frame (Log.ys_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
      (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
    Log.ys_result CPI.IllegalTransition 0sz 0sz
  }
}

(* ── local processing: drive the six local events ─────────────────────────── *)

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
  pure (
    SZ.v out_len == Seq.length old_out /\
    ~ (CPI.no_internal_events #YP.ymodem_server_local ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_server_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list ymodem_message)
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
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  unfold (ymodem_server_local_frame_pre ev frame st0 out out_len old_out);
  with d. _;
  match ev {
    YP.Server_start filename len plan -> {
      (* StepOk — initialise the transfer; the "idle" cell 0uy is unchanged. *)
      Log.lemma_start_step (Ghost.reveal st0) filename len plan;
      let st1 = Ghost.hide (Log.start_next_state filename len plan);
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 0uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_start_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) filename len plan;
      RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ys_result CPI.StepOk 0sz 0sz
    }
    YP.Server_send -> {
      (* StepOk — frame + emit the next 128-byte block; enter one-outstanding. *)
      Codec.ymodem_emit_data_block frame.yslf_blk frame.yslf_buf out;
      with o'. _;
      let body = extract_soh_body d o' frame.yslf_blk;
      Seq.lemma_eq_elim (L.hd (Ghost.reveal st0).YP.yss_pending) (Ghost.reveal d);
      Log.lemma_send_step (Ghost.reveal st0) (Ghost.reveal body);
      let st1 = Ghost.hide (Log.send_next_state (Ghost.reveal st0));
      let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (ymodem_serialize (Body_soh (Ghost.reveal body))));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 1uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_send_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) (Ghost.reveal body);
      RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_ym_serialize_all_singleton (Body_soh (Ghost.reveal body));
      Seq.lemma_eq_intro (Seq.slice (Ghost.reveal o') 0 133) (ymodem_serialize (Body_soh (Ghost.reveal body)));
      Log.lemma_soh_output_written (Ghost.reveal o') (Ghost.reveal body);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        133sz (Ghost.reveal st1) [Body_soh (Ghost.reveal body)]
        (ymodem_serialize (Body_soh (Ghost.reveal body)));
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 133sz)
        old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st1)
        [Body_soh (Ghost.reveal body)] []);
      Log.ys_result CPI.StepOk 0sz 133sz
    }
    YP.Server_eot -> {
      (* StepOk — write the 1-byte EOT; enter the EOT handshake (cell 2uy). *)
      Log.lemma_eot_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.eot_next_state (Ghost.reveal st0));
      let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Seq.create 1 4uy));
      out.(0sz) <- 4uy;
      with o'. _;
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 2uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_eot_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_eot_produced ();
      Log.lemma_eot_output_written (Ghost.reveal o');
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        1sz (Ghost.reveal st1) [Body_eot ()] (Seq.create 1 4uy);
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 1sz)
        old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st1) [Body_eot ()] []);
      Log.ys_result CPI.StepOk 0sz 1sz
    }
    YP.Server_complete -> {
      (* StepOk — the EOT was acked; flip the status to Completed (cell 3uy). *)
      Log.lemma_complete_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.complete_next_state (Ghost.reveal st0));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 3uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_complete_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ys_result CPI.StepOk 0sz 0sz
    }
    YP.Server_timeout -> {
      if (s = 1uy) {
        (* Data phase, one outstanding: retransmit sent[acked]; state unchanged. *)
        Codec.ymodem_emit_data_block frame.yslf_blk frame.yslf_buf out;
        with o'. _;
        let body = extract_soh_body d o' frame.yslf_blk;
        Seq.lemma_eq_elim (L.index (Ghost.reveal st0).YP.yss_sent (Ghost.reveal st0).YP.yss_acked) (Ghost.reveal d);
        Log.lemma_timeout_data_step (Ghost.reveal st0) (Ghost.reveal body);
        let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (ymodem_serialize (Body_soh (Ghost.reveal body))));
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_timeout_data_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) (Ghost.reveal body);
        RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_ym_serialize_all_singleton (Body_soh (Ghost.reveal body));
        Seq.lemma_eq_intro (Seq.slice (Ghost.reveal o') 0 133) (ymodem_serialize (Body_soh (Ghost.reveal body)));
        Log.lemma_soh_output_written (Ghost.reveal o') (Ghost.reveal body);
        Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          133sz (Ghost.reveal st0) [Body_soh (Ghost.reveal body)]
          (ymodem_serialize (Body_soh (Ghost.reveal body)));
        fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 133sz)
          old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st0)
          [Body_soh (Ghost.reveal body)] []);
        Log.ys_result CPI.StepOk 0sz 133sz
      } else if (s = 2uy) {
        (* EOT phase: re-emit the 1-byte EOT; state unchanged. *)
        Log.lemma_timeout_eot_step (Ghost.reveal st0);
        let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (Seq.create 1 4uy));
        out.(0sz) <- 4uy;
        with o'. _;
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_timeout_eot_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_eot_produced ();
        Log.lemma_eot_output_written (Ghost.reveal o');
        Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          1sz (Ghost.reveal st0) [Body_eot ()] (Seq.create 1 4uy);
        fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 1sz)
          old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st0) [Body_eot ()] []);
        Log.ys_result CPI.StepOk 0sz 1sz
      } else {
        (* local_pre_ok(Server_timeout) is inconsistent with any other cell; a
           sound IllegalTransition no-op discharges the (dead) branch. *)
        Log.lemma_local_illegal ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.IllegalTransition 0sz 0sz)
          old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st0) [] []);
        Log.ys_result CPI.IllegalTransition 0sz 0sz
      }
    }
    YP.Server_abort -> {
      (* StepOk — cancel; flip the status to Aborted (cell 4uy). *)
      Log.lemma_abort_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.abort_next_state (Ghost.reveal st0));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 4uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_abort_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (ymodem_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (ymodem_server_local_frame_post ev frame (Log.ys_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ys_result CPI.StepOk 0sz 0sz
    }
  }
}

(* ── constructor: a freshly-created, un-started sender ────────────────────── *)

fn new_ymodem_server ()
requires emp
returns i:ymodem_server_impl
ensures ymodem_server_inv i Seq.empty Seq.empty YP.ymodem_server_initial **
        pure (Vec.is_full_vec i.status)
{
  let status = Vec.alloc 0uy 1sz;
  let progress =
    MR.alloc #_ #Log.ys_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty YP.ymodem_server_initial);
  let i = { status; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty YP.ymodem_server_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty YP.ymodem_server_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  Log.lemma_initial_trace_ok ();
  fold (ymodem_server_inv i Seq.empty Seq.empty YP.ymodem_server_initial);
  assert (pure (Vec.is_full_vec i.status));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let ymodem_server_protocol_implementation
  : CPI.protocol_implementation
      ymodem_server_impl
      YP.ymodem_server_state
      ymodem_message
      YP.ymodem_server_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> YP.ymodem_server_wfsm);
    CPI.pi_internal = CPI.no_internal_events #YP.ymodem_server_local;
    CPI.pi_internal_pending = CPI.nothing_pending #YP.ymodem_server_state;
    CPI.pi_invariant = ymodem_server_inv;
    CPI.pi_snapshot = ymodem_server_snap;
    CPI.pi_network_frame = ymodem_server_network_frame;
    CPI.pi_network_frame_pre = ymodem_server_network_frame_pre;
    CPI.pi_network_frame_post = ymodem_server_network_frame_post;
    CPI.pi_local_frame = ymodem_server_local_frame;
    CPI.pi_local_frame_pre = ymodem_server_local_frame_pre;
    CPI.pi_local_frame_post = ymodem_server_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #ymodem_server_local_frame #YP.ymodem_server_state;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #ymodem_server_local_frame #YP.ymodem_server_state #ymodem_message #unit;
    CPI.pi_invariant_valid = ymodem_server_invariant_valid;
    CPI.pi_take_snapshot = ymodem_server_take_snapshot;
    CPI.pi_recall_snapshot = ymodem_server_recall_snapshot;
    CPI.pi_process_network = ymodem_server_process_network;
    CPI.pi_process_local = ymodem_server_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #YP.ymodem_server_state #ymodem_message #YP.ymodem_server_local #unit #ymodem_server_local_frame
        ymodem_server_inv
        (fun _ -> YP.ymodem_server_wfsm);
  }
