module HTTP.Impl.Client.CanonicalProtocol

(**
  The HTTP/1.1 Content-Length **body receiver** as a verified instance of
  `Common.ProtocolImplementation.protocol_implementation`, refining the spec
  state machine `HTTP.Protocol.Length.http_client_wfsm`.  Dual to
  `HTTP.Impl.Server.CanonicalProtocol`.

    * `pi_process_local` handles the receiver's single local event
      `Client_start filename len`: it binds the target and the declared
      Content-Length learned from the response head.  Nothing is emitted.

    * `pi_process_network` consumes one `Msg_body` datagram.  A body segment is
      *self-delimiting by the datagram discipline*: `http_parse` on a `body_ok`
      buffer yields exactly `Msg_body <that buffer>` with an empty residual
      (`lemma_parse_body_exact`), so the whole input is consumed.  The handler
      checks `body_ok` at runtime (a body may not start with 'G' or 'H', which
      is what keeps it unambiguous against a request/response head) and refuses
      with a sound no-progress `IllegalTransition` when the segment is not
      acceptable — including when the transfer has already completed.

  The receiver emits nothing, ever (`so_wire_outputs` is always `[]`), which is
  the dual of the sender being input-free; `Log.lemma_client_trace_no_wire_outputs`
  is what discharges half of `valid_byte_trace` on this side.

  Since `hcs_received` / `hcs_len` are ghost, the handle carries a concrete
  *remaining-bytes* counter — the residual of the declared Content-Length — tied
  to the abstract state by the invariant.  That single machine integer is enough
  to decide, at run time, whether an arriving segment completes the transfer,
  and hence to keep the concrete status flag in sync with `hcs_status`.
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
module Vec = Pulse.Lib.Vec

module HP = HTTP.Protocol.Length
module Log = HTTP.Impl.Client.Log

open HTTP.Wire.Length

#set-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* ── the concrete residual of the declared Content-Length ─────────────────── *)

noextract
let hc_remaining (st:HP.http_client_state) : nat =
  let got = Seq.length (FT.ft_concat st.HP.hcs_received) in
  if st.HP.hcs_len <= got then 0 else st.HP.hcs_len - got

(* Appending one segment adds exactly its length to the reassembled body. *)
let lemma_recv_len (rcvd:list TCP.bytes) (d:TCP.bytes)
  : Lemma
      (Seq.length (FT.ft_concat (L.append rcvd [d])) ==
       Seq.length (FT.ft_concat rcvd) + Seq.length d)
=
  HP.lemma_ft_concat_append rcvd [d];
  Seq.append_empty_r d

(* ── the receiver implementation handle ───────────────────────────────────── *)

noeq
type http_client_impl = {
  status    : Vec.vec U8.t;                        // single cell: 0/1/2 status flag
  remaining : Vec.vec SZ.t;                        // single cell: bytes still expected
  progress  : MR.mref Log.hc_state_ahead_preorder; // ghost history under the RTC preorder
}

let http_client_inv
  (i:http_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:HP.http_client_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t) (cvs:Seq.seq SZ.t).
     Vec.pts_to i.status svs **
     Vec.pts_to i.remaining cvs **
     pure (Seq.length svs == 1 /\ Log.hc_status_flag_ok (Seq.index svs 0) st /\
           Seq.length cvs == 1 /\ SZ.v (Seq.index cvs 0) == hc_remaining st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.client_trace_ok received sent (Log.mk_log received sent st))

let http_client_snap
  (i:http_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:HP.http_client_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* ── frames ───────────────────────────────────────────────────────────────── *)

noeq
type http_client_network_frame = { hcnf_unit : unit }

let http_client_network_frame_pre
  (frame:http_client_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  pure (
    SZ.v input_len == Seq.length input_contents /\
    Seq.length old_out == SZ.v out_len)

let http_client_network_frame_post
  (frame:http_client_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:HP.http_client_state) (st1:HP.http_client_state)
  (consumed:TCP.bytes)
  (wire_outputs:list http_message) (local_outputs:list unit)
  : slprop =
  pure (local_outputs == [] /\ wire_outputs == [] /\ Seq.equal out_contents old_out)

(* The receiver's only local event carries the declared Content-Length, which the
   concrete side must know as a machine integer. *)
noeq
type http_client_local_frame = { hclf_len : SZ.t }

unfold
let client_local_pre_ok
  (ev:HP.http_client_local) (st0:HP.http_client_state) (len:SZ.t) : prop =
  match ev with
  | HP.Client_start filename l -> st0.HP.hcs_filename == None /\ l == SZ.v len

let http_client_local_frame_pre
  (ev:HP.http_client_local)
  (frame:http_client_local_frame)
  (st0:HP.http_client_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  pure (client_local_pre_ok ev st0 frame.hclf_len)

unfold
let hc_local_post_ok
  (ev:HP.http_client_local) (st0 st1:HP.http_client_state) : prop =
  match ev with
  | HP.Client_start filename l -> st1 == Log.client_start_next_state filename l

let http_client_local_frame_post
  (ev:HP.http_client_local)
  (frame:http_client_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:HP.http_client_state) (st1:HP.http_client_state)
  (wire_outputs:list http_message) (local_outputs:list unit)
  : slprop =
  pure (local_outputs == [] /\ wire_outputs == [] /\ hc_local_post_ok ev st0 st1)

(* ── ghost obligations ────────────────────────────────────────────────────── *)

ghost fn http_client_invariant_valid
  (i:http_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased HP.http_client_state)
requires http_client_inv i received sent st
ensures
  http_client_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (HP.http_client_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (http_client_inv i received sent st);
  with svs cvs. _;
  Log.lemma_client_trace_ok_valid received sent (Log.mk_log received sent st);
  fold (http_client_inv i received sent st)
}

ghost fn http_client_take_snapshot
  (i:http_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased HP.http_client_state)
requires http_client_inv i received sent st
ensures
  http_client_inv i received sent st **
  http_client_snap i received sent st
{
  unfold (http_client_inv i received sent st);
  with svs cvs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
  fold (http_client_snap i received sent st);
  fold (http_client_inv i received sent st)
}

ghost fn http_client_recall_snapshot
  (i:http_client_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased HP.http_client_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased HP.http_client_state)
requires
  http_client_snap i snapshot_received snapshot_sent snapshot_state **
  http_client_inv i current_received current_sent current_state
ensures
  http_client_snap i snapshot_received snapshot_sent snapshot_state **
  http_client_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (HP.http_client_wfsm)
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  unfold (http_client_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (http_client_inv i current_received current_sent current_state);
  with svs cvs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_hc_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_hc_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (http_client_snap i snapshot_received snapshot_sent snapshot_state);
  fold (http_client_inv i current_received current_sent current_state)
}

ghost fn hide_body_payload (c:erased TCP.bytes)
requires pure (body_ok (reveal c))
returns pl : erased body_payload
ensures pure ((reveal pl <: Seq.seq U8.t) == reveal c)
{
  let b : body_payload = reveal c;
  hide b
}

(* ── the runtime `body_ok` test ────────────────────────────────────────────────

   A body segment may not begin with 'G' (0x47) or 'H' (0x48): that is exactly
   what keeps it unambiguous against a "GET " request line or an "HTTP/1.1 "
   status line on the wire. *)
fn http_body_ok (input:array U8.t) (input_len:SZ.t)
requires pts_to input 'c ** pure (SZ.v input_len == Seq.length 'c)
returns b:bool
ensures pts_to input 'c ** pure (b == body_ok 'c)
{
  if (SZ.eq input_len 0sz) {
    true
  } else {
    let b0 = input.(0sz);
    (U8.ne b0 0x47uy && U8.ne b0 0x48uy)
  }
}

(* ── network processing: consume one body segment ─────────────────────────── *)

fn http_client_process_network
  (i:http_client_impl)
  (frame:http_client_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased HP.http_client_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  http_client_inv i received0 sent0 st0 **
  http_client_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased HP.http_client_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list http_message)
                (local_outputs:list unit).
  http_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  http_client_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (HP.http_client_wfsm)
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
  unfold (http_client_inv i received0 sent0 st0);
  with svs cvs. _;
  unfold (http_client_network_frame_pre frame input input_len out out_len input_contents old_out);
  let sflag = Vec.op_Array_Access i.status 0sz;
  let rem = Vec.op_Array_Access i.remaining 0sz;
  let ok = http_body_ok input input_len;
  if (U8.eq sflag 1uy && ok) {
    (* StepOk — the segment is acceptable and the transfer is in progress. *)
    let p = hide_body_payload input_contents;
    let done = SZ.lte rem input_len;
    let st1 = Ghost.hide (Log.recv_next_state (Ghost.reveal st0) (Ghost.reveal p));
    lemma_recv_len (Ghost.reveal st0).HP.hcs_received (Ghost.reveal p);
    let flag = (if done then 2uy else 1uy);
    let newrem = (if done then 0sz else SZ.sub rem input_len);
    Vec.op_Array_Assignment i.status 0sz flag;
    Vec.op_Array_Assignment i.remaining 0sz newrem;
    with cvs2. _;
    let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal p <: TCP.bytes));
    let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_recv_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) (Ghost.reveal p);
    RTC.closure_step Log.hc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
    MR.update i.progress (Ghost.reveal log1);
    fold (http_client_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
    Log.lemma_recv_step (Ghost.reveal st0) (Ghost.reveal p);
    Log.lemma_client_output_written_empty (Ghost.reveal old_out);
    Seq.append_empty_r (Ghost.reveal sent0);
    Log.lemma_client_network_stepok
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      (Ghost.reveal p) (Ghost.reveal st1) [] Seq.empty;
    fold (http_client_network_frame_post
      frame (Log.hc_result CPI.StepOk input_len 0sz) input_contents input_len
      old_out (Ghost.reveal old_out)
      (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
    Log.hc_result CPI.StepOk input_len 0sz
  } else {
    (* Not acceptable (already completed, not yet started, or the bytes could be
       confused with a request/response head): a sound no-progress no-op. *)
    fold (http_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    Log.lemma_client_network_noop
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    fold (http_client_network_frame_post
      frame (Log.hc_result CPI.IllegalTransition 0sz 0sz) input_contents input_len
      old_out (Ghost.reveal old_out)
      (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
    Log.hc_result CPI.IllegalTransition 0sz 0sz
  }
}

(* ── local processing: `Client_start` ─────────────────────────────────────── *)

fn http_client_process_local
  (i:http_client_impl)
  (ev:HP.http_client_local)
  (frame:http_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased HP.http_client_state)
  (old_out:erased TCP.bytes)
requires
  http_client_inv i received0 sent0 st0 **
  http_client_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (
    SZ.v out_len == Seq.length (Ghost.reveal old_out) /\
    ~ (CPI.no_internal_events #HP.http_client_local ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased HP.http_client_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list http_message)
                (local_outputs:list unit).
  http_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  http_client_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1) wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (HP.http_client_wfsm)
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
  unfold (http_client_inv i received0 sent0 st0);
  with svs cvs. _;
  unfold (http_client_local_frame_pre ev frame st0 out out_len old_out);
  match ev {
    HP.Client_start filename len -> {
      Log.lemma_client_start_step (Ghost.reveal st0) filename len;
      let st1 = Ghost.hide (Log.client_start_next_state filename len);
      Vec.op_Array_Assignment i.status 0sz 1uy;
      Vec.op_Array_Assignment i.remaining 0sz frame.hclf_len;
      with cvs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_client_start_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) filename len;
      RTC.closure_step Log.hc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (http_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_client_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_client_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) (Ghost.reveal st1)
        [] Seq.empty;
      fold (http_client_local_frame_post ev frame (Log.hc_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.hc_result CPI.StepOk 0sz 0sz
    }
  }
}

(* ── constructor ──────────────────────────────────────────────────────────── *)

fn new_http_client ()
requires emp
returns i:http_client_impl
ensures http_client_inv i Seq.empty Seq.empty HP.http_client_initial **
        pure (Vec.is_full_vec i.status /\ Vec.is_full_vec i.remaining)
{
  let status = Vec.alloc 0uy 1sz;
  let remaining = Vec.alloc 0sz 1sz;
  let progress =
    MR.alloc #_ #Log.hc_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty HP.http_client_initial);
  let i = { status; remaining; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty HP.http_client_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty HP.http_client_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  with cv. rewrite (Vec.pts_to remaining cv) as (Vec.pts_to i.remaining cv);
  Log.lemma_client_initial_trace_ok ();
  fold (http_client_inv i Seq.empty Seq.empty HP.http_client_initial);
  assert (pure (Vec.is_full_vec i.status /\ Vec.is_full_vec i.remaining));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

let http_client_protocol_implementation
  : CPI.protocol_implementation
      http_client_impl
      HP.http_client_state
      http_message
      HP.http_client_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> HP.http_client_wfsm);
    CPI.pi_internal = CPI.no_internal_events #HP.http_client_local;
    CPI.pi_internal_pending = CPI.nothing_pending #HP.http_client_state;
    CPI.pi_invariant = http_client_inv;
    CPI.pi_snapshot = http_client_snap;
    CPI.pi_network_frame = http_client_network_frame;
    CPI.pi_network_frame_pre = http_client_network_frame_pre;
    CPI.pi_network_frame_post = http_client_network_frame_post;
    CPI.pi_local_frame = http_client_local_frame;
    CPI.pi_local_frame_pre = http_client_local_frame_pre;
    CPI.pi_local_frame_post = http_client_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #http_client_local_frame #HP.http_client_state;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #http_client_local_frame #HP.http_client_state #http_message #unit;
    CPI.pi_invariant_valid = http_client_invariant_valid;
    CPI.pi_take_snapshot = http_client_take_snapshot;
    CPI.pi_recall_snapshot = http_client_recall_snapshot;
    CPI.pi_process_network = http_client_process_network;
    CPI.pi_process_local = http_client_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #HP.http_client_state #http_message #HP.http_client_local #unit #http_client_local_frame
        http_client_inv
        (fun _ -> HP.http_client_wfsm);
  }
