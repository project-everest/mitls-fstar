module DH.Sample.Impl.Endpoint

(**
  DH.Sample.Impl.Endpoint — a verified Pulse implementation of the DH sample as a
  *combined role-indexed endpoint*, fully inhabiting
  `Common.ProtocolImplementation.protocol_implementation` against the pure spec
  systems `DH.Sample.StateMachine.{initiator,responder}_system`.

  ONE endpoint value plays EITHER role (fixed at construction): its immutable
  `dh_role`/`dh_me`/`dh_peer0` fields select the spec system via `dh_system_of`,
  and a single set of `process_network` / `process_local` handlers processes ALL
  events of the three-message flow

      A -> B :  A, g^x                                 (Msg1, 9 bytes)
      B -> A :  B, g^y, Sign_B(A, g^x, g^y)            (Msg2, 17 bytes)
      A -> B :  Sign_A(B, g^x, g^y)                    (Msg3, 9 bytes)

  ── Concrete mutable state & byte histories ─────────────────────────────────
  The endpoint owns THREE genuinely mutable heap boxes (`Pulse.Lib.Box`, real
  memory cells, over-written in place — not ghost witnesses):
    * `dh_state`    : `Box.box endpoint_state`  — the *current* spec state,
                      read to dispatch and over-written on every accepted
                      transition;
    * `dh_received` : `Box.box TCP.bytes`       — the live bytes received so
                      far, over-written with the exact grown history on every
                      accepted transition that consumes wire input;
    * `dh_sent`     : `Box.box TCP.bytes`       — the live bytes sent so far,
                      over-written with the exact grown history on every
                      accepted transition that emits wire output.
  Separately, a monotonic GHOST reference `MR.mref Log.dh_progress` (no heap
  cell — it lives only in the proof state) whose value is the ghost log
  `mk_log received sent st` binds the two live byte histories and the live
  state to a reachable-trace witness (see below); it is what lets a snapshot
  outlive the endpoint and be recalled later as "the state/histories can only
  have advanced".  The wire I/O itself is done by real byte reads/writes on
  the CPI-provided `input`/`out` arrays through the `read4`/`read8`/
  `write_prefix` helpers and the exact `DH.Sample.Wire` serializer; on every
  accepted step the SAME concrete bytes just read/written are the ones stored
  into `dh_received`/`dh_sent` (see e.g. the Responder `Msg1` case, which
  appends `serialize (Msg1 a gx)` to the live received box and the concrete
  output serialization `sb` to the live sent box), so the live boxes are
  literal, not merely ghost-tracked, copies of the byte histories.

  ── The separation-logic invariant `dh_inv i received sent st` ──────────────
      Box.pts_to i.dh_state st                                (live state, heap)
   ** Box.pts_to i.dh_received received                       (live received bytes, heap)
   ** Box.pts_to i.dh_sent sent                                (live sent bytes, heap)
   ** MR.pts_to i.dh_prog #1.0R (mk_log received sent st)     (ghost progress ref: same triple)
   ** pure ( st.ep_role == i.dh_role                          (role is fixed)
          /\ st.ep_me   == i.dh_me                            (identity is fixed)
          /\ (i.dh_role == Initiator ==> st.ep_peer == Some i.dh_peer0)
          /\ Log.dh_trace_ok (dh_system_of i) received sent (mk_log received sent st))
  The three `Box.pts_to` conjuncts pin `received`/`sent`/`st` to the endpoint's
  actual heap contents; the `MR.pts_to` conjunct equates that SAME triple to
  the monotone ghost log (so every live update is simultaneously recorded as
  progress); and the final pure conjunct is the crux tying both to
  `WFSM.valid_byte_trace` / state reachability: it holds an actual reachable
  spec trace whose serialized inputs/outputs are EXACTLY the byte histories.
  No unconstrained ghost witness hides a transition — each accepted step
  extends this trace by precisely the transition just taken (via
  `Log.dh_trace_ok_step`), over-writes the two live history boxes with the
  grown histories, and advances the monotone ghost reference (via
  `RTC.closure_step` + `MR.update`); error / no-progress paths (`dh_net_noop`,
  the local `IllegalTransition` cases) touch none of the three boxes and
  re-fold the invariant with the unchanged triple.

  ── Randomness injection (the responder's fresh scalar y) ───────────────────
  `responder_step` is nondeterministic in the fresh ephemeral scalar y (it
  admits ANY y reflected into `st1.ep_scalar`).  The implementation resolves the
  choice by taking y from the caller-supplied network frame field `dhnf_y`
  (documented at `dh_network_frame`), and stores exactly that y into the new
  endpoint state (`Log.resp_msg1_next … y`), which is why the emitted `Msg2` and
  the recorded transition match `responder_step` for that y.  The injection
  source is thus the FRAME (modelling ephemeral key generation as external
  input), mirroring how the initiator's scalar arrives in `StartInitiator x`.

  Verified but NOT extracted (a `protocol_implementation` dictionary is not
  Low-star; the endpoint keeps spec byte-blobs as `Seq`s).  The heavy pure
  reasoning lives in `DH.Sample.Impl.Log`.
*)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Common.ProtocolImplementation
module SM   = Common.StateMachine
module WF   = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP  = Common.TCP
module SZ   = FStar.SizeT
module U8   = FStar.UInt8
module Seq  = FStar.Seq
module L    = FStar.List.Tot
module MR   = Pulse.Lib.MonotonicGhostRef
module RTC  = FStar.ReflexiveTransitiveClosure
module Box  = Pulse.Lib.Box
module R    = Pulse.Lib.Reference

module Log  = DH.Sample.Impl.Log

open DH.Sample.Types
open DH.Sample.Crypto
open DH.Sample.Wire
open DH.Sample.StateMachine

#set-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Wire I/O helpers (real byte reads / writes on the CPI arrays)
   ─────────────────────────────────────────────────────────────────────────── *)

(** Read the 4-byte field at absolute offset `off` into a concrete `lbytes 4`,
    proved equal to the corresponding slice of the backing byte sequence. *)
fn read4 (a:array U8.t) (off:SZ.t)
  requires pts_to a 's ** pure (SZ.v off + 4 <= Seq.length 's /\ SZ.fits (SZ.v off + 4))
  returns r:lbytes 4
  ensures pts_to a 's ** pure (
    SZ.v off + 4 <= Seq.length 's /\ Seq.equal r (Seq.slice 's (SZ.v off) (SZ.v off + 4)))
{
  let b0 = a.(off);
  let b1 = a.(off `SZ.add` 1sz);
  let b2 = a.(off `SZ.add` 2sz);
  let b3 = a.(off `SZ.add` 3sz);
  let r0 = Seq.create 4 b0;
  let r1 = Seq.upd r0 1 b1;
  let r2 = Seq.upd r1 2 b2;
  let r3 = Seq.upd r2 3 b3;
  r3
}

(** Read the 8-byte field at absolute offset `off` into a concrete `lbytes 8`. *)
fn read8 (a:array U8.t) (off:SZ.t)
  requires pts_to a 's ** pure (SZ.v off + 8 <= Seq.length 's /\ SZ.fits (SZ.v off + 8))
  returns r:lbytes 8
  ensures pts_to a 's ** pure (
    SZ.v off + 8 <= Seq.length 's /\ Seq.equal r (Seq.slice 's (SZ.v off) (SZ.v off + 8)))
{
  let b0 = a.(off);
  let b1 = a.(off `SZ.add` 1sz);
  let b2 = a.(off `SZ.add` 2sz);
  let b3 = a.(off `SZ.add` 3sz);
  let b4 = a.(off `SZ.add` 4sz);
  let b5 = a.(off `SZ.add` 5sz);
  let b6 = a.(off `SZ.add` 6sz);
  let b7 = a.(off `SZ.add` 7sz);
  let r0 = Seq.create 8 b0;
  let r1 = Seq.upd r0 1 b1;
  let r2 = Seq.upd r1 2 b2;
  let r3 = Seq.upd r2 3 b3;
  let r4 = Seq.upd r3 4 b4;
  let r5 = Seq.upd r4 5 b5;
  let r6 = Seq.upd r5 6 b6;
  let r7 = Seq.upd r6 7 b7;
  r7
}

(** Copy the first `len` bytes of the concrete serialization `src` into `a`,
    leaving the buffer's prefix equal to `src`. *)
fn write_prefix (a:array U8.t) (src:Seq.seq U8.t) (len:SZ.t)
  requires pts_to a 's0 ** pure (SZ.v len == Seq.length src /\ SZ.v len <= Seq.length 's0)
  returns _:unit
  ensures exists* s'. pts_to a s' ** pure (
    Seq.length s' == Seq.length 's0 /\ SZ.v len <= Seq.length s' /\
    Seq.equal (Seq.slice s' 0 (SZ.v len)) src)
{
  let mut k = 0sz;
  while (SZ.lt !k len)
  invariant exists* (vk:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to k vk ** pts_to a sv **
    pure (Seq.length sv == Seq.length 's0 /\ SZ.v vk <= SZ.v len /\
          (forall (j:nat). j < SZ.v vk ==> Seq.index sv j == Seq.index src j))
  decreases (SZ.v len - SZ.v (!k))
  {
    let vk = !k;
    let byte = Seq.index src (SZ.v vk);
    a.(vk) <- byte;
    k := vk `SZ.add` 1sz;
  };
  with sf. assert (pts_to a sf);
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   The endpoint handle, its spec system, invariant and snapshot
   ─────────────────────────────────────────────────────────────────────────── *)

(**
  The endpoint implementation handle.  `dh_role` / `dh_me` / `dh_peer0` are
  immutable and pick the spec system (`dh_system_of`).  `dh_state`,
  `dh_received`, `dh_sent` are CONCRETE heap boxes (`Pulse.Lib.Box`, genuine
  mutable memory, over-written in place on every accepted transition) holding
  the live spec state and the live received/sent byte histories respectively.
  `dh_prog` is, by contrast, a monotone GHOST reference (no heap cell) whose
  value is the ghost log tying that same (received, sent, state) triple to a
  reachable-trace witness — see the module header and `dh_inv`.
*)
noeq
type dh_endpoint = {
  dh_role     : role;                       // fixed: which role this endpoint plays
  dh_me       : principal;                  // fixed: this endpoint's identity
  dh_peer0    : principal;                  // fixed: intended peer (used only when Initiator)
  dh_state    : Box.box endpoint_state;     // live mutable spec state (heap box)
  dh_received : Box.box TCP.bytes;          // live mutable received-byte history (heap box)
  dh_sent     : Box.box TCP.bytes;          // live mutable sent-byte history (heap box)
  dh_prog     : MR.mref Log.dh_progress;    // ghost progress ref (received/sent/state), not a heap cell
}

(** The identity-specialised spec system this endpoint refines. *)
noextract
let dh_system_of (i:dh_endpoint)
  : GTot (WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
=
  match i.dh_role with
  | Initiator -> initiator_system i.dh_me i.dh_peer0
  | Responder -> responder_system i.dh_me

(** Phase-dependent well-formedness of an endpoint state: the option-typed
    fields that a later transition consumes are already populated once the
    endpoint has advanced past the phase that installs them.  This is preserved
    by every transition (the next-state constructors set exactly these fields),
    lets the network handlers read the stored scalar/share/key without a runtime
    option check, and is what makes the `Some?.v` projections total. *)
let dh_wf (st:endpoint_state) : prop =
  ((st.ep_phase == Init_Wait2 \/ st.ep_phase == Init_Done) ==>
     (Some? st.ep_scalar /\ Some? st.ep_my_share)) /\
  (st.ep_phase == Init_Done ==>
     (Some? st.ep_peer_share /\ Some? st.ep_key)) /\
  ((st.ep_phase == Resp_Wait3 \/ st.ep_phase == Resp_Done) ==>
     (Some? st.ep_peer /\ Some? st.ep_scalar /\ Some? st.ep_my_share /\
      Some? st.ep_peer_share /\ Some? st.ep_key))

(** The separation-logic invariant (see module header).  The three
    `Box.pts_to` conjuncts equate the endpoint's LIVE heap cells to
    `(received, sent, st)`; the `MR.pts_to` conjunct equates the SAME triple
    to the ghost progress log, so both views advance together on every
    accepted step. *)
let dh_inv (i:dh_endpoint) (received sent:TCP.bytes) (st:endpoint_state) : slprop =
  Box.pts_to i.dh_state st **
  Box.pts_to i.dh_received received **
  Box.pts_to i.dh_sent sent **
  MR.pts_to i.dh_prog #1.0R (Log.mk_log received sent st) **
  pure (
    st.ep_role == i.dh_role /\
    st.ep_me == i.dh_me /\
    (i.dh_role == Initiator ==> st.ep_peer == Some i.dh_peer0) /\
    dh_wf st /\
    Log.dh_trace_ok (dh_system_of i) received sent (Log.mk_log received sent st))

(** A duplicable, monotone snapshot of the endpoint's ghost log. *)
let dh_snap (i:dh_endpoint) (received sent:TCP.bytes) (st:endpoint_state) : slprop =
  MR.snapshot i.dh_prog (Log.mk_log received sent st)

(* ───────────────────────────────────────────────────────────────────────────
   Frame types and their pre/post

   RANDOMNESS INJECTION: `dhnf_y` supplies the responder's fresh ephemeral
   scalar y for `Msg1` processing (unused by the initiator's `Msg2` processing).
   The network output buffer must have room for the largest message (`Msg2`,
   17 bytes); the local output buffer must have room for `Msg1` (9 bytes).
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type dh_network_frame = {
  dhnf_y : dh_scalar;   // fresh responder ephemeral scalar (randomness source)
}

let dh_network_frame_pre
  (frame:dh_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  pure (
    SZ.v input_len == Seq.length input_contents /\
    Seq.length old_out == SZ.v out_len /\
    SZ.v out_len >= 17)

let dh_network_frame_post
  (frame:dh_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:endpoint_state) (st1:endpoint_state)
  (consumed:TCP.bytes)
  (wire_outputs:list dh_message) (local_outputs:list local_output)
  : slprop = emp

type dh_local_frame = unit

let dh_local_frame_pre
  (ev:local_event)
  (frame:dh_local_frame)
  (st0:endpoint_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  pure (SZ.v out_len >= 9)

let dh_local_frame_post
  (ev:local_event)
  (frame:dh_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:endpoint_state) (st1:endpoint_state)
  (wire_outputs:list dh_message) (local_outputs:list local_output)
  : slprop = emp

(* ───────────────────────────────────────────────────────────────────────────
   Ghost obligations of the CPI class
   ─────────────────────────────────────────────────────────────────────────── *)

(** `pi_invariant_valid`: the invariant entails a valid byte trace. *)
ghost fn dh_invariant_valid
  (i:dh_endpoint)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased endpoint_state)
requires dh_inv i received sent st
ensures
  dh_inv i received sent st **
  pure (
    WFSM.valid_byte_trace (dh_system_of i)
      (reveal received) (reveal st) (reveal sent) Seq.empty)
{
  unfold (dh_inv i received sent st);
  Log.lemma_dh_trace_ok_valid (dh_system_of i) received sent (Log.mk_log received sent st);
  fold (dh_inv i received sent st)
}

(** `pi_take_snapshot`: mint a monotone snapshot from the invariant. *)
ghost fn dh_take_snapshot
  (i:dh_endpoint)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased endpoint_state)
requires dh_inv i received sent st
ensures
  dh_inv i received sent st **
  dh_snap i received sent st
{
  unfold (dh_inv i received sent st);
  MR.take_snapshot i.dh_prog (Log.mk_log received sent st);
  fold (dh_snap i received sent st);
  fold (dh_inv i received sent st)
}

(** `pi_recall_snapshot`: a snapshot is behind the current invariant — the state
    only advances (`state_ahead`) and the byte histories only grow
    (`histories_ahead`). *)
ghost fn dh_recall_snapshot
  (i:dh_endpoint)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased endpoint_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased endpoint_state)
requires
  dh_snap i snapshot_received snapshot_sent snapshot_state **
  dh_inv i current_received current_sent current_state
ensures
  dh_snap i snapshot_received snapshot_sent snapshot_state **
  dh_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead (dh_system_of i)
      (reveal snapshot_state) (reveal current_state) /\
    CPI.histories_ahead
      (reveal snapshot_received) (reveal snapshot_sent)
      (reveal current_received) (reveal current_sent))
{
  unfold (dh_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (dh_inv i current_received current_sent current_state);
  MR.recall_snapshot i.dh_prog;
  Log.lemma_dh_closure_ahead i.dh_me i.dh_peer0
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_dh_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  match i.dh_role {
    Initiator -> {
      assert (pure (CPI.state_ahead (initiator_system i.dh_me i.dh_peer0)
        (reveal snapshot_state) (reveal current_state)));
      fold (dh_snap i snapshot_received snapshot_sent snapshot_state);
      fold (dh_inv i current_received current_sent current_state)
    }
    Responder -> {
      assert (pure (CPI.state_ahead (responder_system i.dh_me)
        (reveal snapshot_state) (reveal current_state)));
      fold (dh_snap i snapshot_received snapshot_sent snapshot_state);
      fold (dh_inv i current_received current_sent current_state)
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   Local processing: the initiator's `StartInitiator x` event

   From the freshly-created initiator (`Init_Start`) this is a genuine `StepOk`
   that generates g^x, stores the scalar/share, emits `Msg1 me g^x` to the output
   buffer and advances to `Init_Wait2`.  For a responder, or an initiator not in
   `Init_Start`, there is no matching spec transition, so it is a sound
   `IllegalTransition` no-op that preserves the abstract state and histories.
   ─────────────────────────────────────────────────────────────────────────── *)

fn dh_process_local
  (i:dh_endpoint)
  (ev:local_event)
  (frame:dh_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased endpoint_state)
  (old_out:erased TCP.bytes)
requires
  dh_inv i received0 sent0 st0 **
  dh_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (SZ.v out_len == Seq.length old_out)
returns result:CPI.process_result
ensures exists* (received1:erased TCP.bytes) (sent1:erased TCP.bytes) (st1:erased endpoint_state)
                (out_contents:TCP.bytes) (wire_outputs:list dh_message) (local_outputs:list local_output).
  dh_inv i received1 sent1 st1 **
  dh_local_frame_post ev frame result old_out out_contents st0 st1 wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct (dh_system_of i) ev old_out out_contents out_len
      received0 sent0 st0 result received1 sent1 st1 wire_outputs local_outputs)
{
  unfold (dh_inv i received0 sent0 st0);
  unfold (dh_local_frame_pre ev frame st0 out out_len old_out);
  let st = Box.op_Bang i.dh_state;
  match ev {
    StartInitiator x -> {
      match i.dh_role {
        Initiator -> {
          match st.ep_phase {
            Init_Start -> {
              (* Genuine StepOk: emit Msg1 me g^x, advance to Init_Wait2. *)
              let gx = dh_exp x;
              let msg1 = Msg1 i.dh_me gx;
              let sb = serialize msg1;
              lemma_serialize_len msg1;
              write_prefix out sb 9sz;
              with oc. assert (pts_to out oc);
              let new_st = Log.init_start_next st x;
              let ev' : dh_event = SM.LocalEvent (StartInitiator x);
              let out' : dh_output = { SM.so_wire_outputs = [ msg1 ]; SM.so_local_outputs = [] };
              Log.lemma_init_start_step st x;
              Log.lemma_dh_step_of_initiator st ev' new_st out';
              Log.lemma_dh_advance (dh_system_of i) received0 sent0 st ev' new_st out';
              let produced : erased TCP.bytes = hide (WF.serialize_all Log.fmt [msg1]);
              let received1 : erased TCP.bytes = received0;
              let sent1 : erased TCP.bytes = hide (Seq.append sent0 produced);
              (* received0 ++ serialize_all fmt [] == received0 *)
              Seq.append_empty_r (reveal received0);
              Box.op_Colon_Equals i.dh_state new_st;
              (* dh_received is unchanged (received1 == received0); grow dh_sent by
                 exactly the concrete bytes `sb` just written to `out` (equal, by
                 `lemma_dh_serialize_all_singleton`, to the `produced` ghost bytes
                 the log now records). *)
              Log.lemma_dh_serialize_all_singleton msg1;
              Seq.lemma_eq_elim (WF.serialize_all Log.fmt [msg1]) sb;
              let sent_c = Box.op_Bang i.dh_sent;
              let new_sent = Seq.append sent_c sb;
              Box.op_Colon_Equals i.dh_sent new_sent;
              RTC.closure_step Log.dh_step_rel
                (Log.mk_log received0 sent0 st) (Log.mk_log received1 sent1 new_st);
              MR.update i.dh_prog (Log.mk_log received1 sent1 new_st);
              fold (dh_inv i received1 sent1 new_st);
              Log.lemma_output_written_msg oc msg1 9sz;
              Log.lemma_local_stepok (dh_system_of i) ev old_out oc out_len
                received0 sent0 st 9sz new_st [msg1] [] produced;
              fold (dh_local_frame_post ev frame (Log.dh_result CPI.StepOk 0sz 9sz)
                old_out oc st new_st [msg1] []);
              Log.dh_result CPI.StepOk 0sz 9sz
            }
            _ -> {
              (* Initiator not in Init_Start: sound IllegalTransition no-op. *)
              Log.lemma_local_illegal (dh_system_of i) ev old_out old_out out_len received0 sent0 st;
              fold (dh_inv i received0 sent0 st);
              fold (dh_local_frame_post ev frame (Log.dh_result CPI.IllegalTransition 0sz 0sz)
                old_out old_out st st [] []);
              Log.dh_result CPI.IllegalTransition 0sz 0sz
            }
          }
        }
        Responder -> {
          (* A responder has no local event: sound IllegalTransition no-op. *)
          Log.lemma_local_illegal (dh_system_of i) ev old_out old_out out_len received0 sent0 st;
          fold (dh_inv i received0 sent0 st);
          fold (dh_local_frame_post ev frame (Log.dh_result CPI.IllegalTransition 0sz 0sz)
            old_out old_out st st [] []);
          Log.dh_result CPI.IllegalTransition 0sz 0sz
        }
      }
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   Network processing

   Dispatch on the endpoint's role and phase and the datagram's tag/length:

     * Responder @ Resp_Start, 9-byte Msg1  →  StepOk: choose the fresh scalar y
       (frame.dhnf_y), emit Msg2, advance to Resp_Wait3.
     * Responder @ Resp_Wait3, 9-byte Msg3  →  StepOk iff Sign_A verifies: emit
       nothing, report SessionEstablished, advance to Resp_Done.
     * Initiator @ Init_Wait2, 17-byte Msg2 →  StepOk iff the responder identity
       matches the intended peer AND Sign_B verifies: emit Msg3, report
       SessionEstablished, advance to Init_Done.
     * anything else  →  sound IllegalTransition no-op (abstract state and byte
       histories preserved).
   ─────────────────────────────────────────────────────────────────────────── *)

(** The factored sound no-op: consumes the unfolded invariant resources and
    returns an `IllegalTransition` result that preserves the abstract state and
    both byte histories (the "no progress" disjunct). *)
fn dh_net_noop
  (i:dh_endpoint) (frame:dh_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (received0 sent0:erased TCP.bytes) (st:erased endpoint_state)
  (input_contents:erased TCP.bytes) (old_out:erased TCP.bytes)
requires
  Box.pts_to i.dh_state st **
  Box.pts_to i.dh_received received0 **
  Box.pts_to i.dh_sent sent0 **
  MR.pts_to i.dh_prog #1.0R (Log.mk_log received0 sent0 st) **
  pts_to input input_contents **
  pts_to out old_out **
  pure (
    (reveal st).ep_role == i.dh_role /\ (reveal st).ep_me == i.dh_me /\
    (i.dh_role == Initiator ==> (reveal st).ep_peer == Some i.dh_peer0) /\
    dh_wf st /\
    Log.dh_trace_ok (dh_system_of i) received0 sent0 (Log.mk_log received0 sent0 st) /\
    CPI.buffers_wf input_contents input_len old_out out_len)
returns result:CPI.process_result
ensures exists* (received1:erased TCP.bytes) (sent1:erased TCP.bytes) (st1:erased endpoint_state)
                (out_contents:TCP.bytes) (consumed:TCP.bytes)
                (wire_outputs:list dh_message) (local_outputs:list local_output).
  dh_inv i received1 sent1 st1 **
  dh_network_frame_post frame result input_contents input_len old_out out_contents
    st st1 consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct (dh_system_of i) input_contents input_len old_out out_contents out_len
      received0 sent0 st result received1 sent1 st1 consumed wire_outputs local_outputs)
{
  Log.lemma_network_noop (dh_system_of i) input_contents input_len old_out out_len received0 sent0 st;
  fold (dh_inv i received0 sent0 st);
  fold (dh_network_frame_post frame (Log.dh_result CPI.IllegalTransition 0sz 0sz)
    input_contents input_len old_out old_out st st Seq.empty [] []);
  Log.dh_result CPI.IllegalTransition 0sz 0sz
}

fn dh_process_network
  (i:dh_endpoint)
  (frame:dh_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased endpoint_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  dh_inv i received0 sent0 st0 **
  dh_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf input_contents input_len old_out out_len)
returns result:CPI.process_result
ensures exists* (received1:erased TCP.bytes) (sent1:erased TCP.bytes) (st1:erased endpoint_state)
                (out_contents:TCP.bytes) (consumed:TCP.bytes)
                (wire_outputs:list dh_message) (local_outputs:list local_output).
  dh_inv i received1 sent1 st1 **
  dh_network_frame_post frame result input_contents input_len old_out out_contents
    st0 st1 consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct (dh_system_of i) input_contents input_len old_out out_contents out_len
      received0 sent0 st0 result received1 sent1 st1 consumed wire_outputs local_outputs)
{
  unfold (dh_inv i received0 sent0 st0);
  unfold (dh_network_frame_pre frame input input_len out out_len input_contents old_out);
  let st = Box.op_Bang i.dh_state;
  match i.dh_role {
    Responder -> {
      match st.ep_phase {
        Resp_Start -> {
          if (SZ.eq input_len 9sz) {
            let tag = input.(0sz);
            if (U8.eq tag 1uy) {
              (* Responder Msg1: choose fresh y (frame.dhnf_y), emit Msg2. *)
              let a = read4 input 1sz;
              let gx = read4 input 5sz;
              let y = frame.dhnf_y;
              let gy = dh_exp y;
              let sigB = sign i.dh_me (transcript a gx gy);
              let msg2 = Msg2 i.dh_me gy sigB;
              let sb = serialize msg2;
              lemma_serialize_len msg2;
              write_prefix out sb 17sz;
              with oc. _;
              Log.lemma_parse_msg1 input_contents a gx;
              Log.lemma_dh_serialize_all_singleton (Msg1 a gx);
              Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg1 a gx]) input_contents;
              let new_st = Log.resp_msg1_next st a gx y;
              let ev' : dh_event = SM.WireEvent (Msg1 a gx);
              let out' : dh_output = { SM.so_wire_outputs = [msg2]; SM.so_local_outputs = [] };
              Log.lemma_resp_msg1_step st a gx y;
              Log.lemma_dh_step_of_responder st ev' new_st out';
              Log.lemma_dh_advance (dh_system_of i) received0 sent0 st ev' new_st out';
              let received1 : erased TCP.bytes = hide (Seq.append received0 (WF.serialize_all Log.fmt [Msg1 a gx]));
              let sent1 : erased TCP.bytes = hide (Seq.append sent0 (WF.serialize_all Log.fmt [msg2]));
              Box.op_Colon_Equals i.dh_state new_st;
              (* Grow the live dh_received/dh_sent boxes by exactly the concrete
                 re-serialization `serialize (Msg1 a gx)` of the datagram just
                 consumed (== serialize_all fmt [Msg1 a gx], by the singleton
                 lemma already invoked above) and the concrete `sb` just written
                 to `out` (== serialize_all fmt [msg2]). *)
              Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg1 a gx]) (serialize (Msg1 a gx));
              Log.lemma_dh_serialize_all_singleton msg2;
              Seq.lemma_eq_elim (WF.serialize_all Log.fmt [msg2]) sb;
              let received_c = Box.op_Bang i.dh_received;
              let new_received = Seq.append received_c (serialize (Msg1 a gx));
              Box.op_Colon_Equals i.dh_received new_received;
              let sent_c = Box.op_Bang i.dh_sent;
              let new_sent = Seq.append sent_c sb;
              Box.op_Colon_Equals i.dh_sent new_sent;
              RTC.closure_step Log.dh_step_rel (Log.mk_log received0 sent0 st) (Log.mk_log received1 sent1 new_st);
              MR.update i.dh_prog (Log.mk_log received1 sent1 new_st);
              fold (dh_inv i received1 sent1 new_st);
              let produced : erased TCP.bytes = hide (WF.serialize_all Log.fmt [msg2]);
              Log.lemma_consumed_msg (dh_system_of i) input_contents input_len (Msg1 a gx);
              Log.lemma_output_written_msg oc msg2 17sz;
              Log.lemma_network_stepok (dh_system_of i) input_contents input_len old_out oc out_len
                received0 sent0 st (Msg1 a gx) input_contents new_st input_len 17sz [msg2] [] produced received1 sent1;
              fold (dh_network_frame_post frame (Log.dh_result CPI.StepOk input_len 17sz)
                input_contents input_len old_out oc st new_st input_contents [msg2] []);
              Log.dh_result CPI.StepOk input_len 17sz
            } else {
              dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
            }
          } else {
            dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
          }
        }
        Resp_Wait3 -> {
          if (SZ.eq input_len 9sz) {
            let tag = input.(0sz);
            if (U8.eq tag 3uy) {
              (* Responder Msg3: verify Sign_A, then complete. *)
              let sigA = read8 input 1sz;
              let a = Some?.v st.ep_peer;
              let gx = Some?.v st.ep_peer_share;
              let gy = Some?.v st.ep_my_share;
              let key = Some?.v st.ep_key;
              let expected = sign a (transcript st.ep_me gx gy);
              if (Log.eq8 sigA expected) {
                Seq.lemma_eq_elim sigA expected;
                lemma_sign_verify a (transcript st.ep_me gx gy);
                Log.lemma_parse_msg3 input_contents sigA;
                Log.lemma_dh_serialize_all_singleton (Msg3 sigA);
                Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg3 sigA]) input_contents;
                let new_st = Log.resp_msg3_next st;
                let ev' : dh_event = SM.WireEvent (Msg3 sigA);
                let out' : dh_output = { SM.so_wire_outputs = []; SM.so_local_outputs = [ SessionEstablished a key ] };
                Log.lemma_resp_msg3_step st sigA;
                Log.lemma_dh_step_of_responder st ev' new_st out';
                Log.lemma_dh_advance (dh_system_of i) received0 sent0 st ev' new_st out';
                let received1 : erased TCP.bytes = hide (Seq.append received0 (WF.serialize_all Log.fmt [Msg3 sigA]));
                let sent1 : erased TCP.bytes = hide (Seq.append sent0 (WF.serialize_all Log.fmt ([] <: list dh_message)));
                Box.op_Colon_Equals i.dh_state new_st;
                (* Grow dh_received by the concrete re-serialization
                   `serialize (Msg3 sigA)` of the datagram just consumed
                   (== serialize_all fmt [Msg3 sigA], by the singleton lemma
                   already invoked above); dh_sent is unchanged (Resp_Wait3 ->
                   Resp_Done emits no wire output, and
                   sent0 ++ serialize_all fmt [] == sent0). *)
                Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg3 sigA]) (serialize (Msg3 sigA));
                Seq.append_empty_r (reveal sent0);
                let received_c = Box.op_Bang i.dh_received;
                let new_received = Seq.append received_c (serialize (Msg3 sigA));
                Box.op_Colon_Equals i.dh_received new_received;
                RTC.closure_step Log.dh_step_rel (Log.mk_log received0 sent0 st) (Log.mk_log received1 sent1 new_st);
                MR.update i.dh_prog (Log.mk_log received1 sent1 new_st);
                fold (dh_inv i received1 sent1 new_st);
                let produced : erased TCP.bytes = hide (WF.serialize_all Log.fmt ([] <: list dh_message));
                Log.lemma_consumed_msg (dh_system_of i) input_contents input_len (Msg3 sigA);
                Log.lemma_output_written_empty old_out;
                Log.lemma_network_stepok (dh_system_of i) input_contents input_len old_out old_out out_len
                  received0 sent0 st (Msg3 sigA) input_contents new_st input_len 0sz [] [ SessionEstablished a key ] produced received1 sent1;
                fold (dh_network_frame_post frame (Log.dh_result CPI.StepOk input_len 0sz)
                  input_contents input_len old_out old_out st new_st input_contents [] [ SessionEstablished a key ]);
                Log.dh_result CPI.StepOk input_len 0sz
              } else {
                dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
              }
            } else {
              dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
            }
          } else {
            dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
          }
        }
        _ -> {
          dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
        }
      }
    }
    Initiator -> {
      match st.ep_phase {
        Init_Wait2 -> {
          if (SZ.eq input_len 17sz) {
            let tag = input.(0sz);
            if (U8.eq tag 2uy) {
              (* Initiator Msg2: check peer identity + verify Sign_B, then emit Msg3. *)
              let b = read4 input 1sz;
              let gy = read4 input 5sz;
              let sigB = read8 input 9sz;
              let x = Some?.v st.ep_scalar;
              let gx = Some?.v st.ep_my_share;
              let peer = Some?.v st.ep_peer;
              if (Log.eq4 b peer) {
                Seq.lemma_eq_elim b peer;
                let expected = sign b (transcript st.ep_me gx gy);
                if (Log.eq8 sigB expected) {
                  Seq.lemma_eq_elim sigB expected;
                  lemma_sign_verify b (transcript st.ep_me gx gy);
                  let key = dh_agree x gy;
                  let sigA = sign st.ep_me (transcript b gx gy);
                  let msg3 = Msg3 sigA;
                  let sb = serialize msg3;
                  lemma_serialize_len msg3;
                  write_prefix out sb 9sz;
                  with oc. _;
                  Log.lemma_parse_msg2 input_contents b gy sigB;
                  Log.lemma_dh_serialize_all_singleton (Msg2 b gy sigB);
                  Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg2 b gy sigB]) input_contents;
                  let new_st = Log.init_msg2_next st gy key;
                  let ev' : dh_event = SM.WireEvent (Msg2 b gy sigB);
                  let out' : dh_output = { SM.so_wire_outputs = [msg3]; SM.so_local_outputs = [ SessionEstablished b key ] };
                  Log.lemma_init_msg2_step st b gy sigB;
                  Log.lemma_dh_step_of_initiator st ev' new_st out';
                  Log.lemma_dh_advance (dh_system_of i) received0 sent0 st ev' new_st out';
                  let received1 : erased TCP.bytes = hide (Seq.append received0 (WF.serialize_all Log.fmt [Msg2 b gy sigB]));
                  let sent1 : erased TCP.bytes = hide (Seq.append sent0 (WF.serialize_all Log.fmt [msg3]));
                  Box.op_Colon_Equals i.dh_state new_st;
                  (* Grow the live dh_received/dh_sent boxes by exactly the
                     concrete re-serialization `serialize (Msg2 b gy sigB)` of
                     the datagram just consumed (== serialize_all fmt
                     [Msg2 b gy sigB], by the singleton lemma already invoked
                     above) and the concrete `sb` just written
                     (== serialize_all fmt [msg3]). *)
                  Seq.lemma_eq_elim (WF.serialize_all Log.fmt [Msg2 b gy sigB]) (serialize (Msg2 b gy sigB));
                  Log.lemma_dh_serialize_all_singleton msg3;
                  Seq.lemma_eq_elim (WF.serialize_all Log.fmt [msg3]) sb;
                  let received_c = Box.op_Bang i.dh_received;
                  let new_received = Seq.append received_c (serialize (Msg2 b gy sigB));
                  Box.op_Colon_Equals i.dh_received new_received;
                  let sent_c = Box.op_Bang i.dh_sent;
                  let new_sent = Seq.append sent_c sb;
                  Box.op_Colon_Equals i.dh_sent new_sent;
                  RTC.closure_step Log.dh_step_rel (Log.mk_log received0 sent0 st) (Log.mk_log received1 sent1 new_st);
                  MR.update i.dh_prog (Log.mk_log received1 sent1 new_st);
                  fold (dh_inv i received1 sent1 new_st);
                  let produced : erased TCP.bytes = hide (WF.serialize_all Log.fmt [msg3]);
                  Log.lemma_consumed_msg (dh_system_of i) input_contents input_len (Msg2 b gy sigB);
                  Log.lemma_output_written_msg oc msg3 9sz;
                  Log.lemma_network_stepok (dh_system_of i) input_contents input_len old_out oc out_len
                    received0 sent0 st (Msg2 b gy sigB) input_contents new_st input_len 9sz [msg3] [ SessionEstablished b key ] produced received1 sent1;
                  fold (dh_network_frame_post frame (Log.dh_result CPI.StepOk input_len 9sz)
                    input_contents input_len old_out oc st new_st input_contents [msg3] [ SessionEstablished b key ]);
                  Log.dh_result CPI.StepOk input_len 9sz
                } else {
                  dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
                }
              } else {
                dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
              }
            } else {
              dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
            }
          } else {
            dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
          }
        }
        _ -> {
          dh_net_noop i frame input input_len out out_len received0 sent0 st input_contents old_out
        }
      }
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   Constructors: a freshly-created endpoint of either role, at its spec initial
   state with empty byte histories.
   ─────────────────────────────────────────────────────────────────────────── *)

(** A fresh initiator that intends to talk to [peer0]. *)
fn new_dh_initiator (me:principal) (peer0:principal)
requires emp
returns i:dh_endpoint
ensures
  dh_inv i Seq.empty Seq.empty (initial_initiator me peer0) **
  pure (i.dh_role == Initiator /\ i.dh_me == me /\ i.dh_peer0 == peer0)
{
  let stbox = Box.alloc (initial_initiator me peer0);
  let rbox : Box.box TCP.bytes = Box.alloc #TCP.bytes Seq.empty;
  let sbox : Box.box TCP.bytes = Box.alloc #TCP.bytes Seq.empty;
  let prog = MR.alloc #_ #Log.dh_progress (Log.mk_log Seq.empty Seq.empty (initial_initiator me peer0));
  let i = { dh_role = Initiator; dh_me = me; dh_peer0 = peer0;
            dh_state = stbox; dh_received = rbox; dh_sent = sbox; dh_prog = prog };
  rewrite (Box.pts_to stbox (initial_initiator me peer0)) as (Box.pts_to i.dh_state (initial_initiator me peer0));
  rewrite (Box.pts_to rbox (Seq.empty #U8.t)) as (Box.pts_to i.dh_received (Seq.empty #U8.t));
  rewrite (Box.pts_to sbox (Seq.empty #U8.t)) as (Box.pts_to i.dh_sent (Seq.empty #U8.t));
  rewrite (MR.pts_to prog #1.0R (Log.mk_log Seq.empty Seq.empty (initial_initiator me peer0))) as
          (MR.pts_to i.dh_prog #1.0R (Log.mk_log Seq.empty Seq.empty (initial_initiator me peer0)));
  Log.lemma_dh_initial_trace_ok (dh_system_of i);
  fold (dh_inv i Seq.empty Seq.empty (initial_initiator me peer0));
  i
}

(** A fresh responder (its peer is learned from Msg1). *)
fn new_dh_responder (me:principal)
requires emp
returns i:dh_endpoint
ensures
  dh_inv i Seq.empty Seq.empty (initial_responder me) **
  pure (i.dh_role == Responder /\ i.dh_me == me)
{
  let stbox = Box.alloc (initial_responder me);
  let rbox : Box.box TCP.bytes = Box.alloc #TCP.bytes Seq.empty;
  let sbox : Box.box TCP.bytes = Box.alloc #TCP.bytes Seq.empty;
  let prog = MR.alloc #_ #Log.dh_progress (Log.mk_log Seq.empty Seq.empty (initial_responder me));
  let i = { dh_role = Responder; dh_me = me; dh_peer0 = me;
            dh_state = stbox; dh_received = rbox; dh_sent = sbox; dh_prog = prog };
  rewrite (Box.pts_to stbox (initial_responder me)) as (Box.pts_to i.dh_state (initial_responder me));
  rewrite (Box.pts_to rbox (Seq.empty #U8.t)) as (Box.pts_to i.dh_received (Seq.empty #U8.t));
  rewrite (Box.pts_to sbox (Seq.empty #U8.t)) as (Box.pts_to i.dh_sent (Seq.empty #U8.t));
  rewrite (MR.pts_to prog #1.0R (Log.mk_log Seq.empty Seq.empty (initial_responder me))) as
          (MR.pts_to i.dh_prog #1.0R (Log.mk_log Seq.empty Seq.empty (initial_responder me)));
  Log.lemma_dh_initial_trace_ok (dh_system_of i);
  fold (dh_inv i Seq.empty Seq.empty (initial_responder me));
  i
}

(* ───────────────────────────────────────────────────────────────────────────
   The `Common.ProtocolImplementation.protocol_implementation` instance: a fully
   inhabited refinement dictionary tying the DH endpoint to the spec systems.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
instance dh_protocol_implementation
  : CPI.protocol_implementation dh_endpoint endpoint_state dh_message local_event local_output
  =
  {
    CPI.pi_system              = dh_system_of;
    CPI.pi_invariant           = dh_inv;
    CPI.pi_snapshot            = dh_snap;
    CPI.pi_network_frame       = dh_network_frame;
    CPI.pi_network_frame_pre   = dh_network_frame_pre;
    CPI.pi_network_frame_post  = dh_network_frame_post;
    CPI.pi_local_frame         = dh_local_frame;
    CPI.pi_local_frame_pre     = dh_local_frame_pre;
    CPI.pi_local_frame_post    = dh_local_frame_post;
    CPI.pi_invariant_valid     = dh_invariant_valid;
    CPI.pi_take_snapshot       = dh_take_snapshot;
    CPI.pi_recall_snapshot     = dh_recall_snapshot;
    CPI.pi_process_network     = dh_process_network;
    CPI.pi_process_local       = dh_process_local;
  }
