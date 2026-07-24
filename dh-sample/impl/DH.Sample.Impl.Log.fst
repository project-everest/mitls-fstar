module DH.Sample.Impl.Log

(**
  DH.Sample.Impl.Log — the pure (non-Pulse) ghost-log / reachable-trace engine
  underlying the combined role-indexed endpoint implementation
  `DH.Sample.Impl.Endpoint`, which refines
  `Common.ProtocolImplementation.protocol_implementation` against the DH sample
  spec state machines `DH.Sample.StateMachine.{initiator,responder}_system`.

  All of the delicate separation-logic-free reasoning lives here so that the
  Pulse shell in `DH.Sample.Impl.Endpoint` only has to *fold/unfold* an invariant
  and *call* these lemmas (mirroring how `TFTP.Impl.Client.CanonicalProtocol`
  delegates to `TFTP.Impl.Client.Log`).  Nothing in this module depends on any
  Dolev–Yao / DY* development.

  ── The ghost log ──────────────────────────────────────────────────────────
  A `dh_log` bundles the two byte histories (`dl_received`, `dl_sent`) with the
  abstract spec state (`dl_state : endpoint_state`).  A Pulse endpoint owns a
  monotonic ghost reference over `dh_progress` (below), whose value is exactly
  `mk_log received sent st`, so the invariant ties the physical byte histories
  and the concrete endpoint state to a single ghost log that only ever moves
  forward.

  ── The unified step relation (system-independent) ─────────────────────────
  `dh_step` dispatches on the endpoint's role to the spec's `initiator_step`
  (role `Initiator`) or `responder_step` (role `Responder`).  Because the role
  never changes and each spec relation reads the acting party's identity from
  the *state* (not from the machine), `dh_step` needs no identity parameters, so
  its reflexive-transitive closure `dh_progress` is a single global preorder —
  the monotonicity relation for every endpoint's ghost reference regardless of
  role or identity.

  ── The two obligations discharged from `dh_progress` ──────────────────────
    * `state_ahead` (monotone snapshots): a `dh_progress` chain from `log0` to
      `log1` yields `CPI.state_ahead system log0.state log1.state` for the
      role-appropriate `system`; crucially `CPI.state_ahead system` inspects only
      `system`'s *step* relation (never its initial state), so the fact holds for
      the endpoint's identity-specialised system.  Proved by RTC induction over a
      single motive bundling role-preservation with both role directions.
    * `histories_ahead`: each step only ever *appends* to both byte histories, so
      `dh_progress` implies `TCP.bytes_extends` on both.

  ── `valid_byte_trace` (the crux) ──────────────────────────────────────────
  The DH wire format IS a strong-prefix parser, but — as in the TFTP/YMODEM
  client instances — we discharge `WFSM.valid_byte_trace` through its DATAGRAM
  (serialize-equality) disjunct, which holds *by construction*: `dh_trace_ok`
  carries a reachable trace whose serialized inputs/outputs are *exactly* the
  byte histories, grown one transition at a time.
*)

module L    = FStar.List.Tot
module Seq  = FStar.Seq
module ID   = FStar.IndefiniteDescription
module Pre  = FStar.Preorder
module RTC  = FStar.ReflexiveTransitiveClosure
module SM   = Common.StateMachine
module WF   = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP  = Common.TCP
module CPI  = Common.ProtocolImplementation
module SZ   = FStar.SizeT
module U8   = FStar.UInt8

open DH.Sample.Types
open DH.Sample.Crypto
open DH.Sample.Wire
open DH.Sample.StateMachine

#set-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Section 1.  The ghost log and its abbreviations
   ─────────────────────────────────────────────────────────────────────────── *)

(** The endpoint ghost log: byte histories paired with the abstract state. *)
noeq
type dh_log = {
  dl_received : TCP.bytes;        // all wire bytes received (parsed DH messages)
  dl_sent     : TCP.bytes;        // all wire bytes emitted (serialized DH messages)
  dl_state    : endpoint_state;   // abstract spec state
}

(** The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:endpoint_state) : dh_log =
  { dl_received = received; dl_sent = sent; dl_state = st }

(** A trace of the composed endpoint machine. *)
noextract
let dh_trace = list (SM.transition endpoint_state dh_message local_event local_output)

(** The wire format shared by both role systems (an abbreviation). *)
noextract
let fmt : WF.wire_format dh_message = dh_wire_format

(* ───────────────────────────────────────────────────────────────────────────
   Section 2.  Generic serialize / trace list-append lemmas
   (structural facts about `serialize_all`, `trace_wire_outputs`,
    `trace_input_messages`; independent of the DH specifics)
   ─────────────────────────────────────────────────────────────────────────── *)

(** Serializing a concatenation is the concatenation of the serializations
    (generic over the wire format `f`, so it serves both `fmt` and an arbitrary
    endpoint system's `wfsm_wire_format`). *)
let rec lemma_serialize_all_append (f:WF.wire_format dh_message) (l1 l2:list dh_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all f (L.append l1 l2))
          (Seq.append (WF.serialize_all f l1) (WF.serialize_all f l2)))
      (decreases l1)
=
  match l1 with
  | [] -> Seq.append_empty_l (WF.serialize_all f l2)
  | x :: r ->
    lemma_serialize_all_append f r l2;
    Seq.lemma_eq_elim
      (WF.serialize_all f (L.append r l2))
      (Seq.append (WF.serialize_all f r) (WF.serialize_all f l2));
    Seq.append_assoc
      (f.WF.wf_serialize x)
      (WF.serialize_all f r)
      (WF.serialize_all f l2)

(** `serialize_all` of a singleton is the serialization of the sole element. *)
let lemma_dh_serialize_all_singleton (m:dh_message)
  : Lemma (Seq.equal (WF.serialize_all fmt [m]) (serialize m))
=
  Seq.append_empty_r (serialize m)

(** The wire outputs of a concatenated trace concatenate. *)
let rec lemma_trace_wire_outputs_append (t1 t2:dh_trace)
  : Lemma
      (ensures
        SM.trace_wire_outputs (L.append t1 t2) ==
        L.append (SM.trace_wire_outputs t1) (SM.trace_wire_outputs t2))
      (decreases t1)
=
  match t1 with
  | [] -> ()
  | tr :: rest ->
    lemma_trace_wire_outputs_append rest t2;
    L.append_assoc
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest)
      (SM.trace_wire_outputs t2)

(** Likewise for the input messages of a concatenated trace. *)
let rec lemma_trace_input_messages_append (t1 t2:dh_trace)
  : Lemma
      (ensures
        WFSM.trace_input_messages (L.append t1 t2) ==
        L.append (WFSM.trace_input_messages t1) (WFSM.trace_input_messages t2))
      (decreases t1)
=
  match t1 with
  | [] -> ()
  | tr :: rest ->
    lemma_trace_input_messages_append rest t2;
    L.append_assoc
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest)
      (WFSM.trace_input_messages t2)

(* ───────────────────────────────────────────────────────────────────────────
   Section 3.  The unified role-dispatching step and its RTC-closure preorder
   ─────────────────────────────────────────────────────────────────────────── *)

(**
  The combined step: dispatch on the acting endpoint's role.  Because
  `initiator_step` (resp. `responder_step`) internally requires
  `st0.ep_role == Initiator` (resp. `Responder`), the dispatch is faithful — for
  a role-`Initiator` state only `initiator_step` can hold, and vice versa.
*)
let dh_step
  (st0:endpoint_state) (ev:dh_event) (st1:endpoint_state) (out:dh_output)
  : prop =
  match st0.ep_role with
  | Initiator -> initiator_step st0 ev st1 out
  | Responder -> responder_step st0 ev st1 out

(**
  One log step: some event `ev` and step output `out` carry `log0` to `log1`,
  growing `dl_received` by the serialized *input* messages of `ev` (a singleton
  for a `WireEvent`, empty for a `LocalEvent`) and `dl_sent` by the serialized
  *wire outputs* of the step.
*)
let dh_step_body
  (log0 log1:dh_log)
  (ev:dh_event)
  (out:dh_output)
  : prop =
  dh_step log0.dl_state ev log1.dl_state out /\
  Seq.equal log1.dl_received
    (Seq.append log0.dl_received
       (WF.serialize_all fmt (WFSM.event_input_messages ev))) /\
  Seq.equal log1.dl_sent
    (Seq.append log0.dl_sent
       (WF.serialize_all fmt out.SM.so_wire_outputs))

let dh_step_rel (log0 log1:dh_log) : prop =
  exists ev out. dh_step_body log0 log1 ev out

(** Introduce a step from concrete witnesses (existential intro). *)
let lemma_dh_step_rel_intro
  (log0 log1:dh_log) (ev:dh_event) (out:dh_output)
  : Lemma (requires dh_step_body log0 log1 ev out) (ensures dh_step_rel log0 log1)
= ()

(** The monotonicity preorder: the reflexive-transitive closure of `dh_step_rel`. *)
noextract
let dh_progress : Pre.preorder dh_log = RTC.closure dh_step_rel

(* ───────────────────────────────────────────────────────────────────────────
   Section 4.  Role preservation (a single step, then the closure)
   ─────────────────────────────────────────────────────────────────────────── *)

(** A single spec step never changes the acting endpoint's role. *)
let lemma_dh_step_role
  (st0:endpoint_state) (ev:dh_event) (st1:endpoint_state) (out:dh_output)
  : Lemma (requires dh_step st0 ev st1 out) (ensures st1.ep_role == st0.ep_role)
= ()

let lemma_dh_step_rel_role (log0 log1:dh_log)
  : Lemma (requires dh_step_rel log0 log1)
          (ensures log1.dl_state.ep_role == log0.dl_state.ep_role)
= ()

(* ───────────────────────────────────────────────────────────────────────────
   Section 5.  state_ahead:  a `dh_progress` chain advances the state machine
   (for the role-appropriate identity-specialised system)
   ─────────────────────────────────────────────────────────────────────────── *)

(** A single initiator step is a one-transition run of *any* initiator system. *)
let lemma_dh_step_ahead_init (me peer:principal) (log0 log1:dh_log)
  : Lemma
      (requires dh_step_rel log0 log1 /\ log0.dl_state.ep_role == Initiator)
      (ensures CPI.state_ahead (initiator_system me peer) log0.dl_state log1.dl_state)
=
  let ev = ID.indefinite_description_ghost dh_event
             (fun ev -> exists out. dh_step_body log0 log1 ev out) in
  let out = ID.indefinite_description_ghost dh_output
              (fun out -> dh_step_body log0 log1 ev out) in
  let tr : SM.transition endpoint_state dh_message local_event local_output =
    { SM.tr_event = ev; SM.tr_next_state = log1.dl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    (initiator_system me peer).WFSM.wfsm_state_machine log0.dl_state [tr] log1.dl_state)

(** A single responder step is a one-transition run of *any* responder system. *)
let lemma_dh_step_ahead_resp (me:principal) (log0 log1:dh_log)
  : Lemma
      (requires dh_step_rel log0 log1 /\ log0.dl_state.ep_role == Responder)
      (ensures CPI.state_ahead (responder_system me) log0.dl_state log1.dl_state)
=
  let ev = ID.indefinite_description_ghost dh_event
             (fun ev -> exists out. dh_step_body log0 log1 ev out) in
  let out = ID.indefinite_description_ghost dh_output
              (fun out -> dh_step_body log0 log1 ev out) in
  let tr : SM.transition endpoint_state dh_message local_event local_output =
    { SM.tr_event = ev; SM.tr_next_state = log1.dl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    (responder_system me).WFSM.wfsm_state_machine log0.dl_state [tr] log1.dl_state)

(**
  The bundled induction motive: role-preservation together with both role
  directions of `state_ahead`.  Bundling is what makes transitivity go through
  (the middle log's role is known to match, so the correct disjunct chains).
*)
let dh_ahead_motive (me peer:principal) (x y:dh_log) : prop =
  (x.dl_state.ep_role == y.dl_state.ep_role) /\
  (x.dl_state.ep_role == Initiator ==>
     CPI.state_ahead (initiator_system me peer) x.dl_state y.dl_state) /\
  (x.dl_state.ep_role == Responder ==>
     CPI.state_ahead (responder_system me) x.dl_state y.dl_state)

let lemma_dh_closure_ahead (me peer:principal) (log0 log1:dh_log)
  : Lemma (requires dh_progress log0 log1)
          (ensures dh_ahead_motive me peer log0 log1)
=
  RTC.induct dh_step_rel (dh_ahead_motive me peer)
    (fun x ->
       SM.lemma_state_evolves_refl (initiator_system me peer).WFSM.wfsm_state_machine x.dl_state;
       SM.lemma_state_evolves_refl (responder_system me).WFSM.wfsm_state_machine x.dl_state)
    (fun x y ->
       lemma_dh_step_rel_role x y;
       Classical.move_requires (lemma_dh_step_ahead_init me peer x) y;
       Classical.move_requires (lemma_dh_step_ahead_resp me x) y)
    (fun x y z ->
       Classical.move_requires
         (SM.lemma_state_evolves_trans (initiator_system me peer).WFSM.wfsm_state_machine
            x.dl_state y.dl_state) z.dl_state;
       Classical.move_requires
         (SM.lemma_state_evolves_trans (responder_system me).WFSM.wfsm_state_machine
            x.dl_state y.dl_state) z.dl_state)
    log0 log1 ()

(* ───────────────────────────────────────────────────────────────────────────
   Section 6.  histories_ahead:  each step only appends to both byte histories
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_dh_step_histories_ahead (log0 log1:dh_log)
  : Lemma
      (requires dh_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.dl_received log1.dl_received /\
        TCP.bytes_extends log0.dl_sent log1.dl_sent)
=
  let ev = ID.indefinite_description_ghost dh_event
             (fun ev -> exists out. dh_step_body log0 log1 ev out) in
  let out = ID.indefinite_description_ghost dh_output
              (fun out -> dh_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.dl_received log1.dl_received
    (WF.serialize_all fmt (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.dl_sent log1.dl_sent
    (WF.serialize_all fmt out.SM.so_wire_outputs)

let lemma_dh_closure_histories_ahead (log0 log1:dh_log)
  : Lemma
      (requires dh_progress log0 log1)
      (ensures
        TCP.bytes_extends log0.dl_received log1.dl_received /\
        TCP.bytes_extends log0.dl_sent log1.dl_sent)
=
  RTC.induct dh_step_rel
    (fun x y ->
       TCP.bytes_extends x.dl_received y.dl_received /\
       TCP.bytes_extends x.dl_sent y.dl_sent)
    (fun x ->
       CPI.lemma_bytes_extends_refl x.dl_received;
       CPI.lemma_bytes_extends_refl x.dl_sent)
    (fun x y -> lemma_dh_step_histories_ahead x y)
    (fun x y z ->
       CPI.lemma_bytes_extends_trans x.dl_received y.dl_received z.dl_received;
       CPI.lemma_bytes_extends_trans x.dl_sent y.dl_sent z.dl_sent)
    log0 log1 ()

(* ───────────────────────────────────────────────────────────────────────────
   Section 7.  The canonical reachable-trace invariant `dh_trace_ok`
   (parameterised by the endpoint's identity-specialised `system`)
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let dh_trace_witness
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (received sent:TCP.bytes)
  (log:dh_log)
  (trace:dh_trace)
  : prop =
  SM.trace_reaches
    system.WFSM.wfsm_state_machine
    system.WFSM.wfsm_state_machine.SM.sm_initial_state
    trace
    log.dl_state /\
  Seq.equal received
    (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal sent
    (WF.serialize_all system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.dl_received /\
  Seq.equal sent log.dl_sent

noextract
let dh_trace_ok
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (received sent:TCP.bytes)
  (log:dh_log)
  : prop =
  exists trace. dh_trace_witness system received sent log trace

(**
  `dh_trace_ok` refines the byte histories into a valid state-machine trace via
  the DATAGRAM (serialize-equality) disjunct of `WFSM.valid_byte_trace` with
  residual `Seq.empty` — the forward direction, which holds by construction.
*)
let lemma_dh_trace_ok_valid
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (received sent:TCP.bytes)
  (log:dh_log)
  : Lemma
      (requires dh_trace_ok system received sent log)
      (ensures
        WFSM.valid_byte_trace system received log.dl_state sent Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost dh_trace (dh_trace_witness system received sent log) in
  Seq.append_empty_r
    (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace));
  assert (Seq.equal received
    (Seq.append
      (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace))
      Seq.empty));
  assert (exists trace'.
    SM.trace_reaches
      system.WFSM.wfsm_state_machine
      system.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.dl_state /\
    (WF.parses_as
       system.WFSM.wfsm_wire_format received (WFSM.trace_input_messages trace') Seq.empty
     \/
     Seq.equal received
       (Seq.append
         (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace'))
         Seq.empty)) /\
    Seq.equal sent
      (WF.serialize_all system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace')))

(** The initial state is reached by the empty trace; both histories are empty. *)
let lemma_dh_initial_trace_ok
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  : Lemma
      (dh_trace_ok system Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty system.WFSM.wfsm_state_machine.SM.sm_initial_state))
=
  let trace : dh_trace = [] in
  Seq.lemma_eq_elim Seq.empty
    (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim Seq.empty
    (WF.serialize_all system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace));
  assert (dh_trace_witness system Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty system.WFSM.wfsm_state_machine.SM.sm_initial_state) trace)

(**
  Extend the canonical trace by one transition: the histories grow by the
  serialized input messages of `ev` and the serialized wire outputs of the step.
  Uses only `system.wfsm_state_machine.sm_step` (so it is instantiated with the
  concrete `initiator_step` / `responder_step` in the Pulse shell).
*)
let lemma_dh_trace_ok_step
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (received0 sent0:TCP.bytes)
  (st0:endpoint_state)
  (ev:dh_event)
  (st1:endpoint_state)
  (out:dh_output)
  : Lemma
      (requires
        dh_trace_ok system received0 sent0 (mk_log received0 sent0 st0) /\
        system.WFSM.wfsm_state_machine.SM.sm_step st0 ev st1 out)
      (ensures (
        let received1 =
          Seq.append received0
            (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.event_input_messages ev)) in
        let sent1 =
          Seq.append sent0
            (WF.serialize_all system.WFSM.wfsm_wire_format out.SM.so_wire_outputs) in
        dh_trace_ok system received1 sent1 (mk_log received1 sent1 st1)))
=
  let log0 = mk_log received0 sent0 st0 in
  let trace0 =
    ID.indefinite_description_ghost dh_trace (dh_trace_witness system received0 sent0 log0) in
  let tr : SM.transition endpoint_state dh_message local_event local_output =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches system.WFSM.wfsm_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    system.WFSM.wfsm_state_machine
    system.WFSM.wfsm_state_machine.SM.sm_initial_state st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  lemma_trace_input_messages_append trace0 [tr];
  lemma_serialize_all_append system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim received0
    (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace0));
  L.append_l_nil (WFSM.event_input_messages ev);
  lemma_trace_wire_outputs_append trace0 [tr];
  lemma_serialize_all_append system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs;
  Seq.lemma_eq_elim sent0
    (WF.serialize_all system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace0));
  L.append_l_nil out.SM.so_wire_outputs;
  let received1 =
    Seq.append received0
      (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.event_input_messages ev)) in
  let sent1 =
    Seq.append sent0
      (WF.serialize_all system.WFSM.wfsm_wire_format out.SM.so_wire_outputs) in
  assert (Seq.equal received1
    (WF.serialize_all system.WFSM.wfsm_wire_format (WFSM.trace_input_messages trace1)));
  assert (Seq.equal sent1
    (WF.serialize_all system.WFSM.wfsm_wire_format (SM.trace_wire_outputs trace1)));
  assert (dh_trace_witness system received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   Section 8.  Next-state constructors and step witnesses

   For each of the four enabled spec transitions we (a) name the successor state
   the implementation installs, and (b) prove the corresponding `initiator_step`
   / `responder_step` clause holds for that successor and the emitted outputs.
   These are the sole bridges from the imperative endpoint to the pure relations.
   ─────────────────────────────────────────────────────────────────────────── *)

(** Successor after the initiator's `StartInitiator x` from `Init_Start`. *)
noextract
let init_start_next (st0:endpoint_state) (x:dh_scalar) : endpoint_state =
  { st0 with ep_phase = Init_Wait2; ep_scalar = Some x; ep_my_share = Some (dh_exp x) }

(** Successor after the initiator verifies `Msg2` from `Init_Wait2`. *)
noextract
let init_msg2_next (st0:endpoint_state) (gy:dh_share) (key:shared_secret) : endpoint_state =
  { st0 with ep_phase = Init_Done; ep_peer_share = Some gy; ep_key = Some key }

(** Successor after the responder consumes `Msg1 a gx` with fresh scalar `y`. *)
noextract
let resp_msg1_next (st0:endpoint_state) (a:principal) (gx:dh_share) (y:dh_scalar) : endpoint_state =
  { st0 with ep_phase = Resp_Wait3; ep_peer = Some a; ep_scalar = Some y;
             ep_my_share = Some (dh_exp y); ep_peer_share = Some gx;
             ep_key = Some (dh_agree y gx) }

(** Successor after the responder verifies `Msg3` from `Resp_Wait3`. *)
noextract
let resp_msg3_next (st0:endpoint_state) : endpoint_state =
  { st0 with ep_phase = Resp_Done }

(** The initiator's start transition holds for `init_start_next`. *)
let lemma_init_start_step (st0:endpoint_state) (x:dh_scalar)
  : Lemma
      (requires st0.ep_role == Initiator /\ st0.ep_phase == Init_Start /\ Some? st0.ep_peer)
      (ensures
        initiator_step st0 (SM.LocalEvent (StartInitiator x))
          (init_start_next st0 x)
          ({ SM.so_wire_outputs = [ Msg1 st0.ep_me (dh_exp x) ]; SM.so_local_outputs = [] }))
= ()

(** The initiator's `Msg2` transition holds for `init_msg2_next`. *)
let lemma_init_msg2_step (st0:endpoint_state) (b:principal) (gy:dh_share) (sigB:signature)
  : Lemma
      (requires
        st0.ep_role == Initiator /\ st0.ep_phase == Init_Wait2 /\
        st0.ep_peer == Some b /\ Some? st0.ep_scalar /\ Some? st0.ep_my_share /\
        verify b (transcript st0.ep_me (Some?.v st0.ep_my_share) gy) sigB)
      (ensures (
        let x  = Some?.v st0.ep_scalar in
        let gx = Some?.v st0.ep_my_share in
        let key = dh_agree x gy in
        let sigA = sign st0.ep_me (transcript b gx gy) in
        initiator_step st0 (SM.WireEvent (Msg2 b gy sigB))
          (init_msg2_next st0 gy key)
          ({ SM.so_wire_outputs = [ Msg3 sigA ];
             SM.so_local_outputs = [ SessionEstablished b key ] })))
= ()

(** The responder's `Msg1` transition holds for `resp_msg1_next` and any `y`. *)
let lemma_resp_msg1_step (st0:endpoint_state) (a:principal) (gx:dh_share) (y:dh_scalar)
  : Lemma
      (requires st0.ep_role == Responder /\ st0.ep_phase == Resp_Start)
      (ensures (
        let gy = dh_exp y in
        let key = dh_agree y gx in
        let sigB = sign st0.ep_me (transcript a gx gy) in
        responder_step st0 (SM.WireEvent (Msg1 a gx))
          (resp_msg1_next st0 a gx y)
          ({ SM.so_wire_outputs = [ Msg2 st0.ep_me gy sigB ]; SM.so_local_outputs = [] })))
= ()

(** The responder's `Msg3` transition holds for `resp_msg3_next`. *)
let lemma_resp_msg3_step (st0:endpoint_state) (sigA:signature)
  : Lemma
      (requires
        st0.ep_role == Responder /\ st0.ep_phase == Resp_Wait3 /\
        Some? st0.ep_peer /\ Some? st0.ep_my_share /\ Some? st0.ep_peer_share /\ Some? st0.ep_key /\
        verify (Some?.v st0.ep_peer)
               (transcript st0.ep_me (Some?.v st0.ep_peer_share) (Some?.v st0.ep_my_share)) sigA)
      (ensures (
        let a = Some?.v st0.ep_peer in
        let key = Some?.v st0.ep_key in
        responder_step st0 (SM.WireEvent (Msg3 sigA))
          (resp_msg3_next st0)
          ({ SM.so_wire_outputs = []; SM.so_local_outputs = [ SessionEstablished a key ] })))
= ()

(** Bridge a role-specific spec step into the combined `dh_step` (for the preorder). *)
let lemma_dh_step_of_initiator
  (st0:endpoint_state) (ev:dh_event) (st1:endpoint_state) (out:dh_output)
  : Lemma (requires st0.ep_role == Initiator /\ initiator_step st0 ev st1 out)
          (ensures dh_step st0 ev st1 out)
= ()

let lemma_dh_step_of_responder
  (st0:endpoint_state) (ev:dh_event) (st1:endpoint_state) (out:dh_output)
  : Lemma (requires st0.ep_role == Responder /\ responder_step st0 ev st1 out)
          (ensures dh_step st0 ev st1 out)
= ()

(* ───────────────────────────────────────────────────────────────────────────
   Section 9.  Parse-connection lemmas

   A raw datagram of the exact length with the right tag byte and whose fixed
   fields equal the given values parses to precisely that message with an empty
   residual — i.e. the buffer IS the serialization of one message.  Follows by
   reduction of `DH.Sample.Wire.parse`.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_parse_msg1 (input:TCP.bytes) (a gx:dh_share)
  : Lemma
      (requires
        Seq.length input == 9 /\ U8.v (Seq.index input 0) == 1 /\
        Seq.equal a (Seq.slice input 1 5) /\ Seq.equal gx (Seq.slice input 5 9))
      (ensures
        input == serialize (Msg1 a gx) /\
        parse input == Some (Msg1 a gx, Seq.empty))
=
  Seq.lemma_eq_elim a (Seq.slice input 1 5);
  Seq.lemma_eq_elim gx (Seq.slice input 5 9);
  Seq.lemma_eq_intro input (serialize (Msg1 a gx));
  lemma_parse_serialize_prefix (Msg1 a gx) Seq.empty;
  Seq.append_empty_r (serialize (Msg1 a gx))

let lemma_parse_msg2 (input:TCP.bytes) (b:principal) (gy:dh_share) (sigB:signature)
  : Lemma
      (requires
        Seq.length input == 17 /\ U8.v (Seq.index input 0) == 2 /\
        Seq.equal b (Seq.slice input 1 5) /\ Seq.equal gy (Seq.slice input 5 9) /\
        Seq.equal sigB (Seq.slice input 9 17))
      (ensures
        input == serialize (Msg2 b gy sigB) /\
        parse input == Some (Msg2 b gy sigB, Seq.empty))
=
  Seq.lemma_eq_elim b (Seq.slice input 1 5);
  Seq.lemma_eq_elim gy (Seq.slice input 5 9);
  Seq.lemma_eq_elim sigB (Seq.slice input 9 17);
  Seq.lemma_eq_intro input (serialize (Msg2 b gy sigB));
  lemma_parse_serialize_prefix (Msg2 b gy sigB) Seq.empty;
  Seq.append_empty_r (serialize (Msg2 b gy sigB))

let lemma_parse_msg3 (input:TCP.bytes) (sigA:signature)
  : Lemma
      (requires
        Seq.length input == 9 /\ U8.v (Seq.index input 0) == 3 /\
        Seq.equal sigA (Seq.slice input 1 9))
      (ensures
        input == serialize (Msg3 sigA) /\
        parse input == Some (Msg3 sigA, Seq.empty))
=
  Seq.lemma_eq_elim sigA (Seq.slice input 1 9);
  Seq.lemma_eq_intro input (serialize (Msg3 sigA));
  lemma_parse_serialize_prefix (Msg3 sigA) Seq.empty;
  Seq.append_empty_r (serialize (Msg3 sigA))

(* ── Decidable byte-string equality on fixed-size blobs ──────────────────────
   Reflected to `Seq.equal`, so a `true` result lets the caller upgrade to `==`
   (via `Seq.lemma_eq_elim`) and hence establish the spec's `verify` predicate
   (which is `sig == sign …`) or a principal-identity match. *)

let eq4 (s1 s2:lbytes 4) : b:bool{b <==> Seq.equal s1 s2} =
  Seq.index s1 0 = Seq.index s2 0 && Seq.index s1 1 = Seq.index s2 1 &&
  Seq.index s1 2 = Seq.index s2 2 && Seq.index s1 3 = Seq.index s2 3

let eq8 (s1 s2:lbytes 8) : b:bool{b <==> Seq.equal s1 s2} =
  Seq.index s1 0 = Seq.index s2 0 && Seq.index s1 1 = Seq.index s2 1 &&
  Seq.index s1 2 = Seq.index s2 2 && Seq.index s1 3 = Seq.index s2 3 &&
  Seq.index s1 4 = Seq.index s2 4 && Seq.index s1 5 = Seq.index s2 5 &&
  Seq.index s1 6 = Seq.index s2 6 && Seq.index s1 7 = Seq.index s2 7

(* ───────────────────────────────────────────────────────────────────────────
   Section 10.  Output-byte helpers
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_output_written_empty (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz Seq.empty)
=
  assert (Seq.equal (CPI.output_prefix o 0sz) Seq.empty)

(** From "the first `produced_len` bytes of `o` equal `produced`" conclude the
    CPI `output_written` predicate. *)
let lemma_output_written_prefix (o produced:TCP.bytes) (produced_len:SZ.t)
  : Lemma
      (requires
        SZ.v produced_len == Seq.length produced /\
        SZ.v produced_len <= Seq.length o /\
        Seq.equal (Seq.slice o 0 (SZ.v produced_len)) produced)
      (ensures CPI.output_written o produced_len produced)
=
  assert (CPI.bounded_len o produced_len == SZ.v produced_len);
  Seq.lemma_eq_elim (CPI.output_prefix o produced_len) produced

(** `serialize_all` of one message equals its serialization (for any system's fmt). *)
let lemma_serialize_all_singleton_gen
  (f:WF.wire_format dh_message) (m:dh_message)
  : Lemma (Seq.equal (WF.serialize_all f [m]) (f.WF.wf_serialize m))
=
  Seq.append_empty_r (f.WF.wf_serialize m)

(* ───────────────────────────────────────────────────────────────────────────
   Section 11.  Result values and process-correctness packaging

   The Pulse handlers only choose a `process_result` and call one of these four
   lemmas to discharge the `network_process_correct` / `local_process_correct`
   postcondition of the CPI class.
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let dh_result (status:CPI.process_status) (consumed_len produced_len:SZ.t) : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

(**
  A genuine network `StepOk`: the (whole) input datagram parses to `msg`
  (residual empty), the spec makes exactly the step
  `WireEvent msg -> (wire_outputs, local_outputs)`, and `produced` (the
  serialization of the wire outputs) was written to the output buffer.  The byte
  histories grow by the consumed datagram and the produced bytes respectively.
*)
let lemma_network_stepok
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:endpoint_state)
  (msg:dh_message) (consumed:TCP.bytes) (st1:endpoint_state)
  (consumed_len produced_len:SZ.t)
  (wire_outputs:list dh_message) (local_outputs:list local_output) (produced:TCP.bytes)
  (received1 sent1:TCP.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        CPI.consumed_by_parse system.WFSM.wfsm_wire_format
          (CPI.input_bytes input input_len) msg consumed Seq.empty /\
        SZ.v consumed_len == Seq.length consumed /\
        system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1
          (CPI.step_output wire_outputs local_outputs) /\
        Seq.equal produced (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced))
      (ensures
        CPI.network_process_correct system input input_len old_out out_bytes out_len
          received0 sent0 st0
          (dh_result CPI.StepOk consumed_len produced_len)
          received1 sent1 st1
          consumed wire_outputs local_outputs)
=
  introduce exists (msg':dh_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse system.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' consumed residual /\
    SZ.v (dh_result CPI.StepOk consumed_len produced_len).CPI.process_consumed_len == Seq.length consumed /\
    system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.WireEvent msg') st1
      (CPI.step_output wire_outputs local_outputs) /\
    Seq.equal produced' (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written out_bytes
      (dh_result CPI.StepOk consumed_len produced_len).CPI.process_produced_len produced' /\
    Seq.equal received1 (Seq.append received0 consumed) /\
    Seq.equal sent1 (Seq.append sent0 produced')
  with msg Seq.empty produced
  and ()

(** A genuine local `StepOk` (the initiator's `StartInitiator`): received is
    unchanged, sent grows by `produced`, and consumed length is zero. *)
let lemma_local_stepok
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (ev:local_event) (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:endpoint_state) (produced_len:SZ.t)
  (st1:endpoint_state) (wire_outputs:list dh_message) (local_outputs:list local_output)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\ Seq.length out_bytes == Seq.length old_out /\
        system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.LocalEvent ev) st1
          (CPI.step_output wire_outputs local_outputs) /\
        Seq.equal produced (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct system ev old_out out_bytes out_len
          received0 sent0 st0
          (dh_result CPI.StepOk 0sz produced_len)
          received0 (Seq.append sent0 produced) st1 wire_outputs local_outputs)
= ()

(** A sound network no-op (`IllegalTransition`): the abstract state and both byte
    histories are preserved (the "no progress" disjunct). *)
let lemma_network_noop
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (input:TCP.bytes) (input_len:SZ.t) (old_out:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:endpoint_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct system input input_len old_out old_out out_len
          received0 sent0 st0
          (dh_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0 Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine system
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])

(** A sound local no-op (`IllegalTransition`): received/sent/state preserved. *)
let lemma_local_illegal
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (ev:local_event) (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:endpoint_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\ Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct system ev old_out out_bytes out_len
          received0 sent0 st0
          (dh_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0 [] [])
=
  lemma_output_written_empty out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine system st0 st0 [] [])

(* ───────────────────────────────────────────────────────────────────────────
   Section 12.  Pulse-facing packaging helpers

   The Pulse endpoint threads its byte histories in the canonical
   `serialize_all` form; these three lemmas let it (a) advance the reachable
   trace AND the monotone preorder in one shot, (b) recognise an exact-length
   input buffer as its own parse window, and (c) discharge `output_written` for
   a freshly serialized message.
   ─────────────────────────────────────────────────────────────────────────── *)

(** Advance both the canonical trace (`dh_trace_ok`) and the monotone step
    relation (`dh_step_rel`) by a single spec transition. *)
let lemma_dh_advance
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (received0 sent0:TCP.bytes)
  (st0:endpoint_state)
  (ev:dh_event)
  (st1:endpoint_state)
  (out:dh_output)
  : Lemma
      (requires
        system.WFSM.wfsm_wire_format == fmt /\
        dh_trace_ok system received0 sent0 (mk_log received0 sent0 st0) /\
        system.WFSM.wfsm_state_machine.SM.sm_step st0 ev st1 out /\
        dh_step st0 ev st1 out)
      (ensures (
        let received1 = Seq.append received0 (WF.serialize_all fmt (WFSM.event_input_messages ev)) in
        let sent1 = Seq.append sent0 (WF.serialize_all fmt out.SM.so_wire_outputs) in
        dh_trace_ok system received1 sent1 (mk_log received1 sent1 st1) /\
        dh_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)))
=
  let received1 = Seq.append received0 (WF.serialize_all fmt (WFSM.event_input_messages ev)) in
  let sent1 = Seq.append sent0 (WF.serialize_all fmt out.SM.so_wire_outputs) in
  lemma_dh_trace_ok_step system received0 sent0 st0 ev st1 out;
  lemma_dh_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent1 st1) ev out

(** An input buffer of its exact length is its own parse window. *)
let lemma_input_bytes_all (input:TCP.bytes) (input_len:SZ.t)
  : Lemma
      (requires SZ.v input_len == Seq.length input)
      (ensures CPI.input_bytes input input_len == input)
=
  Seq.lemma_eq_intro (CPI.input_bytes input input_len) input

(** Consuming an exactly-`msg`-shaped buffer with empty residual. *)
let lemma_consumed_msg
  (system:WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output)
  (input:TCP.bytes) (input_len:SZ.t) (msg:dh_message)
  : Lemma
      (requires
        system.WFSM.wfsm_wire_format == fmt /\
        SZ.v input_len == Seq.length input /\
        parse input == Some (msg, Seq.empty))
      (ensures
        CPI.consumed_by_parse system.WFSM.wfsm_wire_format
          (CPI.input_bytes input input_len) msg input Seq.empty)
=
  lemma_input_bytes_all input input_len;
  Seq.append_empty_r input

(** `output_written` for a freshly serialized single message written to the
    output buffer's prefix. *)
let lemma_output_written_msg (o:TCP.bytes) (msg:dh_message) (produced_len:SZ.t)
  : Lemma
      (requires
        SZ.v produced_len == msg_len msg /\
        msg_len msg <= Seq.length o /\
        Seq.equal (Seq.slice o 0 (SZ.v produced_len)) (serialize msg))
      (ensures
        Seq.equal (WF.serialize_all fmt [msg]) (serialize msg) /\
        Seq.length (WF.serialize_all fmt [msg]) == msg_len msg /\
        CPI.output_written o produced_len (WF.serialize_all fmt [msg]))
=
  lemma_serialize_len msg;
  lemma_dh_serialize_all_singleton msg;
  lemma_output_written_prefix o (WF.serialize_all fmt [msg]) produced_len
