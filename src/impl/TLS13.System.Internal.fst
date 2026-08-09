module TLS13.System.Internal

(**
  Internal (drain) steps at the level of the combined client<->server system.

  Phases 2--5 gave the TLS client one receive path: a protected record is
  delivered once, and the handshake messages it carries are drained one at a
  time by *internal* steps.  Decision S1 made those steps ordinary local
  events, which is what this module cashes in at the system level.

  Three things are proved here.

  1. **No new move families.**  A drain step of the client endpoint is exactly
     an `MP.mp_client_local` move of the existing product, hence a
     `tls_sys_step`.  `Common.MachineProduct` and `Common.SystemProduct` are
     untouched: the quiet-gated local family that was already there is the one
     internal steps travel on.

  2. **Draining is a system run.**  A whole drain chain lifts to
     `T.reachable tls_sys_step`, and `combined_inv` -- hence `tls_system_inv`
     on non-rekeyed states -- survives it.  So the intermediate states in which
     a delivered record is only partly consumed are ordinary reachable states,
     not a hole in the invariant.

  3. **The settled payoff.**  `tls_settled` strengthens `tls_quiescent` with
     "no internal work pending", and the flagship record-key-material
     agreement theorem is re-established at settled states.  A drain that runs
     to quiescence reaches such a state, so the strengthening costs nothing:
     `TLS13.Impl.Client.DrainLoop.drain_pending` is the implementation that
     produces the witness.
 **)

module B    = TLS13.Bytes
module CP   = TLS13.Impl.Client.CanonicalProtocol
module CPI  = Common.ProtocolImplementation
module CS   = TLS13.Spec.StateMachine
module CTy  = TLS13.Impl.CanonicalTypes
module CW   = TLS13.Spec.Endpoint.Wire
module D    = TLS13.Impl.Client.Drain
module DP   = TLS13.Impl.Client.DrainProgress
module EAPI = TLS13.Spec.Endpoint.API
module EC   = TLS13.Spec.Endpoint.Client
module ID   = FStar.IndefiniteDescription
module MP   = Common.MachineProduct
module RTC  = FStar.ReflexiveTransitiveClosure
module SM   = Common.StateMachine
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module T    = Common.Temporal
module TT   = TLS13.System.Temporal
module WFL  = TLS13.Spec.WireFormatLemmas

open TLS13.System

(** ─────────────────────────────────────────────────────────────────────────
    Pending internal work, and the settled state.
    ───────────────────────────────────────────────────────────────────────── **)

(**
  The client still holds unprocessed plaintext in its pending
  protected-handshake buffer.  Only the client has internal work: the server
  never receives a coalescing protected record in this system.
 **)
let tls_internal_pending (s:tls_system_state) : prop =
  CP.client_internal_pending s.client

(**
  Settled = nothing in flight *and* nothing pending internally.

  `tls_quiescent` alone is the channel condition; it is satisfied the instant a
  record is delivered, while the receiver may still owe several internal steps.
  `tls_settled` is the condition under which the endpoint has actually finished
  reacting, and it is the honest antecedent for an agreement statement.
 **)
let tls_settled (s:tls_system_state) : prop =
  tls_quiescent s /\ ~(tls_internal_pending s)

let lemma_settled_quiescent (s:tls_system_state)
  : Lemma (requires tls_settled s) (ensures tls_quiescent s)
= ()

(**
  The bridge from the running client to the settled predicate.

  `TLS13.Impl.Client.Engine.poll` reports `EngineReady` only after the internal
  primitive has answered `None`, and its contract therefore carries
  `~(D.internal_pending st1)`.  With an empty channel that is exactly
  `tls_settled`, so the C API's Ready signal is the antecedent of the flagship
  theorem rather than a weaker heuristic.
 **)
let lemma_settled_of_client_quiescent (s:tls_system_state)
  : Lemma
      (requires tls_quiescent s /\ ~(D.internal_pending s.client))
      (ensures tls_settled s)
= DP.lemma_internal_pending_agrees s.client

(**
  Readiness is settledness.

  This is the statement §8 of INTERNAL_EVENT_PLAN.md left open, and it is worth
  recording why it needs `client_driver_application_ready` to carry
  `protected_handshake_buffer_empty` rather than being derivable without it.

  This needed a fix to the state machine, not just to the predicate.

  `legal_protected_handshake_step` deliberately does not require a record's
  plaintext to be consumed to the end -- that permissiveness is what let the
  receive-path fork be removed -- so a head step may take delivery of a record
  and leave a remainder.  The client then reaches `ControlApplicationData` by
  *sending* its own Finished, and that transition used to carry no precondition
  on the pending buffer.  The resulting state was not merely inconvenient for
  this proof, it was WEDGED: `legal_handshake_message` admits no message at all
  in `ControlApplicationData`, so the leftover plaintext could never be drained
  and `tls_internal_pending` held forever.  A server that appended trailing
  bytes after its Finished in the same record could park the client there
  permanently.

  So `legal_handshake_message` now requires `protected_handshake_buffer_empty`
  on the client's `Sent Finished` transition, and
  `can_send_client_finished_runtime` checks it, which is what discharges the
  obligation in `TLS13.Impl.ConnectionState.LocalSend.try_send_client_finished`.
  The wedged state is unreachable by construction.

  `client_driver_application_ready` keeps the buffer conjunct as well.  That is
  not redundancy: it is the honest reading of "has finished reacting" rather
  than "has arrived at the right control state", and it is the conjunct this
  lemma actually consumes.  Given it, readiness plus an empty channel is
  settledness, with no proof obligation left over.
 **)
let lemma_application_ready_settled (s:tls_system_state)
  : Lemma
      (requires tls_quiescent s /\ tls_application_ready s)
      (ensures tls_settled s)
= ()

(** ─────────────────────────────────────────────────────────────────────────
    (1) A drain step is a client-local move -- no new move family.
    ───────────────────────────────────────────────────────────────────────── **)

(** The step output of an internal step: nothing on the wire, nothing to the
    application.  A drain is invisible to both. **)
let internal_step_output : SM.step_output CW.wire_message EAPI.local_output =
  CPI.step_output ([] <: list CW.wire_message) ([] <: list EAPI.local_output)

let lemma_internal_step_output_silent ()
  : Lemma (internal_step_output.SM.so_wire_outputs == [])
= ()

(**
  A drain step of the client endpoint, with the channel quiet, is precisely a
  `tls_step_client_local` move.

  This is the "no new move families" claim of the phase, discharged rather than
  asserted.  `MP.mp_client_local` asks for a `LocalEvent` step emitting no wire
  output; `CP.lemma_internal_step_is_client_step` supplies exactly that at
  `CP.client_internal_event`.
 **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_drain_step_is_client_local (a b:tls_system_state)
  : Lemma
      (requires
        D.drain_step a.client b.client /\
        b == ({ a with client = b.client } <: tls_system_state))
      (ensures tls_step_client_local a b)
=
  let w = D.drain_step_witness a.client b.client in
  CP.lemma_internal_step_is_client_step a.client b.client (fst w) (snd w);
  MP.lemma_mp_client_local_intro
    tls_machine_iface a b
    CP.client_internal_event b.client internal_step_output
#pop-options

(** ...and therefore a system step, once the channel is quiet.  The quiet gate
    is `Common.SystemProduct`'s, not ours: a local move is enabled only with an
    empty channel, which is exactly the schedule of design-doc §5. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_drain_step_is_sys_step (a b:tls_system_state)
  : Lemma
      (requires
        tls_quiescent a /\
        D.drain_step a.client b.client /\
        b == ({ a with client = b.client } <: tls_system_state))
      (ensures tls_sys_step a b)
=
  lemma_drain_step_is_client_local a b
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    (2) A drain chain is a system run.
    ───────────────────────────────────────────────────────────────────────── **)

(** A drain never touches the channel or the server, so every intermediate
    state of a chain is again quiescent -- which is what keeps the *next* local
    move enabled.  Draining therefore does not have to interleave with the
    channel discipline; it runs to completion under one quiet window. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_drain_chain_reachable
  (n:nat) (a:tls_system_state) (c':CS.connection_state)
  : Lemma
      (requires tls_quiescent a /\ D.drain_chain n a.client c')
      (ensures
        T.reachable tls_sys_step a ({ a with client = c' } <: tls_system_state))
      (decreases n)
=
  if n = 0
  then assert (({ a with client = c' } <: tls_system_state) == a)
  else
  let m : nat = n - 1 in
    eliminate
      (c' == a.client) \/
      (exists st'. D.drain_step a.client st' /\ D.drain_chain m st' c')
    with assert (({ a with client = c' } <: tls_system_state) == a)
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> D.drain_step a.client st' /\ D.drain_chain m st' c') in
       let a' : tls_system_state = { a with client = st' } in
       lemma_drain_step_is_sys_step a a';
       RTC.closure_step tls_sys_step a a';
       lemma_drain_chain_reachable m a' c';
       assert (({ a' with client = c' } <: tls_system_state) ==
               ({ a with client = c' } <: tls_system_state));
       // `RTC.closure` is a preorder by construction, so reachability composes.
       assert (FStar.Preorder.transitive (RTC.closure tls_sys_step)))
#pop-options

(** The unbounded form: a completed drain is a run of the system. **)
let lemma_drained_reachable (a:tls_system_state) (c':CS.connection_state)
  : Lemma
      (requires tls_quiescent a /\ D.drained a.client c')
      (ensures
        T.reachable tls_sys_step a ({ a with client = c' } <: tls_system_state))
=
  let n = ID.indefinite_description_ghost nat (fun n -> D.drain_chain n a.client c') in
  lemma_drain_chain_reachable n a c'

(** ─────────────────────────────────────────────────────────────────────────
    Invariant preservation across a drain.
    ───────────────────────────────────────────────────────────────────────── **)

(** `combined_inv` is inductive for `tls_sys_step` (`TLS13.System`), so it is
    stable along any reachable pair -- in particular along a drain.  Stating it
    this way avoids an inductive re-proof: the drain contributes nothing new,
    which is the point of it being an ordinary local move. **)
let lemma_reachable_combined_inv (a b:tls_system_state)
  : Lemma
      (requires combined_inv a /\ T.reachable tls_sys_step a b)
      (ensures combined_inv b)
=
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_combined_inv_preserved);
  RTC.stable_on_closure tls_sys_step combined_inv ()

(**
  The invariant survives a drain.

  A delivered protected record leaves the client mid-consumption; this says the
  intermediate states are not a gap in the invariant.  The `tls_no_rekeying`
  hypothesis on the *target* is the same one `lemma_inv_preserved` takes, and
  is recovered backwards by `lemma_no_key_update_backward`.
 **)
let lemma_drained_inv (a:tls_system_state) (c':CS.connection_state)
  : Lemma
      (requires
        tls_system_inv a /\ tls_quiescent a /\ D.drained a.client c' /\
        tls_no_rekeying ({ a with client = c' } <: tls_system_state))
      (ensures tls_system_inv ({ a with client = c' } <: tls_system_state))
=
  lemma_drained_reachable a c';
  lemma_reachable_combined_inv a ({ a with client = c' } <: tls_system_state)

(** A drain leaves the channel quiet: it is a client-only move. **)
let lemma_drained_quiescent (a:tls_system_state) (c':CS.connection_state)
  : Lemma
      (requires tls_quiescent a)
      (ensures tls_quiescent ({ a with client = c' } <: tls_system_state))
= ()

(**
  A drain run to quiescence reaches a *settled* state.

  `D.internal_pending` and `CP.client_internal_pending` are the same inequality
  (`DP.lemma_internal_pending_agrees`), and
  `TLS13.Impl.Client.DrainLoop.drain_pending` returns `quiet` exactly when it
  has established the former.  So the implementation's drain loop produces the
  system-level settled witness this module's payoff consumes.
 **)
let lemma_drain_to_settled (a:tls_system_state) (c':CS.connection_state)
  : Lemma
      (requires
        tls_quiescent a /\ D.drained a.client c' /\ ~(D.internal_pending c'))
      (ensures
        T.reachable tls_sys_step a ({ a with client = c' } <: tls_system_state) /\
        tls_settled ({ a with client = c' } <: tls_system_state))
=
  lemma_drained_reachable a c';
  DP.lemma_internal_pending_agrees c'

(** ─────────────────────────────────────────────────────────────────────────
    (3) The settled payoff.
    ───────────────────────────────────────────────────────────────────────── **)

(** The flagship state-predicate, at the settled boundary. **)
let record_material_agrees_when_settled : T.sprop tls_system_state = fun s ->
  (tls_no_rekeying s /\ tls_settled s /\ tls_application_ready s) ==>
    (SMKM.peer_record_material_agrees
       (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) s.client s.server /\
     SMKM.peer_record_material_agrees
       (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) s.client s.server)

(**
  Flagship, restated at settled states: on every run, whenever the system has
  not rekeyed, is settled (channel quiet AND no pending internal work) and the
  handshake has completed on both endpoints, the application record-key
  material agrees in both directions.

  This is the phase's exit criterion.  The added `~(tls_internal_pending s)`
  clause is what makes the statement meaningful once a record can be consumed
  over several steps: without it, "quiescent" would be satisfiable at a state
  where the client has not yet processed the Finished it has already received.
 **)
val lemma_flagship_settled_record_material_agreement
  (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c)
      (ensures
        T.ag tls_sys_step
          record_material_agrees_when_settled
          (initial_tls_system cfg_c cfg_s))
let lemma_flagship_settled_record_material_agreement cfg_c cfg_s =
  let s0 = initial_tls_system cfg_c cfg_s in
  introduce
    forall (s':tls_system_state).
      T.reachable tls_sys_step s0 s' ==> record_material_agrees_when_settled s'
  with begin
    introduce
      T.reachable tls_sys_step s0 s' ==> record_material_agrees_when_settled s'
    with begin
      introduce
        (tls_no_rekeying s' /\ tls_settled s' /\ tls_application_ready s') ==>
          (SMKM.peer_record_material_agrees
             (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) s'.client s'.server /\
           SMKM.peer_record_material_agrees
             (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) s'.client s'.server)
      with begin
        lemma_reachable_inv cfg_c cfg_s s';
        TT.lemma_inv_implies_agreement s'
      end
    end
  end;
  T.lemma_ag_of_invariant tls_sys_step record_material_agrees_when_settled s0
