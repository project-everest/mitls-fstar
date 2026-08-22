module TLS13.System.Temporal

(**
  Temporal-logic theorems about the combined TLS 1.3 client<->server system.

  Using the generic path-based operators of `Common.Temporal` over the
  transition system of `TLS13.System`, we prove the flagship record-key-material
  agreement theorem in the clean LTL / `system_state` style — the scaled-up
  analogue of the calculator `Calc.System.Temporal` flagship:

    AG ( (quiescent /\ application_ready)
         ==>   peer_record_material_agrees (Application, ClientTraffic) client server
            /\ peer_record_material_agrees (Application, ServerTraffic) client server )

  "on every run of the system, whenever the handshake has completed on both
  endpoints and no message is in flight, the two endpoints agree on the
  application record-key material in both directions".

  The naive unconditional `AG (record material agrees)` is false: before the
  handshake completes there is no application material at all, and mid-delivery
  the two endpoints lag. The side conditions (`application_ready` = handshake
  complete + application keys installed on both sides; and "no rekeying", which
  is discharged *by the invariant* since the honest step relation never performs
  a key update) are exactly the clean structural hypotheses — no hardcoded packet
  counts, no trace splitting, unlike the retired `PairingSemanticTrace`.
**)

module T   = Common.Temporal
module R   = FStar.ReflexiveTransitiveClosure
module CS  = TLS13.Spec.StateMachine
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module CD  = TLS13.Impl.Client.Driver
module SD  = TLS13.Impl.Server.Driver
module WFL = TLS13.Spec.WireFormatLemmas
module MP  = Common.MachineProduct
module CCShape = TLS13.ConnectionState.ClientCanonicalShape
module SCShape = TLS13.ConnectionState.ServerCanonicalShape

open TLS13.System

(** ─────────────────────────────────────────────────────────────────────────
    Flagship: AG ( quiescent /\ application_ready ==> record material agrees )
    ───────────────────────────────────────────────────────────────────────── **)

(** The flagship state-predicate (scoped): at any *non-rekeyed*, quiescent,
    handshake-complete state the application record-key material agrees in both
    traffic directions.  The no-rekeying side condition is now part of the
    antecedent (rather than pinned inside the step relation) — the honest run
    never rekeys, so it still fires along every real run. **)
let record_material_agrees_when_ready_scoped : T.sprop tls_system_state = fun s ->
  (tls_no_rekeying s /\ tls_quiescent s /\ tls_application_ready s /\
   CCShape.no_buffering_steps s.client.CS.cs_event_log) ==>
    (SMKM.peer_record_material_agrees
       (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) s.client s.server /\
     SMKM.peer_record_material_agrees
       (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) s.client s.server)

(** The structural invariant entails the scoped flagship state-predicate: at a
    quiescent + ready state the invariant supplies handshake-message pairing and
    the no-rekeying discipline, and the existing verified pairing payoff concludes
    record-material agreement (which is definitionally the two conjuncts). **)
val lemma_inv_implies_agreement (s:tls_system_state)
  : Lemma (requires tls_system_inv s)
          (ensures record_material_agrees_when_ready_scoped s)
let lemma_inv_implies_agreement s =
  introduce
    (tls_no_rekeying s /\ tls_quiescent s /\ tls_application_ready s /\
     CCShape.no_buffering_steps s.client.CS.cs_event_log) ==>
      (SMKM.peer_record_material_agrees
         (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) s.client s.server /\
       SMKM.peer_record_material_agrees
         (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) s.client s.server)
  with begin
    (* The server-side gate on [lemma_ready_quiescent_agrees] is a conjunct of
       [tls_system_inv] (the paired system steps by
       [ES.server_step_nonbuffering]); reachability alone no longer excludes
       buffering, since [WStep.server_sm] is built over the general step. *)
    lemma_ready_quiescent_agrees s;
    // SMKM.supported_profile_application_record_material_agrees s.client s.server
    // unfolds definitionally to the two peer_record_material_agrees conjuncts.
    assert (SMKM.supported_profile_application_record_material_agrees s.client s.server)
  end

(**
  Flagship theorem: on *every* run of the system from the initial state, it is
  *always* the case that if the system is quiescent, has not rekeyed, and the
  handshake has completed on both endpoints then the application record-key
  material agrees.
**)
val lemma_flagship_record_material_agreement
  (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c)
      (ensures
        T.ag tls_sys_step
          record_material_agrees_when_ready_scoped
          (initial_tls_system cfg_c cfg_s))
let lemma_flagship_record_material_agreement cfg_c cfg_s =
  let s0 = initial_tls_system cfg_c cfg_s in
  introduce
    forall (s':tls_system_state).
      T.reachable tls_sys_step s0 s' ==> record_material_agrees_when_ready_scoped s'
  with begin
    introduce
      T.reachable tls_sys_step s0 s' ==> record_material_agrees_when_ready_scoped s'
    with begin
      introduce
        (tls_no_rekeying s' /\ tls_quiescent s' /\ tls_application_ready s' /\
         CCShape.no_buffering_steps s'.client.CS.cs_event_log) ==>
          (SMKM.peer_record_material_agrees
             (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) s'.client s'.server /\
           SMKM.peer_record_material_agrees
             (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) s'.client s'.server)
      with begin
        // tls_no_rekeying s' (from _ant) unlocks the combined-invariant reachability.
        lemma_reachable_inv cfg_c cfg_s s';
        lemma_inv_implies_agreement s'
      end
    end
  end;
  T.lemma_ag_of_invariant tls_sys_step record_material_agrees_when_ready_scoped s0

(** ─────────────────────────────────────────────────────────────────────────
    A next-step (X) property exercising the operator vocabulary.
    ───────────────────────────────────────────────────────────────────────── **)

(** A message is in flight (the system is not quiescent). **)
let system_in_flight (s:tls_system_state) : prop = ~(tls_quiescent s)

(**
  From any in-flight state the *only* enabled transitions are deliveries (every
  send/local step requires a quiescent channel), and a delivery returns the
  channel to quiet.  Hence on any run, whenever a message is in flight the *next*
  state is quiescent: `X quiescent` — a message in flight is delivered in exactly
  one step.
**)
val lemma_x_delivery_completes (p:T.path tls_system_state) (i:nat)
  : Lemma
      (requires T.is_run tls_sys_step p /\ system_in_flight (p i))
      (ensures T.holds_X tls_quiescent (T.shift p i))
let lemma_x_delivery_completes p i =
  let a = p i in
  let b = p (i + 1) in
  assert (tls_sys_step a b);        // from is_run at index i
  assert (MP.ToServer? a.channel \/ MP.ToClient? a.channel);  // a is in flight
  // the product's channel discipline gates sends and local steps on
  // `MP.Quiet? a.channel`, so only a deliver step is enabled from an in-flight
  // state, and every deliver step returns the channel to `MP.Quiet`.
  assert (T.shift p i 1 == b)
