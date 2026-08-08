module TLS13.System.StreamTemporal

(**
  THE APPLICATION-DATA STREAM-INTEGRITY FLAGSHIP.

  Using the generic path-based operators of `Common.Temporal` over the transition
  system of `TLS13.System`, this module proves, in the same clean LTL /
  `system_state` style as the record-key-material flagship
  (`TLS13.System.Temporal.lemma_flagship_record_material_agreement`):

    AG ( no-rekeying ==> stream_integrity_holds )

  i.e. "on every run of the client<->server system, at every reachable state, each
  endpoint's received application byte stream is a PREFIX of its peer's sent
  application byte stream" — no bytes are invented, reordered, dropped from the
  middle, or delivered out of band, in either direction, at any point of the run,
  including mid-flight and after either endpoint has failed or begun closing.

  ── WHY THE ANTECEDENT IS WHERE IT IS ──────────────────────────────────────
  `tls_no_rekeying` sits in the ANTECEDENT of the scoped state predicate, exactly
  as `TLS13.System.Temporal.record_material_agrees_when_ready_scoped` places it.
  That is what discharges the corresponding entry hypothesis of
  `ASI.lemma_reachable_app_stream_inv` from INSIDE the `introduce`, so the AG is
  a statement about all runs and not just about a restricted step relation.

  ── THE ENTRY HYPOTHESIS `server_config_valid_e2e` ─────────────────────────
  Unlike the record-material flagship, this theorem carries
  `SY.server_config_valid_e2e (CS.initial cfg_s)` in its `requires`.  It comes
  from `AEI.lemma_reachable_stream2_inv`, and it is an IMPL-SIDE bound on the
  server's certificate chain (its wire encoding fits the record-layer budget)
  which is NOT derivable from spec-level reachability: nothing in the transition
  system constrains how large a configured certificate is.  It is a
  well-formedness side condition on the deployment, discharged once by any
  concrete server configuration, not a weakening of the temporal statement.
  (Removing it is the separately-tracked "Option B" and is out of scope here.)

  ── WHAT IS PROVED VS. `SY.app_pairing` ────────────────────────────────────
  The invariant carried through the induction is `ASI.app_stream_pairing`, NOT
  `SY.app_pairing`.  See the header of `TLS13.System.AppStreamInv` for the full
  argument; in brief, `SY.app_pairing`'s UNGATED exact equality is
  true-but-underivable, because its delivery case needs record-sequence alignment
  and alignment is only available outside the closing region.  `app_stream_pairing`
  splits the statement into an ungated PREFIX clause — which is literally
  `SY.stream_integrity_holds`, the thing this flagship needs — plus an exact
  equality gated on the receiver being outside the closing region.  Consequently
  the frozen pure reduction `SY.lemma_app_pairing_implies_stream_integrity` is
  BYPASSED here rather than being wrong: it remains correct, it simply asks for a
  strictly stronger hypothesis than the conclusion requires.
**)

module T   = Common.Temporal
module RTC = FStar.ReflexiveTransitiveClosure
module CS  = TLS13.Spec.StateMachine
module WFL = TLS13.Spec.WireFormatLemmas
module SY  = TLS13.System
module ASI = TLS13.System.AppStreamInv

(** The flagship state predicate (scoped): at any non-rekeyed state, each
    endpoint's received application stream is a prefix of its peer's sent
    application stream. **)
let stream_integrity_scoped : T.sprop SY.tls_system_state = fun s ->
  SY.tls_no_rekeying s ==> SY.stream_integrity_holds s

(** The byte-level invariant entails the flagship state predicate.  This is the
    seq-level -> byte-level bridge, and it is DEFINITIONAL: the two ungated
    clauses of `ASI.app_stream_pairing` are the two conjuncts of
    `SY.stream_integrity_holds`, with the in-flight delta as the `rest` witness. **)
val lemma_app_stream_pairing_implies_integrity (s:SY.tls_system_state)
  : Lemma (requires ASI.app_stream_pairing s)
          (ensures SY.stream_integrity_holds s)
let lemma_app_stream_pairing_implies_integrity s =
  ASI.lemma_app_stream_pairing_implies_stream_integrity s

(**
  FLAGSHIP THEOREM.  On every run of the system from the initial state it is
  ALWAYS the case that, absent rekeying, application-data stream integrity holds
  in both directions.
**)
val lemma_flagship_stream_integrity
  (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c /\
        SY.server_config_valid_e2e (CS.initial cfg_s))
      (ensures
        T.ag SY.tls_sys_step
          stream_integrity_scoped
          (SY.initial_tls_system cfg_c cfg_s))
let lemma_flagship_stream_integrity cfg_c cfg_s =
  let s0 = SY.initial_tls_system cfg_c cfg_s in
  introduce
    forall (s':SY.tls_system_state).
      T.reachable SY.tls_sys_step s0 s' ==> stream_integrity_scoped s'
  with begin
    introduce
      T.reachable SY.tls_sys_step s0 s' ==> stream_integrity_scoped s'
    with begin
      introduce SY.tls_no_rekeying s' ==> SY.stream_integrity_holds s'
      with begin
        // `tls_no_rekeying s'` (from the antecedent) unlocks the byte-level
        // reachability payoff; the bridge below is definitional.
        ASI.lemma_reachable_app_stream_inv cfg_c cfg_s s';
        lemma_app_stream_pairing_implies_integrity s'
      end
    end
  end;
  T.lemma_ag_of_invariant SY.tls_sys_step stream_integrity_scoped s0
