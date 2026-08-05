module TLS13.System.WireStep.StartShape

(**
  `client_start_shape` and its one-step preservation lemma.

  Factored out of `TLS13.System.WireStep`: the lemma is a pure `()` proof over
  the full `legal_event`/`step_model` case analysis, and under Z3 4.15.3 it no
  longer fits in a sensible rlimit when discharged against WireStep's ~2300-line
  ambient context (every prior definition in that module is in the SMT context).
  In this module the same proof, at the same fuel/ifuel/rlimit, discharges in
  seconds.  Nothing about the statement changed.
 **)

module CS = TLS13.Spec.StateMachine

(** Once a client has recorded its handshake-start parameters, they match the
    (immutable) config.  Set exactly at `LocalStartHandshake` whose legality
    forces `start_matches_config`, and preserved elsewhere (config is
    immutable). **)
let client_start_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  (match m.CS.model_handshake.CS.hs_start with
   | Some start -> CS.start_matches_config m.CS.model_config start
   | None -> True)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** A single legal step preserves `client_start_shape`. **)
let lemma_step_model_preserves_client_start_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\ CS.step_model m ev == Some m' /\ client_start_shape m)
      (ensures client_start_shape m')
  = ()
#pop-options
