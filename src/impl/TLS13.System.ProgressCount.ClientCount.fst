module TLS13.System.ProgressCount.ClientCount

(**
  The client progress count and its control-change progress lemma.

  Factored out of `TLS13.System.ProgressCount`.  Both lemmas are pure `()`
  proofs over the full `legal_event`/`step_model` case analysis.  Under Z3
  4.15.3 `lemma_client_control_change_progress` no longer fits in rlimit 80 when
  discharged against ProgressCount's ~500-line ambient context (every prior
  definition in that module — including the whole server count — is in the SMT
  context); here, against `TLS13.Spec.StateMachine` and the four small
  definitions below, it discharges comfortably.  Nothing about the statements
  changed.

  `lemma_client_progress_step_bound` deliberately stays in
  `TLS13.System.ProgressCount`: it verifies fine there, and keeping it out of
  this module keeps this module's SMT context down to the four definitions
  below, which is what makes the control-change lemma cheap.

  `TLS13.System.ProgressCount` re-exports these with `include`, so every client
  of that module sees exactly the names it saw before.
 **)

module CS  = TLS13.Spec.StateMachine
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module B   = TLS13.Bytes
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog

(** Control stages strictly before application data (and before any close). **)
let pre_appdata_control (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> false
  | _ -> true

(** All five key-schedule slots empty. **)
let keys_all_none (keys:CS.key_schedule_state) : prop =
  keys.CS.ks_shared_secret == None /\
  keys.CS.ks_client_handshake_traffic == None /\
  keys.CS.ks_server_handshake_traffic == None /\
  keys.CS.ks_client_application_traffic == None /\
  keys.CS.ks_server_application_traffic == None

let client_progress (m:CS.connection_model) : int =
  match m.CS.model_control with
  | CS.ControlNew -> 0
  | CS.ControlHandshaking _ -> 14 - PNI.client_application_progress_rank m
  | _ -> 0

(** The one client region-entry shape fact: at ControlNew the key schedule is
    empty (no install can have fired before leaving ControlNew).  Every other
    client boundary is handshake-stage -> handshake-stage, handled uniformly by
    the rank step lemma. **)
let client_micro_shape (m:CS.connection_model) : prop =
  CS.ControlNew? m.CS.model_control ==>
    keys_all_none m.CS.model_handshake.CS.hs_keys

(** A legal step that CHANGES the control state (and stays
    pre-application-data) strictly increases the client progress count.  This is
    the lower-bound half needed to keep the forward LENGTH invariant
    (`client_len_ok`) under the stricter internal-local guard
    `client_local_advances` (progress↑ ∨ control-changed), which — unlike the
    send/deliver guard — also forbids the internal application-data self-loop.

    The client version needs no restriction: every pre-appdata client control
    change strictly advances progress. **)
(** The `step_handshake_message` half of the control-change progress lemma,
    isolated so that BOTH routes into it -- an ordinary received
    `ConnNetworkEvent (TlsHandshake hm)` and the protected-record
    `ConnProtectedHandshake` step -- can reuse the same enumeration. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 80"
let lemma_client_control_change_progress_handshake
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg)
  (m':CS.connection_model)
  : Lemma (requires
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            CS.legal_handshake_message m dir hm /\
            CS.step_handshake_message m dir hm == Some m' /\
            pre_appdata_control m.CS.model_control /\
            pre_appdata_control m'.CS.model_control /\
            client_micro_shape m /\
            ~(m'.CS.model_control == m.CS.model_control))
          (ensures client_progress m' > client_progress m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 80"
let lemma_client_control_change_progress
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            pre_appdata_control m.CS.model_control /\
            pre_appdata_control m'.CS.model_control /\
            client_micro_shape m /\
            ~(m'.CS.model_control == m.CS.model_control))
          (ensures client_progress m' > client_progress m)
  = match ev with
    | CS.ConnNetworkEvent _ -> ()
    | CS.ConnLocalEvent _ -> ()
    (* A cleartext buffering step changes only the pending cleartext buffer. *)
    | CS.ConnCleartextHandshake step ->
      assert_norm (CS.step_model m (CS.ConnCleartextHandshake step) ==
                   CS.step_cleartext_handshake m step);
      CS.lemma_step_cleartext_handshake_inert m step
    | CS.ConnProtectedHandshake step ->
      (* `step_protected_handshake` is a RECEIVED handshake message step.  The
         two post-processing rewrites it applies on top of
         `step_handshake_message` touch only `model_record` (the tail
         `record_read` restore) and `model_handshake.hs_buffers` (the pending
         protected-handshake fragment); neither `model_control` nor
         `model_handshake.hs_keys` moves.  Since `client_progress` is a
         function of exactly those two, the stepped model and `m'` have equal
         progress, and the shared handshake enumeration applies.  Legality is
         supplied by `legal_protected_handshake_step`, which contains
         `legal_handshake_message m CL.Received
         step.protected_handshake_message` verbatim. *)
      let hm = step.CS.protected_handshake_message in
      (match CS.step_handshake_message m CL.Received hm with
       | Some stepped ->
         assert (m'.CS.model_control == stepped.CS.model_control);
         assert (m'.CS.model_handshake.CS.hs_keys ==
                 stepped.CS.model_handshake.CS.hs_keys);
         assert (client_progress m' == client_progress stepped);
         lemma_client_control_change_progress_handshake m CL.Received hm stepped
       | None -> ())
#pop-options
