module TLS13.ConnectionState.AppDataBufferEmpty

module CS  = TLS13.Spec.StateMachine
module SMR = TLS13.Spec.StateMachine.Reachability
module RTC = FStar.ReflexiveTransitiveClosure
module ID  = FStar.IndefiniteDescription
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog

(* ------------------------------------------------------------------ *)
(* The step-stable shape.                                              *)
(*                                                                     *)
(* Both conjuncts are needed at once: [buf_at_appdata] alone is NOT     *)
(* step-stable, because the SERVER enters [ControlApplicationData] by a *)
(* transition that carries no buffer guard, and only [buf_off_client]   *)
(* explains why the server's buffer was empty to begin with.            *)
(* ------------------------------------------------------------------ *)

let buf_empty (m:CS.connection_model) : prop =
  CS.protected_handshake_buffer_empty m

let buf_off_client (m:CS.connection_model) : prop =
  ~(m.CS.model_config.CS.config_role == CS.ClientEndpoint) ==> buf_empty m

let buf_at_appdata (m:CS.connection_model) : prop =
  m.CS.model_control == CS.ControlApplicationData ==> buf_empty m

let model_shape (m:CS.connection_model) : prop =
  buf_off_client m /\ buf_at_appdata m

let conn_shape (st:CS.connection_state) : prop = model_shape st.CS.cs_model

(* ------------------------------------------------------------------ *)
(* Per-step preservation.                                              *)
(* ------------------------------------------------------------------ *)

(** The handshake-message dispatch, isolated so its enumeration is a small
    self-contained query.  Two facts come out of it:

      - `step_handshake_message` NEVER writes the protected-handshake pair:
        the four `hs_buffers` updates it performs
        (`hb_client_hello_bytes`, `hb_server_hello_bytes`,
        `hb_certificate_leaf_der`, `hb_certificate_verify_input`) all go
        through `{ hs.hs_buffers with ... }`, leaving
        `hb_encrypted_server_handshake_bytes`/`_parsed` untouched; and

      - the only arm reaching `ControlApplicationData` with a CLIENT role is
        `CL.Sent, Finished, HsServerFinishedVerified`, whose legality guard
        contains `protected_handshake_buffer_empty model` verbatim. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 100"
let lemma_step_handshake_buffer
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg)
  (m':CS.connection_model)
  : Lemma
      (requires CS.legal_handshake_message m dir hm /\
                CS.step_handshake_message m dir hm == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes /\
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed /\
        m'.CS.model_config.CS.config_role == m.CS.model_config.CS.config_role /\
        (m'.CS.model_control == CS.ControlApplicationData /\
         m.CS.model_config.CS.config_role == CS.ClientEndpoint ==> buf_empty m))
  = ()
#pop-options

(** The `step_tls_message` dispatch.  Non-handshake TLS messages
    (application data, alerts, key update, CCS, ignored post-handshake) rewrite
    neither `hs_buffers` nor `model_config`, and the only one of them that can
    sit at `ControlApplicationData` starts there. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200"
let lemma_step_tls_buffer
  (m:CS.connection_model) (dir:CS.direction) (msg:M.tls_message)
  (m':CS.connection_model)
  : Lemma
      (requires CS.legal_tls_message m dir msg /\
                CS.step_tls_message m dir msg == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes /\
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed /\
        m'.CS.model_config.CS.config_role == m.CS.model_config.CS.config_role /\
        (m'.CS.model_control == CS.ControlApplicationData /\
         m.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
           buf_empty m \/ m.CS.model_control == CS.ControlApplicationData))
  = match msg with
    | M.TlsHandshake hm -> lemma_step_handshake_buffer m dir hm m'
    | _ -> ()
#pop-options

(** The `step_local_event` dispatch.  The two local arms that touch
    `hs_buffers` write `hb_certificate_verify_input` only; the one local arm
    reaching `ControlApplicationData` (`LocalVerifyClientFinished` at
    `HsClientFinishedReceived`) is pinned by `legal_local_event` to
    `ServerEndpoint`, so it never fires at a client. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 150"
let lemma_step_local_buffer
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires CS.legal_local_event m lev /\
                CS.step_local_event m lev == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes /\
        m'.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed ==
        m.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed /\
        m'.CS.model_config.CS.config_role == m.CS.model_config.CS.config_role /\
        (m'.CS.model_control == CS.ControlApplicationData /\
         m.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
           m.CS.model_control == CS.ControlApplicationData))
  = ()
#pop-options

(** The `ConnProtectedHandshake` arm.  This is the ONLY event that writes the
    protected-handshake buffer, so it is the only arm where the conclusion is
    not simply inherited.

    - `buf_off_client m'`: `legal_protected_handshake_step` pins
      `config_role == ClientEndpoint`, and the role is preserved, so
      `buf_off_client m'` is VACUOUS -- there is nothing to prove.
    - `buf_at_appdata m'`: the post-state control is that of
      `step_handshake_message m CL.Received step.protected_handshake_message`
      (the two post-processing rewrites touch only `model_record` and
      `hs_buffers`).  With the role pinned to `ClientEndpoint`, the only
      `legal_handshake_message` arm reaching `ControlApplicationData` at a
      client is `CL.Sent, Finished, HsServerFinishedVerified`, and this step is
      `CL.Received`.  So `m'.model_control =!= ControlApplicationData` and
      `buf_at_appdata m'` is vacuous too. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 150"
let lemma_step_protected_buffer
  (m:CS.connection_model) (step:CS.protected_handshake_step)
  (m':CS.connection_model)
  : Lemma
      (requires CS.legal_protected_handshake_step m step /\
                CS.step_protected_handshake m step == Some m')
      (ensures
        m'.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        ~(m'.CS.model_control == CS.ControlApplicationData))
  =
    if step.CS.protected_handshake_buffering
    then
      (* A buffering step touches neither the role nor the control state, and
         its legality confines it to a handshaking stage. *)
      ()
    else
    let hm = step.CS.protected_handshake_message in
    match CS.step_handshake_message m CL.Received hm with
    | Some stepped -> lemma_step_handshake_buffer m CL.Received hm stepped
    | None -> ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_step_model_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires model_shape m /\ CS.legal_event m ev /\
                    CS.step_model m ev == Some m')
          (ensures model_shape m')
  = match ev with
    | CS.ConnNetworkEvent dm ->
      lemma_step_tls_buffer m dm.CL.message_direction dm.CL.message_value m'
    | CS.ConnProtectedHandshake step ->
      lemma_step_protected_buffer m step m'
    (* A cleartext buffering step rewrites only the cleartext handshake
       buffer, so the application-data buffer is preserved verbatim. *)
    | CS.ConnCleartextHandshake step -> ()
    | CS.ConnLocalEvent lev ->
      lemma_step_local_buffer m lev m'
#pop-options

(* ------------------------------------------------------------------ *)
(* Closure over the reachability relation.                             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_shape (st0 st1:CS.connection_state)
  : Lemma (requires conn_shape st0 /\ SMR.connection_state_single_step st0 st1)
          (ensures conn_shape st1)
=
  let delta_w = ID.indefinite_description_ghost CS.connection_delta
    (fun delta -> CS.legal_connection_delta st0 delta st1) in
  let delta : CS.connection_delta = delta_w in
  assert (CS.legal_connection_delta st0 delta st1);
  assert (CS.legal_event st0.CS.cs_model delta.CS.delta_event);
  assert (CS.step_model st0.CS.cs_model delta.CS.delta_event == Some st1.CS.cs_model);
  lemma_step_model_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_shape (_:unit)
  : Lemma (ensures forall (x y:CS.connection_state).
      {:pattern (conn_shape y); (SMR.connection_state_single_step x y)}
      conn_shape x /\ SMR.connection_state_single_step x y ==> conn_shape y)
=
  introduce forall (x y:CS.connection_state).
    conn_shape x /\ SMR.connection_state_single_step x y ==> conn_shape y
  with introduce _ ==> _ with lemma_delta_shape x y

let lemma_initial_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_shape (CS.initial cfg))
= ()

let lemma_reachable_shape (st:CS.connection_state)
  : Lemma (requires SMR.connection_state_consistent st)
          (ensures conn_shape st)
=
  lemma_initial_shape st.CS.cs_model.CS.model_config;
  lemma_single_step_shape ();
  let p = conn_shape in
  let stable : squash (forall (x y:CS.connection_state).
      {:pattern (p y); (SMR.connection_state_single_step x y)}
      p x /\ SMR.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure SMR.connection_state_single_step p stable;
  assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)

let lemma_connection_appdata_protected_handshake_buffer_empty st =
  lemma_reachable_shape st

let lemma_connection_non_client_protected_handshake_buffer_empty st =
  lemma_reachable_shape st
