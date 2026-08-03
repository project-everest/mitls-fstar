module TLS13.System.WireStep

(**
  Pure step-inversion helper lemmas for the wire-level combined system
  (TLS13.System).  These are self-contained facts about the ConnectionState
  step relation used to discharge the wire/projection FACTS of `tls_system_inv`:

    * handshake-hello field MONOTONICITY across a single legal step
      (once `hs_client_hello`/`hs_server_hello` is `Some x`, it stays `Some x`);
    * the config -> supported-wire-profile derivation for a freshly-sent
      ClientHello.

  Everything here is pure F* over `TLS13.Spec.StateMachine`; no admits.
**)

module CS  = TLS13.Spec.StateMachine
module WSS = TLS13.System.WireStep.StartShape
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog
module B   = TLS13.Bytes
module Seq = FStar.Seq
module WFL = TLS13.Spec.WireFormatLemmas
module T   = TLS13.Types
module W   = TLS13.Wire.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module ID  = FStar.IndefiniteDescription
module CSL = TLS13.ConnectionState.Lemmas
module EC  = TLS13.Spec.Endpoint.Client
module EAPI = TLS13.Spec.Endpoint.API
module SMR  = TLS13.Spec.StateMachine.Reachability
module SMCan = TLS13.Spec.StateMachine.Canonical
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module ES  = TLS13.Spec.Endpoint.Server
module CW  = TLS13.Spec.Endpoint.Wire
module CTy = TLS13.Impl.CanonicalTypes
module SM  = Common.StateMachine
module WFSM = Common.WireFormatStateMachine
module WF  = Common.WireFormat
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module CT  = TLS13.Impl.Client.Types
module L   = FStar.List.Tot
module RVD = TLS13.Wire.Spec.RevealDecode
module WU  = TLS13.Wire.Spec.Reveal.Util
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module Sem = TLS13.Wire.Semantics
module RVDH = TLS13.Wire.Spec.Reveal.Handshake
module GHS = TLS13.Wire.Generated.Handshake
module INJ = TLS13.Wire.Spec.Reveal.Injective
module LP  = LowParse.Spec

(** Hello-field stability predicate: the cleartext-hello fields plus `hs_start`
    are monotone across a step. **)
let hs_hellos_stable (m0 m1:CS.connection_model) : prop =
  (Some? m0.CS.model_handshake.CS.hs_client_hello ==>
     m1.CS.model_handshake.CS.hs_client_hello == m0.CS.model_handshake.CS.hs_client_hello) /\
  (Some? m0.CS.model_handshake.CS.hs_server_hello ==>
     m1.CS.model_handshake.CS.hs_server_hello == m0.CS.model_handshake.CS.hs_server_hello) /\
  (Some? m0.CS.model_handshake.CS.hs_start ==>
     m1.CS.model_handshake.CS.hs_start == m0.CS.model_handshake.CS.hs_start)

(** A single legal step preserves the two cleartext-hello fields.

    The only step that RE-ASSIGNS an already-populated hello field is
    `LocalSelectServerParameters`, and its legality
    (`hs.hs_client_hello == Some selection.server_selected_client_hello`) forces
    that assignment to be a no-op.  Every other assignment happens from a control
    stage at which the field was still `None`. **)
// NOTE: a general step monotonicity for the hello fields is NOT provable from
// `legal_event`+`step_model` alone (an ill-formed `m0` with a hello already set
// at a pre-install control would be overwritten).  It requires an EXACT
// control->field-population well-formedness (`hellos_shape`), below.

(** EXACT control -> {hs_client_hello, hs_server_hello} population characteristic.
    Upper AND lower bounds, mirroring `step_handshake_message`/`step_local_event`.
    Terminal control states (Closing/Closed/Failed) impose no bound. **)
let hellos_shape (m:CS.connection_model) : prop =
  let h = m.CS.model_handshake in
  match m.CS.model_control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsNotStarted ->
    h.CS.hs_client_hello == None /\ h.CS.hs_server_hello == None /\
    h.CS.hs_start == None
  | CS.ControlHandshaking CS.HsStarted
  | CS.ControlHandshaking CS.HsAwaitingClientHello ->
    h.CS.hs_client_hello == None /\ h.CS.hs_server_hello == None
  | CS.ControlHandshaking CS.HsClientHelloSent
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    Some? h.CS.hs_client_hello /\ h.CS.hs_server_hello == None
  | CS.ControlHandshaking CS.HsServerHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified
  | CS.ControlHandshaking CS.HsClientFinishedSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello
  | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> True

(** A single legal step preserves `hellos_shape` AND the hello field values. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_step_model_preserves_hellos
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires CS.legal_event m0 ev /\ CS.step_model m0 ev == Some m1 /\ hellos_shape m0)
      (ensures hellos_shape m1 /\ hs_hellos_stable m0 m1)
  = match ev with
    | CS.ConnNetworkEvent _ -> ()
    | CS.ConnProtectedHandshake _ -> ()
    | CS.ConnLocalEvent _ -> ()
#pop-options

(** config profile + start/config + CH/start  ==>  supported CH wire profile. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_ch_profile_from_start_config
  (cfg:CS.connection_config) (start:CS.handshake_start) (ch:GCH.clientHello)
  : Lemma
      (requires
        WFL.supported_client_config_wire_profile cfg /\
        CS.start_matches_config cfg start /\
        CS.client_hello_matches_start start ch)
      (ensures WFL.supported_client_hello_wire_profile ch)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Received-ServerHello wire bridge support.

    Two self-contained pure facts feeding the `TLS13.System` SH-delivery bridge:

      * the record-parse image of a cleartext ServerHello raw byte string is
        exactly its canonical handshake serialization (used to identify the
        in-flight fragment with `W.serialize_handshake (M.ServerHello sh)`);

      * an RTC (reachable-shape) invariant on the SERVER endpoint: whenever the
        server has stored BOTH its ClientHello and its (sent) ServerHello, the
        ServerHello's cipher suite is one the stored ClientHello offered and its
        `body` is empty.  This is the ServerHello analogue of
        `CSL.lemma_connection_state_consistent_server_certificate_verify_body_empty`
        and is proven by the same `RTC.stable_on_closure` pattern.
    ───────────────────────────────────────────────────────────────────────── **)

(** The record-parse image of a cleartext ServerHello raw is its canonical
    handshake serialization. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_cleartext_server_hello_parse_record
  (sh:GSH.serverHello) (raw:B.bytes)
  : Lemma
      (requires
        B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640 /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello sh)) raw)
      (ensures
        W.parse_record_wire raw ==
          Some (T.Handshake, W.serialize_handshake (M.ServerHello sh), B.length raw))
=
  let fragment = W.serialize_handshake (M.ServerHello sh) in
  W.lemma_serialize_tls_message_handshake (M.ServerHello sh);
  assert (B.length fragment <= 16640);
  WFL.lemma_parse_record_wire_serialize_record T.Handshake fragment;
  assert (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh)) ==
          W.serialize_record T.Handshake fragment);
  assert (Seq.equal raw (W.serialize_record T.Handshake fragment));
  Seq.lemma_eq_elim raw (W.serialize_record T.Handshake fragment)
#pop-options

(** Server-endpoint reachable-shape: selection/hello cipher-and-body coherence. **)
let server_hello_cipher_body_reachable_shape (st:CS.connection_state) : prop =
  hellos_shape st.CS.cs_model /\
  (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
    ((match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection,
            st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some sel, Some ch ->
        CS.cipher_suite_offered (Sem.clientHello_cipher_suites ch) sel.CS.server_selected_cipher_suite
      | Some _, None -> False
      | None, _ -> True)
     /\
     (match st.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
            st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some (sh:GSH.serverHello), Some sel ->
        Sem.serverHello_cipher_suite sh == Some sel.CS.server_selected_cipher_suite /\
        B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640
      | Some _, None -> False
      | None, _ -> True)))

#push-options "--fuel 1 --ifuel 4 --z3rlimit 80"
let lemma_step_model_server_hello_cipher_body_reachable_shape
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires
        server_hello_cipher_body_reachable_shape
          { CS.cs_model = model; CS.cs_wire_log = CL.empty_raw_io_log; CS.cs_event_log = [] } /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        server_hello_cipher_body_reachable_shape
          { CS.cs_model = model'; CS.cs_wire_log = CL.empty_raw_io_log; CS.cs_event_log = [] })
=
  CSL.lemma_step_model_preserves_config model ev model';
  lemma_step_model_preserves_hellos model ev model'
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_connection_delta_server_hello_cipher_body_reachable_shape
  (st0:CS.connection_state) (st1:CS.connection_state)
  : Lemma
      (requires
        server_hello_cipher_body_reachable_shape st0 /\
        SMR.connection_state_single_step st0 st1)
      (ensures server_hello_cipher_body_reachable_shape st1)
=
  assert (exists delta. CS.legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      CS.connection_delta
      (fun delta -> CS.legal_connection_delta st0 delta st1) in
  let delta : CS.connection_delta = delta_w in
  assert (CS.legal_connection_delta st0 delta st1);
  assert (CS.legal_event st0.CS.cs_model delta.CS.delta_event);
  assert (CS.step_model st0.CS.cs_model delta.CS.delta_event == Some st1.CS.cs_model);
  lemma_step_model_server_hello_cipher_body_reachable_shape
    st0.CS.cs_model
    delta.CS.delta_event
    st1.CS.cs_model
#pop-options

let lemma_initial_server_hello_cipher_body_reachable_shape
  (cfg:CS.connection_config)
  : Lemma
      (ensures server_hello_cipher_body_reachable_shape (CS.initial cfg))
=
  ()

let lemma_single_step_server_hello_cipher_body_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern
            (server_hello_cipher_body_reachable_shape y);
            (SMR.connection_state_single_step x y)}
          server_hello_cipher_body_reachable_shape x /\
          SMR.connection_state_single_step x y ==>
          server_hello_cipher_body_reachable_shape y)
=
  introduce forall x y.
    server_hello_cipher_body_reachable_shape x /\
    SMR.connection_state_single_step x y ==>
    server_hello_cipher_body_reachable_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_server_hello_cipher_body_reachable_shape x y

(** The consumer: a consistent SERVER state that has stored both its ClientHello
    and its ServerHello has an empty-body ServerHello whose cipher suite the
    stored ClientHello offered. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_consistent_server_hello_cipher_body (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures
        (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
         Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
         Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello) ==>
        (let sh : GSH.serverHello = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_server_hello in
         let ch : GCH.clientHello = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
         (match Sem.serverHello_cipher_suite sh with
          | Some cs -> CS.cipher_suite_offered (Sem.clientHello_cipher_suites ch) cs
          | None -> False) /\
         B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640))
=
  let p = server_hello_cipher_body_reachable_shape in
  lemma_initial_server_hello_cipher_body_reachable_shape
    st.CS.cs_model.CS.model_config;
  lemma_single_step_server_hello_cipher_body_reachable_shape ();
  let stable :
    squash (
      forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    SMR.connection_state_single_step
    p
    stable;
  assert (p (CS.initial st.CS.cs_model.CS.model_config));
  assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ServerHello wire-size bound reachable-shape (endpoint-agnostic).

    With the QuackyDucky-generated (unbounded) [GSH.serverHello] record the old
    hand-written [M.server_hello] type no longer supplies the single-record wire
    bound for free.  But whenever a ServerHello is installed in the model — the
    server SENDs it (legal_event requires [server_hello_matches_selection], which
    carries the bound) or the client RECEIVEs it (legal_event requires the bound
    directly) — the wire image is bounded by 16640.  This RTC invariant restores,
    for BOTH endpoints, the record-parseability bound the deleted bounded type
    previously gave for free. **)
let server_hello_wire_bound_reachable_shape (st:CS.connection_state) : prop =
  hellos_shape st.CS.cs_model /\
  (match st.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
   | Some sh -> B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640
   | None -> True)

#push-options "--fuel 1 --ifuel 4 --z3rlimit 80"
let lemma_step_model_server_hello_wire_bound_reachable_shape
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires
        server_hello_wire_bound_reachable_shape
          { CS.cs_model = model; CS.cs_wire_log = CL.empty_raw_io_log; CS.cs_event_log = [] } /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        server_hello_wire_bound_reachable_shape
          { CS.cs_model = model'; CS.cs_wire_log = CL.empty_raw_io_log; CS.cs_event_log = [] })
=
  CSL.lemma_step_model_preserves_config model ev model';
  lemma_step_model_preserves_hellos model ev model'
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_connection_delta_server_hello_wire_bound_reachable_shape
  (st0:CS.connection_state) (st1:CS.connection_state)
  : Lemma
      (requires
        server_hello_wire_bound_reachable_shape st0 /\
        SMR.connection_state_single_step st0 st1)
      (ensures server_hello_wire_bound_reachable_shape st1)
=
  assert (exists delta. CS.legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      CS.connection_delta
      (fun delta -> CS.legal_connection_delta st0 delta st1) in
  let delta : CS.connection_delta = delta_w in
  assert (CS.legal_connection_delta st0 delta st1);
  assert (CS.legal_event st0.CS.cs_model delta.CS.delta_event);
  assert (CS.step_model st0.CS.cs_model delta.CS.delta_event == Some st1.CS.cs_model);
  lemma_step_model_server_hello_wire_bound_reachable_shape
    st0.CS.cs_model
    delta.CS.delta_event
    st1.CS.cs_model
#pop-options

let lemma_initial_server_hello_wire_bound_reachable_shape
  (cfg:CS.connection_config)
  : Lemma
      (ensures server_hello_wire_bound_reachable_shape (CS.initial cfg))
=
  ()

let lemma_single_step_server_hello_wire_bound_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern
            (server_hello_wire_bound_reachable_shape y);
            (SMR.connection_state_single_step x y)}
          server_hello_wire_bound_reachable_shape x /\
          SMR.connection_state_single_step x y ==>
          server_hello_wire_bound_reachable_shape y)
=
  introduce forall x y.
    server_hello_wire_bound_reachable_shape x /\
    SMR.connection_state_single_step x y ==>
    server_hello_wire_bound_reachable_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_server_hello_wire_bound_reachable_shape x y

(** The consumer: a consistent state (either endpoint) that has stored a
    ServerHello has a ServerHello whose wire image fits a single record. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_consistent_server_hello_wire_bound (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures
        (match st.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some sh -> B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640
         | None -> True))
=
  let p = server_hello_wire_bound_reachable_shape in
  lemma_initial_server_hello_wire_bound_reachable_shape
    st.CS.cs_model.CS.model_config;
  lemma_single_step_server_hello_wire_bound_reachable_shape ();
  let stable :
    squash (
      forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    SMR.connection_state_single_step
    p
    stable;
  assert (p (CS.initial st.CS.cs_model.CS.model_config));
  assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)
#pop-options

(** A cipher suite offered by the singleton chacha list IS chacha. **)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_cipher_suite_offered_singleton_chacha (suite:T.cipher_suite)
  : Lemma
      (requires
        CS.cipher_suite_offered [T.TLS_CHACHA20_POLY1305_SHA256] suite)
      (ensures suite == T.TLS_CHACHA20_POLY1305_SHA256)
=
  ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Byte-trace reachability: the maintained System invariant is that each
    endpoint's connection state is reachable, via the OFFICIAL canonical step
    relation, from its initial state (`CS.initial cfg`).  At a quiescent+ready
    state this yields `WFSM.valid_byte_trace`, the byte-level entry predicate of
    the clean16 FACT-4 producer.
    ───────────────────────────────────────────────────────────────────────── **)

(** Unrefined state-machine wrappers: identical to EC/ES.client/server_state_machine
    but without the role refinement on the initial-state parameter.
    Definitionally equal to the refined versions when the role holds. **)
let client_sm (init:CS.connection_state)
  : SM.state_machine CS.connection_state CW.wire_message CTy.client_local_event EAPI.local_output
  = { SM.sm_initial_state = init; SM.sm_step = EC.client_step #CTy.client_local_event }

let server_sm (init:CS.connection_state)
  : SM.state_machine CS.connection_state CW.wire_message CTy.server_local_event EAPI.local_output
  = { SM.sm_initial_state = init; SM.sm_step = ES.server_step #CTy.server_local_event }

let client_sys (init:CS.connection_state)
  : WFSM.wire_format_state_machine CS.connection_state CW.wire_message CTy.client_local_event EAPI.local_output
  = { WFSM.wfsm_state_machine = client_sm init; WFSM.wfsm_wire_format = CW.tls_record_wire_format }

let server_sys (init:CS.connection_state)
  : WFSM.wire_format_state_machine CS.connection_state CW.wire_message CTy.server_local_event EAPI.local_output
  = { WFSM.wfsm_state_machine = server_sm init; WFSM.wfsm_wire_format = CW.tls_record_wire_format }

(** Client is reachable from its `CS.initial cfg` via `client_step`. **)
let client_reachable (init:CS.connection_state) (st:CS.connection_state) : prop =
  SM.valid_state (client_sm init) st

(** Server is reachable from its `CS.initial cfg` via `server_step`. **)
let server_reachable (init:CS.connection_state) (st:CS.connection_state) : prop =
  SM.valid_state (server_sm init) st

(** One official client step extends reachability. **)
let lemma_client_reachable_step
  (init st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires client_reachable init st0 /\ EC.client_step st0 ev st1 out)
      (ensures client_reachable init st1)
  = SM.lemma_valid_state_after_step (client_sm init) st0 ev st1 out

(** One official server step extends reachability. **)
let lemma_server_reachable_step
  (init st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires server_reachable init st0 /\ ES.server_step st0 ev st1 out)
      (ensures server_reachable init st1)
  = SM.lemma_valid_state_after_step (server_sm init) st0 ev st1 out

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30 --split_queries always"
(** Reachability from `CS.initial cfg` yields the byte-level `valid_byte_trace`. **)
let lemma_client_valid_byte_trace_of_reachable
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma
      (requires client_reachable (CS.initial cfg) client /\
               cfg.CS.config_role == CS.ClientEndpoint)
      (ensures
        WFSM.valid_byte_trace
          (client_sys (CS.initial cfg))
          client.CS.cs_wire_log.CL.raw_received
          client
          client.CS.cs_wire_log.CL.raw_sent
          Seq.empty)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns
      WFSM.valid_byte_trace (client_sys init)
        client.CS.cs_wire_log.CL.raw_received client
        client.CS.cs_wire_log.CL.raw_sent Seq.empty
    with _.
    (
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let out_msgs = SM.trace_wire_outputs trace in
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      Seq.lemma_eq_elim
        client.CS.cs_wire_log.CL.raw_received
        (WF.serialize_all CW.tls_record_wire_format in_msgs);
      introduce exists (tr:list (SM.transition CS.connection_state CW.wire_message
                                   CTy.client_local_event EAPI.local_output)).
        SM.trace_reaches sm init tr client /\
        WF.parses_as CW.tls_record_wire_format
          client.CS.cs_wire_log.CL.raw_received (WFSM.trace_input_messages tr) Seq.empty /\
        Seq.equal client.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all CW.tls_record_wire_format (SM.trace_wire_outputs tr))
      with trace and ()
    )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30 --split_queries always"
(** Server-symmetric. **)
let lemma_server_valid_byte_trace_of_reachable
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma
      (requires server_reachable (CS.initial cfg) server /\
               cfg.CS.config_role == CS.ServerEndpoint)
      (ensures
        WFSM.valid_byte_trace
          (server_sys (CS.initial cfg))
          server.CS.cs_wire_log.CL.raw_received
          server
          server.CS.cs_wire_log.CL.raw_sent
          Seq.empty)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns
      WFSM.valid_byte_trace (server_sys init)
        server.CS.cs_wire_log.CL.raw_received server
        server.CS.cs_wire_log.CL.raw_sent Seq.empty
    with _.
    (
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let out_msgs = SM.trace_wire_outputs trace in
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      Seq.lemma_eq_elim
        server.CS.cs_wire_log.CL.raw_received
        (WF.serialize_all CW.tls_record_wire_format in_msgs);
      introduce exists (tr:list (SM.transition CS.connection_state CW.wire_message
                                   CTy.server_local_event EAPI.local_output)).
        SM.trace_reaches sm init tr server /\
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received (WFSM.trace_input_messages tr) Seq.empty /\
        Seq.equal server.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all CW.tls_record_wire_format (SM.trace_wire_outputs tr))
      with trace and ()
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Per-shape raw-byte-log deltas (the channel-pairing one-step extension).

    Each honest system transition advances exactly one endpoint by one official
    step.  These lemmas package the resulting change to that endpoint's raw
    wire logs in the clean form the `byte_pairing` preservation needs:
      * a SEND (LocalEvent emitting `[w]`) appends `wire_serialize w` to `raw_sent`
        and leaves `raw_received` unchanged;
      * a LOCAL step (LocalEvent emitting `[]`) leaves both logs unchanged;
      * a DELIVER (WireEvent wire) appends `wire_serialize wire` to `raw_received`
        and leaves `raw_sent` unchanged (a receive emits no wire output).
    ───────────────────────────────────────────────────────────────────────── **)

(** A single-record wire output serializes to exactly that record's bytes. **)
let lemma_serialize_all_single_wire (w:CW.wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format [w])
          (CW.wire_serialize w))
  = Seq.append_empty_r (CW.wire_serialize w)

(** The empty wire output serializes to empty bytes. **)
let lemma_serialize_all_nil_wire (_:unit)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format [])
          B.empty)
  = ()

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** A server WireEvent (delivery) emits no wire output: `raw_sent` is empty in
    the delta, because `event_raw_delta_legal` pins the sent side of a `Received`
    event to empty. **)
let lemma_server_wire_event_no_output
  (st0 st1:CS.connection_state)
  (wire:CW.wire_message)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step #CTy.server_local_event st0 (SM.WireEvent wire) st1 out)
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          B.empty)
  = eliminate exists msg.
      (let conn_ev =
         CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = msg;
         } in
       CS.legal_connection_delta
         st0
         {
           CS.delta_event = conn_ev;
           CS.delta_raw_sent =
             WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire;
         }
         st1 /\
       SMCan.sent_event_nonempty_seal_projection
         st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection
         st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        B.empty
    with _. ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** A client WireEvent (delivery) emits no wire output (symmetric). **)
let lemma_client_wire_event_no_output
  (st0 st1:CS.connection_state)
  (wire:CW.wire_message)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step #CTy.client_local_event st0 (SM.WireEvent wire) st1 out)
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          B.empty)
  = eliminate exists (conn_ev:CS.conn_event).
      (EC.client_wire_received_event st0 wire conn_ev /\
       SMCan.canonical_wire_step
         st0
         st1
         conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
         (CW.wire_serialize wire) /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        B.empty
    with _. ()
#pop-options

(** The initial state is reachable (empty trace). **)
let lemma_client_reachable_initial (cfg:CS.connection_config)
  : Lemma (ensures client_reachable (CS.initial cfg) (CS.initial cfg))
  = let sm = client_sm (CS.initial cfg) in
    assert (SM.trace_reaches sm sm.SM.sm_initial_state [] (CS.initial cfg));
    introduce exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm sm.SM.sm_initial_state trace (CS.initial cfg)
    with [] and ()

let lemma_server_reachable_initial (cfg:CS.connection_config)
  : Lemma (ensures server_reachable (CS.initial cfg) (CS.initial cfg))
  = let sm = server_sm (CS.initial cfg) in
    assert (SM.trace_reaches sm sm.SM.sm_initial_state [] (CS.initial cfg));
    introduce exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm sm.SM.sm_initial_state trace (CS.initial cfg)
    with [] and ()

(** ClientHello wire round-trip: the wire image of a representable ClientHello
    parses back (through the generated codec) to the very same record.  This is
    the ClientHello analogue of the ServerHello parseback bridge and replaces the
    former hand-written [TLS13.Wire.Spec.Reveal.ClientHello.Parseback] module. **)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 40"
let lemma_ch_wire_parse_roundtrip (ch:GCH.clientHello)
  : Lemma
      (requires W.clientHello_representable ch)
      (ensures
        W.parse_tls_message T.Handshake (W.serialize_handshake (M.ClientHello ch)) ==
          Some (M.TlsHandshake (M.ClientHello ch)))
=
  let fragment = W.serialize_handshake (M.ClientHello ch) in
  RVDH.lemma_serialize_handshake_client_hello ch;
  Seq.lemma_eq_elim fragment
    (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch));
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_client_hello ch);
  RVDH.lemma_handshake_synth_client_hello ch;
  RVDH.lemma_ptm_handshake_some fragment (GHS.Body_client_hello ch) (M.ClientHello ch)
#pop-options

(**
  NON-VACUITY WITNESS (single-delivery inhabitation).

  This lemma refutes the exact unsatisfiability that made the OLD
  semantic-channel design vacuous.  In that design, delivering a ClientHello to
  the server required the SAME raw bytes to satisfy both

    * the sender's cleartext projection for its stored ClientHello; and
    * the receiver's [received_cleartext_tls_message_raw] projection, whose
      ClientHello special case forces a body-full parse (>= 5 bytes).

  Those two constraints were JOINTLY UNSATISFIABLE on the OLD hand-written model
  (whose sent ClientHello stored an empty verbatim [body] while the received one
  stored the full record bytes), so the server could never leave
  [HsAwaitingClientHello] and the flagship agreement theorem was vacuously true.

  With the QuackyDucky-generated INJECTIVE codec there is no longer a separate
  verbatim [body]: the received ClientHello record IS the parse image of the
  sent bytes, which round-trips back to the very same record.  Here we exhibit a
  common [raw] and a received [recv_ch] (= [sent_ch] up to wire image) satisfying
  BOTH projections, so a CH deliver-to-server transition
  (`TLS13.System.tls_step_deliver_to_server`) is inhabited -- not identically
  [False] -- and the vacuity source is gone.
**)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let lemma_ch_deliver_projection_inhabited (sent_ch:GCH.clientHello)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile sent_ch /\
        W.clientHello_representable sent_ch)
      (ensures
        (exists (raw:B.bytes) (recv_ch:GCH.clientHello).
          CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello sent_ch)) raw /\
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello recv_ch)) raw /\
          Seq.equal (W.serialize_handshake (M.ClientHello recv_ch))
                    (W.serialize_handshake (M.ClientHello sent_ch))))
  = let hs = M.ClientHello sent_ch in
    let msg = M.TlsHandshake hs in
    // raw is the sender's cleartext serialization of its stored CH.
    let frag0 = W.serialize_handshake hs in
    let raw = CS.serialized_cleartext_tls_message msg in
    // Sender-side cleartext projection holds reflexively (ClientHello is not HRR).
    assert (CS.cleartext_tls_message_raw msg raw);
    // Pin the record framing:  raw == serialize_record Handshake frag0.
    W.lemma_serialize_tls_message_handshake hs;
    assert (Seq.equal raw (W.serialize_record T.Handshake frag0));
    Seq.lemma_eq_elim raw (W.serialize_record T.Handshake frag0);
    // The handshake fragment fits a single record.
    WFL.lemma_serialize_handshake_client_hello_record_bound sent_ch;
    // Record round-trip:  parse_record_wire raw == Some (Handshake, frag0, len raw).
    WFL.lemma_parse_record_wire_serialize_record T.Handshake frag0;
    // Handshake-message round-trip:  frag0 parses back to the same CH record.
    lemma_ch_wire_parse_roundtrip sent_ch;
    // Assemble the receiver-side projection existential with fragment = frag0.
    introduce exists (fragment:B.bytes).
        W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
        W.parse_tls_message T.Handshake fragment ==
          Some (M.TlsHandshake (M.ClientHello sent_ch))
    with frag0 and ();
    assert (CS.received_cleartext_tls_message_raw
              (M.TlsHandshake (M.ClientHello sent_ch)) raw);
    introduce exists (raw':B.bytes) (recv_ch:GCH.clientHello).
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello sent_ch)) raw' /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello recv_ch)) raw' /\
        Seq.equal (W.serialize_handshake (M.ClientHello recv_ch))
                  (W.serialize_handshake (M.ClientHello sent_ch))
    with raw sent_ch and ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    APPLICATION-DATA RECORD REACHABILITY INVERSION.

    Two single-endpoint facts used by the `client_clean` ready-coupling of
    `TLS13.System`:

      * a reachable CLIENT at `ControlApplicationData` has sent (in its
        `raw_sent` byte log) at least one ApplicationData-typed record (its
        protected Finished);
      * a reachable SERVER whose `raw_received` byte log contains an
        ApplicationData-typed record has its control at or after receipt of the
        client Finished (`HsClientFinishedReceived`).

    Bridged at the System level by `byte_pairing` (client `raw_sent` == server
    `raw_received` at a quiet channel).
    ───────────────────────────────────────────────────────────────────────── **)

(** A wire-record message list contains an ApplicationData-typed record. **)
let list_has_appdata (msgs:list CW.wire_message) : prop =
  exists (m:CW.wire_message).
    L.memP m msgs /\ m.CW.wm_content_type == T.Application_data

(** A raw byte log parses into a wire-record list containing an
    ApplicationData-typed record.  A pure function of `raw` (hence stable under
    `Seq.equal`). **)
let raw_has_appdata_record (raw:B.bytes) : prop =
  exists (msgs:list CW.wire_message).
    WF.parses_as CW.tls_record_wire_format raw msgs Seq.empty /\
    list_has_appdata msgs

(** `raw_has_appdata_record` transports across byte-equal logs. **)
let lemma_raw_has_appdata_record_seq_equal (raw1 raw2:B.bytes)
  : Lemma
      (requires Seq.equal raw1 raw2 /\ raw_has_appdata_record raw1)
      (ensures raw_has_appdata_record raw2)
  = Seq.lemma_eq_elim raw1 raw2

(** The `tls_record_wire_format` record parser strictly consumes input: any
    successful parse leaves a shorter residual. **)
let lemma_wire_parse_strict_decrease (raw:B.bytes)
  : Lemma
      (ensures
        (match CW.wire_parse raw with
         | Some (_, after) -> B.length after < B.length raw
         | None -> True))
  = match W.parse_record_wire raw with
    | None -> ()
    | Some (content_type, fragment, consumed) ->
      W.lemma_parse_record_wire_some_consumed_positive raw content_type fragment consumed;
      Seq.lemma_len_slice raw consumed (B.length raw)

(** `parses_as` with empty residual is FUNCTIONAL: the record wire format admits
    at most one message decomposition of a given byte log (each record consumes
    a positive prefix). **)
let rec lemma_parses_as_functional
  (raw:B.bytes) (msgs1 msgs2:list CW.wire_message)
  : Lemma
      (requires
        WF.parses_as CW.tls_record_wire_format raw msgs1 Seq.empty /\
        WF.parses_as CW.tls_record_wire_format raw msgs2 Seq.empty)
      (ensures msgs1 == msgs2)
      (decreases msgs1)
  = match msgs1, msgs2 with
    | [], [] -> ()
    | [], w2 :: r2 ->
      // msgs1 = [] forces raw == empty; but msgs2 nonempty forces a positive parse.
      Seq.lemma_eq_elim raw Seq.empty;
      (match W.parse_record_wire raw with
       | None -> ()
       | Some (ct, frag, consumed) ->
         W.lemma_parse_record_wire_some_consumed_positive raw ct frag consumed)
    | w1 :: r1, [] ->
      Seq.lemma_eq_elim raw Seq.empty;
      (match W.parse_record_wire raw with
       | None -> ()
       | Some (ct, frag, consumed) ->
         W.lemma_parse_record_wire_some_consumed_positive raw ct frag consumed)
    | w1 :: r1, w2 :: r2 ->
      // Both decompositions start by parsing `raw`; `wire_parse` is a function,
      // so the first message and residual coincide.  Recurse on the residual.
      eliminate exists parsed1 after1.
        CW.wire_parse raw == Some (parsed1, after1) /\ parsed1 == w1 /\
        WF.parses_as CW.tls_record_wire_format after1 r1 Seq.empty
      returns msgs1 == msgs2
      with _p1.
      eliminate exists parsed2 after2.
        CW.wire_parse raw == Some (parsed2, after2) /\ parsed2 == w2 /\
        WF.parses_as CW.tls_record_wire_format after2 r2 Seq.empty
      returns msgs1 == msgs2
      with _p2.
      (lemma_parses_as_functional after1 r1 r2)

(** If the FIRST record of `raw` is ApplicationData-typed and `raw` decomposes
    into `msgs`, then `msgs` contains an ApplicationData-typed record. **)
let lemma_first_record_appdata (raw:B.bytes) (msgs:list CW.wire_message)
  : Lemma
      (requires
        (match W.parse_record_wire raw with
         | Some (ct, _, _) -> ct == T.Application_data
         | None -> False) /\
        WF.parses_as CW.tls_record_wire_format raw msgs Seq.empty)
      (ensures list_has_appdata msgs)
  = match msgs with
    | [] ->
      // Empty decomposition forces raw == empty, contradicting a positive parse.
      Seq.lemma_eq_elim raw Seq.empty;
      (match W.parse_record_wire raw with
       | Some (ct, frag, consumed) ->
         W.lemma_parse_record_wire_some_consumed_positive raw ct frag consumed)
    | w :: rest ->
      eliminate exists parsed after.
        CW.wire_parse raw == Some (parsed, after) /\ parsed == w /\
        WF.parses_as CW.tls_record_wire_format after rest Seq.empty
      returns list_has_appdata msgs
      with _p.
      (assert (w.CW.wm_content_type == T.Application_data);
       assert (L.memP w msgs))

(** ─────────────────────────────────────────────────────────────────────────
    PART 2 — single-endpoint control predicates and pure `step_model`
    inversion facts (server role).
    ───────────────────────────────────────────────────────────────────────── **)

(** The controls a reachable SERVER endpoint can occupy. **)
let server_ctrl_ok (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> true
  | _ -> false

(** Server control at or after receipt of the client Finished. **)
let server_post_cf_ctrl (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> true
  | _ -> false

#push-options "--fuel 2 --ifuel 3 --z3rlimit 30"
(** `step_model` never changes the (immutable) connection config. **)
let lemma_step_model_preserves_config
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires CS.step_model m ev == Some m')
          (ensures m'.CS.model_config == m.CS.model_config)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** SC1 — server control closure: a legal server-role step from a server control
    lands in a server control. **)
let lemma_server_ctrl_ok_step
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok m.CS.model_control)
          (ensures server_ctrl_ok m'.CS.model_control)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** SC2 — monotonicity of `post_cf`: once at/after client-Finished receipt, a
    legal server-role step stays at/after it. **)
let lemma_server_post_cf_monotone
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_post_cf_ctrl m.CS.model_control)
          (ensures server_post_cf_ctrl m'.CS.model_control)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
(** SC3-core — at a server control that is NOT yet post-CF, the only legal
    RECEIVED messages that keep the server out of the post-CF region are the
    cleartext ClientHello and ChangeCipherSpec (every protected receipt either is
    illegal or moves control into the post-CF region). **)
let lemma_server_recv_nonpostcf_msg
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (SMKM.received_tls_event msg) /\
            CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok m.CS.model_control /\
            ~(server_post_cf_ctrl m'.CS.model_control))
          (ensures
            (M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) \/
            msg == M.TlsChangeCipherSpec)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** A cleartext ClientHello / ChangeCipherSpec received-record has a record
    content type that is NOT ApplicationData. **)
let lemma_cleartext_recv_not_appdata
  (m:CS.connection_model) (msg:M.tls_message) (raw:B.bytes)
  : Lemma (requires
            ((M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) \/
             msg == M.TlsChangeCipherSpec) /\
            CS.network_message_raw_delta_legal m
              ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw)
          (ensures
            (match W.parse_record_wire raw with
             | Some (ct, _, _) -> ~(ct == T.Application_data)
             | None -> True))
  = match msg with
    | M.TlsHandshake (M.ClientHello ch) -> ()
    | M.TlsChangeCipherSpec ->
      W.lemma_serialize_tls_message_change_cipher_spec ();
      WFL.lemma_parse_record_wire_serialize_record T.Change_cipher_spec (B.singleton 1uy);
      Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec)
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** SC3 (server-step level) — a reachable-server WireEvent whose record has
    content type ApplicationData moves control into the post-CF region. **)
let lemma_server_step_recv_appdata_post_cf
  (st0:CS.connection_state)
  (wire:CW.wire_message)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            ES.server_step #CTy.server_local_event st0 (SM.WireEvent wire) st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control /\
            wire.CW.wm_content_type == T.Application_data)
          (ensures server_post_cf_ctrl st1.CS.cs_model.CS.model_control)
  = eliminate exists (msg:M.tls_message).
      (let conn_ev =
         CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = msg;
         } in
       CS.legal_connection_delta
         st0
         {
           CS.delta_event = conn_ev;
           CS.delta_raw_sent =
             WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire;
         }
         st1 /\
       SMCan.sent_event_nonempty_seal_projection
         st0.CS.cs_model
         conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection
         st0.CS.cs_model
         conn_ev
         (CW.wire_serialize wire) /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns server_post_cf_ctrl st1.CS.cs_model.CS.model_control
    with _.
    (
      let raw = CW.wire_serialize wire in
      assert (raw == wire.CW.wm_raw);
      assert (W.parse_record_wire raw ==
              Some (wire.CW.wm_content_type, wire.CW.wm_fragment, B.length raw));
      if server_post_cf_ctrl st1.CS.cs_model.CS.model_control then ()
      else (
        lemma_server_recv_nonpostcf_msg st0.CS.cs_model msg st1.CS.cs_model;
        lemma_cleartext_recv_not_appdata st0.CS.cs_model msg raw
      )
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** Server-step model facts: config immutability, server-control closure (SC1),
    and post-CF monotonicity (SC2), lifted from `step_model` to `server_step`. **)
let lemma_server_step_model_facts
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            ES.server_step st0 ev st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
          (ensures
            st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
            (server_ctrl_ok st0.CS.cs_model.CS.model_control ==>
               server_ctrl_ok st1.CS.cs_model.CS.model_control) /\
            (server_post_cf_ctrl st0.CS.cs_model.CS.model_control ==>
               server_post_cf_ctrl st1.CS.cs_model.CS.model_control))
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
         (server_ctrl_ok st0.CS.cs_model.CS.model_control ==>
            server_ctrl_ok st1.CS.cs_model.CS.model_control) /\
         (server_post_cf_ctrl st0.CS.cs_model.CS.model_control ==>
            server_post_cf_ctrl st1.CS.cs_model.CS.model_control))
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        lemma_step_model_preserves_config st0.CS.cs_model conn_ev st1.CS.cs_model;
        introduce
          server_ctrl_ok st0.CS.cs_model.CS.model_control ==>
            server_ctrl_ok st1.CS.cs_model.CS.model_control
        with _h. lemma_server_ctrl_ok_step st0.CS.cs_model conn_ev st1.CS.cs_model;
        introduce
          server_post_cf_ctrl st0.CS.cs_model.CS.model_control ==>
            server_post_cf_ctrl st1.CS.cs_model.CS.model_control
        with _h. lemma_server_post_cf_monotone st0.CS.cs_model conn_ev st1.CS.cs_model
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
         (server_ctrl_ok st0.CS.cs_model.CS.model_control ==>
            server_ctrl_ok st1.CS.cs_model.CS.model_control) /\
         (server_post_cf_ctrl st0.CS.cs_model.CS.model_control ==>
            server_post_cf_ctrl st1.CS.cs_model.CS.model_control))
      with _.
      (
        lemma_step_model_preserves_config st0.CS.cs_model conn_ev st1.CS.cs_model;
        introduce
          server_ctrl_ok st0.CS.cs_model.CS.model_control ==>
            server_ctrl_ok st1.CS.cs_model.CS.model_control
        with _h. lemma_server_ctrl_ok_step st0.CS.cs_model conn_ev st1.CS.cs_model;
        introduce
          server_post_cf_ctrl st0.CS.cs_model.CS.model_control ==>
            server_post_cf_ctrl st1.CS.cs_model.CS.model_control
        with _h. lemma_server_post_cf_monotone st0.CS.cs_model conn_ev st1.CS.cs_model
      )
#pop-options

(** `list_has_appdata` distributes over append. **)
let lemma_list_has_appdata_append (a b:list CW.wire_message)
  : Lemma (ensures
            (list_has_appdata (L.append a b) <==>
             (list_has_appdata a \/ list_has_appdata b)))
  = introduce
      list_has_appdata (L.append a b) ==> (list_has_appdata a \/ list_has_appdata b)
    with _.
      (eliminate exists (m:CW.wire_message).
         L.memP m (L.append a b) /\ m.CW.wm_content_type == T.Application_data
       returns (list_has_appdata a \/ list_has_appdata b)
       with _. L.append_memP a b m);
    introduce
      (list_has_appdata a \/ list_has_appdata b) ==> list_has_appdata (L.append a b)
    with _.
      (eliminate list_has_appdata a \/ list_has_appdata b
       returns list_has_appdata (L.append a b)
       with _la.
         (eliminate exists (m:CW.wire_message).
            L.memP m a /\ m.CW.wm_content_type == T.Application_data
          returns list_has_appdata (L.append a b)
          with _. L.append_memP a b m)
       and _lb.
         (eliminate exists (m:CW.wire_message).
            L.memP m b /\ m.CW.wm_content_type == T.Application_data
          returns list_has_appdata (L.append a b)
          with _. L.append_memP a b m))

(** ─────────────────────────────────────────────────────────────────────────
    PHASE 2 — ApplicationData-record COUNTING (cleartext-immune).

    Counts the number of `ApplicationData`-content-type wire records in a raw
    byte log.  ChangeCipherSpec and cleartext handshake records are NOT
    ApplicationData-typed, so they contribute 0 — hence these counts (unlike raw
    event-log length) are immune to stray CCS/cleartext inflation.
    ───────────────────────────────────────────────────────────────────────── **)

(** A total, `Seq.equal`-stable count of ApplicationData-typed records in a raw
    byte log. **)
let rec raw_appdata_count (raw:B.bytes) : GTot nat (decreases (B.length raw)) =
  match CW.wire_parse raw with
  | Some (m, after) ->
    if B.length after < B.length raw
    then (if m.CW.wm_content_type = T.Application_data then 1 else 0)
         + raw_appdata_count after
    else 0
  | None -> 0

(** The record-list analogue. **)
let rec list_appdata_count (msgs:list CW.wire_message) : nat =
  match msgs with
  | [] -> 0
  | m :: rest ->
    (if m.CW.wm_content_type = T.Application_data then 1 else 0)
    + list_appdata_count rest

(** `raw_appdata_count` transports across byte-equal logs. **)
let lemma_raw_appdata_count_seq_equal (raw1 raw2:B.bytes)
  : Lemma
      (requires Seq.equal raw1 raw2)
      (ensures raw_appdata_count raw1 == raw_appdata_count raw2)
  = Seq.lemma_eq_elim raw1 raw2

(** The empty byte log has count 0. **)
let lemma_raw_appdata_count_empty ()
  : Lemma (ensures raw_appdata_count B.empty == 0)
  = match CW.wire_parse B.empty with
    | None -> ()
    | Some (m, after) ->
      lemma_wire_parse_strict_decrease B.empty

(** PREFIX-PASSTHROUGH: if `raw` parses its first record as `m` leaving residual
    `after`, then appending arbitrary `delta` parses the SAME first record `m`
    and leaves residual `after ++ delta` (the record parser only consumes a
    fixed positive prefix; trailing bytes pass through untouched).  Proved from
    the exported `RVD.lemma_parse_record_wire_from_prefix` — no reliance on any
    non-exported PNTWL helper. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30 --split_queries always"
let lemma_wire_parse_append_first
  (raw after delta:B.bytes) (m:CW.wire_message)
  : Lemma
      (requires CW.wire_parse raw == Some (m, after))
      (ensures
        CW.wire_parse (B.append raw delta) == Some (m, B.append after delta))
  = let ct = m.CW.wm_content_type in
    let frag = m.CW.wm_fragment in
    let c = B.length m.CW.wm_raw in
    // Reveal wire_parse's structure by matching on the underlying record parse.
    match W.parse_record_wire raw with
    | None -> ()   // then wire_parse raw == None, contradicting the hypothesis
    | Some (ct0, frag0, consumed0) ->
      W.lemma_parse_record_wire_fragment_bound raw;
      W.lemma_parse_record_wire_some_consumed_positive raw ct0 frag0 consumed0;
      // wire_parse raw == Some(m0, after0); by hypothesis m0==m, after0==after.
      Seq.lemma_len_slice raw 0 consumed0;
      // Hence: parse_record_wire raw == Some(ct,frag,c), c == consumed0 <= length raw.
      assert (ct0 == ct /\ frag0 == frag /\ consumed0 == c);
      assert (W.parse_record_wire raw == Some (ct, frag, c));
      assert (m.CW.wm_raw == Seq.slice raw 0 c);
      assert (after == Seq.slice raw c (B.length raw));
      // m.wm_parse_ok: parse_record_wire m.wm_raw == Some(ct,frag,c).
      assert (W.parse_record_wire m.CW.wm_raw == Some (ct, frag, c));
      // raw == m.wm_raw ++ after
      Seq.lemma_split raw c;
      Seq.lemma_eq_elim raw (B.append m.CW.wm_raw after);
      let full = B.append raw delta in
      Seq.append_assoc m.CW.wm_raw after delta;
      Seq.lemma_eq_elim full (B.append m.CW.wm_raw (B.append after delta));
      Seq.lemma_len_append raw delta;
      Seq.lemma_len_append m.CW.wm_raw (B.append after delta);
      // slice full 0 c == m.wm_raw
      WU.lemma_slice_append_left m.CW.wm_raw (B.append after delta);
      Seq.lemma_eq_elim (Seq.slice full 0 c) m.CW.wm_raw;
      assert (W.parse_record_wire (Seq.slice full 0 c) == Some (ct, frag, c));
      RVD.lemma_parse_record_wire_from_prefix full ct frag c;
      assert (W.parse_record_wire full == Some (ct, frag, c));
      // residual of parsing full == slice full c (length full) == after ++ delta
      Seq.lemma_len_append after delta;
      Seq.slice_slice full c (B.length full) 0 (B.length full - c);
      Seq.lemma_eq_elim (Seq.slice full c (B.length full)) (B.append after delta)
#pop-options

(** A record `raw` whose first parse leaves a shorter residual: appending `delta`
    keeps the first record and grows the residual by `delta`. **)
let lemma_raw_appdata_count_append_helper
  (raw after delta:B.bytes) (m:CW.wire_message)
  : Lemma
      (requires
        CW.wire_parse raw == Some (m, after) /\
        B.length after < B.length raw)
      (ensures
        (let full = B.append raw delta in
         CW.wire_parse full == Some (m, B.append after delta) /\
         B.length (B.append after delta) < B.length full))
  = lemma_wire_parse_append_first raw after delta m;
    Seq.lemma_len_append raw delta;
    Seq.lemma_len_append after delta

(** COUNT-APPEND: appending `delta` to a record-aligned prefix `old` (one whose
    records exactly decompose `old`) splits the count additively at the boundary. **)
let rec lemma_raw_appdata_count_append
  (old delta:B.bytes) (msgs:list CW.wire_message)
  : Lemma
      (requires WF.parses_as CW.tls_record_wire_format old msgs Seq.empty)
      (ensures
        raw_appdata_count (B.append old delta)
          == raw_appdata_count old + raw_appdata_count delta)
      (decreases msgs)
  = match msgs with
    | [] ->
      // parses_as old [] empty ==> old is empty.
      Seq.lemma_eq_elim old Seq.empty;
      lemma_raw_appdata_count_empty ();
      Seq.lemma_eq_elim (B.append old delta) delta;
      lemma_raw_appdata_count_seq_equal (B.append old delta) delta
    | m :: rest ->
      eliminate exists parsed after.
        CW.wire_parse old == Some (parsed, after) /\ parsed == m /\
        WF.parses_as CW.tls_record_wire_format after rest Seq.empty
      returns
        raw_appdata_count (B.append old delta)
          == raw_appdata_count old + raw_appdata_count delta
      with _p.
      (
        lemma_wire_parse_strict_decrease old;
        lemma_raw_appdata_count_append_helper old after delta m;
        lemma_raw_appdata_count_append after delta rest
      )

(** GENERAL: count of a byte log that cleanly decomposes into `msgs` equals the
    record-list count.  Pure structural induction on the parse — no append/prefix
    facts, just the `parses_as` unfolding + strict decrease. **)
let rec lemma_raw_appdata_count_of_parse
  (raw:B.bytes) (msgs:list CW.wire_message)
  : Lemma
      (requires WF.parses_as CW.tls_record_wire_format raw msgs Seq.empty)
      (ensures raw_appdata_count raw == list_appdata_count msgs)
      (decreases msgs)
  = match msgs with
    | [] ->
      Seq.lemma_eq_elim raw Seq.empty;
      lemma_raw_appdata_count_empty ()
    | m :: rest ->
      eliminate exists parsed after.
        CW.wire_parse raw == Some (parsed, after) /\ parsed == m /\
        WF.parses_as CW.tls_record_wire_format after rest Seq.empty
      returns raw_appdata_count raw == list_appdata_count msgs
      with _p.
      (
        lemma_wire_parse_strict_decrease raw;
        lemma_raw_appdata_count_of_parse after rest
      )

(** COROLLARY — count of a fully-serialized record list equals the list count. **)
let lemma_raw_appdata_count_serialize_all
  (msgs:list CW.wire_message)
  : Lemma
      (ensures
        raw_appdata_count (WF.serialize_all CW.tls_record_wire_format msgs)
          == list_appdata_count msgs)
  = PNTWL.lemma_wire_parse_serialize_all_inverse msgs;
    lemma_raw_appdata_count_of_parse
      (WF.serialize_all CW.tls_record_wire_format msgs) msgs

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
(** Server trace induction: along any reachability trace from a server-role,
    server-control start state, the endpoint stays in a server control, keeps its
    config, and EITHER ends post-CF OR (started pre-CF and received no
    ApplicationData record along the trace). **)
let rec lemma_server_trace_appdata_post_cf
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control)
          (ensures
            server_ctrl_ok st1.CS.cs_model.CS.model_control /\
            st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
            (server_post_cf_ctrl st1.CS.cs_model.CS.model_control \/
             (~(server_post_cf_ctrl st0.CS.cs_model.CS.model_control) /\
              ~(list_has_appdata (WFSM.trace_input_messages trace)))))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_appdata_post_cf init s' st1 rest;
      lemma_list_has_appdata_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest);
      introduce
        ~(server_post_cf_ctrl s'.CS.cs_model.CS.model_control) ==>
          ~(list_has_appdata (WFSM.event_input_messages tr.SM.tr_event))
      with _.
        (match tr.SM.tr_event with
         | SM.WireEvent wire ->
           introduce
             list_has_appdata (WFSM.event_input_messages tr.SM.tr_event) ==> False
           with _hh.
             (assert (WFSM.event_input_messages tr.SM.tr_event == [wire]);
              assert (ES.server_step #CTy.server_local_event st0 (SM.WireEvent wire) s' tr.SM.tr_output);
              eliminate exists (m:CW.wire_message).
                L.memP m (WFSM.event_input_messages tr.SM.tr_event) /\
                m.CW.wm_content_type == T.Application_data
              returns False
              with _.
                (assert (L.memP m [wire]);
                 assert (m == wire);
                 lemma_server_step_recv_appdata_post_cf st0 wire s' tr.SM.tr_output))
         | SM.LocalEvent _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** SERVER INVERSION — a reachable server whose received byte log contains an
    ApplicationData-typed record is at or after receipt of the client Finished. **)
let lemma_server_received_appdata_record_implies_post_cf
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            raw_has_appdata_record server.CS.cs_wire_log.CL.raw_received /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures server_post_cf_ctrl server.CS.cs_model.CS.model_control)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns server_post_cf_ctrl server.CS.cs_model.CS.model_control
    with _.
    (
      lemma_server_trace_appdata_post_cf init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      Seq.lemma_eq_elim server.CS.cs_wire_log.CL.raw_received sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      eliminate exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received msgs Seq.empty /\
        list_has_appdata msgs
      returns server_post_cf_ctrl server.CS.cs_model.CS.model_control
      with _.
        lemma_parses_as_functional server.CS.cs_wire_log.CL.raw_received msgs in_msgs
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    CLIENT-side inversion — a ready client has SENT an ApplicationData record.
    ───────────────────────────────────────────────────────────────────────── **)

(** The client control that guarantees the protected Finished has been sent. **)
let client_at_appdata (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData -> true
  | _ -> false

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
(** A RECEIVED event never moves a client from a non-application control into the
    application-data control (that transition is the client SENDING its Finished,
    a local send event). **)
let lemma_client_recv_not_into_appdata
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (SMKM.received_tls_event msg) /\
            CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            ~(client_at_appdata m.CS.model_control))
          (ensures ~(client_at_appdata m'.CS.model_control))
  = ()

(** A protected-handshake receipt never moves the client into the
    application-data control: that control is entered only by SENDING the
    protected Finished. **)
let lemma_client_protected_not_into_appdata
  (m:CS.connection_model) (step:CS.protected_handshake_step) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (CS.ConnProtectedHandshake step) /\
            CS.step_model m (CS.ConnProtectedHandshake step) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            ~(client_at_appdata m.CS.model_control))
          (ensures ~(client_at_appdata m'.CS.model_control))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
(** The ONLY legal client-role event that moves control into the application-data
    control from outside it is sending the protected Finished — a non-cleartext,
    single-record Sent event.  Hence its raw byte delta is exactly one
    ApplicationData record. **)
let lemma_client_into_appdata_raw_sent_appdata
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent:B.bytes)
  : Lemma (requires
            CS.legal_event m conn_ev /\
            CS.step_model m conn_ev == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            ~(client_at_appdata m.CS.model_control) /\
            client_at_appdata m'.CS.model_control /\
            CS.event_raw_delta_legal m conn_ev raw_sent B.empty)
          (ensures CS.raw_records_exactly raw_sent T.Application_data 1)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** Client-step config immutability, lifted from `step_model` to `client_step`. **)
let lemma_client_step_preserves_config
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires EC.client_step st0 ev st1 out)
          (ensures st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
      with _.
        (         lemma_step_model_preserves_config st0.CS.cs_model conn_ev st1.CS.cs_model)
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
      with _.
        lemma_step_model_preserves_config st0.CS.cs_model conn_ev st1.CS.cs_model
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(** CLIENT crux — a client step that ENTERS the application-data control emits an
    ApplicationData-typed wire record (the protected Finished). **)
let lemma_client_step_into_appdata_emits
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            EC.client_step st0 ev st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            ~(client_at_appdata st0.CS.cs_model.CS.model_control) /\
            client_at_appdata st1.CS.cs_model.CS.model_control)
          (ensures list_has_appdata out.SM.so_wire_outputs)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns list_has_appdata out.SM.so_wire_outputs
      with _.
        (match conn_ev with
         | CS.ConnLocalEvent _ -> ()
         | CS.ConnNetworkEvent dm ->
           lemma_client_recv_not_into_appdata
             st0.CS.cs_model dm.CL.message_value st1.CS.cs_model
         | CS.ConnProtectedHandshake step ->
           lemma_client_protected_not_into_appdata
             st0.CS.cs_model step st1.CS.cs_model)
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns list_has_appdata out.SM.so_wire_outputs
      with _.
      (
        lemma_client_into_appdata_raw_sent_appdata
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent;
        CSL.lemma_raw_records_exactly_one_parse_record raw_sent T.Application_data;
        W.lemma_parse_record_implies_parse_record_wire raw_sent;
        Seq.lemma_eq_elim raw_sent
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs);
        PNTWL.lemma_wire_parse_serialize_all_inverse out.SM.so_wire_outputs;
        lemma_first_record_appdata raw_sent out.SM.so_wire_outputs
      )
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
(** Client trace induction: from a client-role start state, along any reachability
    trace, the config is preserved and EITHER the trace already emitted an
    ApplicationData record, OR the endpoint is not (yet) at the application-data
    control, OR it started there. **)
let rec lemma_client_trace_emits_appdata
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
          (ensures
            st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
            (list_has_appdata (SM.trace_wire_outputs trace) \/
             ~(client_at_appdata st1.CS.cs_model.CS.model_control) \/
             client_at_appdata st0.CS.cs_model.CS.model_control))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_emits_appdata init s' st1 rest;
      lemma_list_has_appdata_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest);
      introduce
        (~(client_at_appdata st0.CS.cs_model.CS.model_control) /\
         client_at_appdata s'.CS.cs_model.CS.model_control) ==>
          list_has_appdata tr.SM.tr_output.SM.so_wire_outputs
      with _.
        lemma_client_step_into_appdata_emits st0 tr.SM.tr_event s' tr.SM.tr_output
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** CLIENT INVERSION — a reachable client at the application-data control has SENT
    an ApplicationData-typed record on its outgoing byte log. **)
let lemma_client_ready_sent_has_appdata_record
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_has_appdata_record client.CS.cs_wire_log.CL.raw_sent)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_has_appdata_record client.CS.cs_wire_log.CL.raw_sent
    with _.
    (
      lemma_client_trace_emits_appdata init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent sm_bytes);
      Seq.lemma_eq_elim client.CS.cs_wire_log.CL.raw_sent sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse out_msgs
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PART 3 — single-endpoint APPLICATION-DATA COUNT BOUNDS.

    Four count-bound lemmas relating a reachable endpoint's control to the
    number of ApplicationData-typed wire records on its raw byte logs, proved by
    trace induction with control/marker potentials.
    ───────────────────────────────────────────────────────────────────────── **)

(** UNIVERSAL single-record count bridge: a raw byte log whose FIRST record
    parse consumes the WHOLE log with content type `ct` has appdata-count equal
    to `1` iff `ct` is ApplicationData, else `0`. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20 --split_queries always"
let lemma_single_full_record_count (raw:B.bytes) (ct:T.content_type)
  : Lemma
      (requires
        (exists (frag:M.sealed_record).
          W.parse_record_wire raw == Some (ct, frag, B.length raw)))
      (ensures
        raw_appdata_count raw == (if ct = T.Application_data then 1 else 0))
  = eliminate exists (frag:M.sealed_record).
      W.parse_record_wire raw == Some (ct, frag, B.length raw)
    returns raw_appdata_count raw == (if ct = T.Application_data then 1 else 0)
    with _.
    (
      W.lemma_parse_record_wire_some_consumed_positive raw ct frag (B.length raw);
      // wire_parse raw reduces to Some(m, after) with m.wm_content_type == ct.
      W.lemma_parse_record_wire_fragment_bound raw;
      let after = Seq.slice raw (B.length raw) (B.length raw) in
      Seq.lemma_eq_elim after B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal after B.empty
    )
#pop-options

(** `list_appdata_count` distributes over append. **)
let rec lemma_list_appdata_count_append (a b:list CW.wire_message)
  : Lemma
      (ensures list_appdata_count (L.append a b)
                 == list_appdata_count a + list_appdata_count b)
      (decreases a)
  = match a with
    | [] -> ()
    | _ :: rest -> lemma_list_appdata_count_append rest b

(** A single wire message's appdata count equals the appdata count of its
    serialized byte log. **)
let lemma_list_appdata_count_single_wire (w:CW.wire_message)
  : Lemma
      (ensures list_appdata_count [w] == raw_appdata_count (CW.wire_serialize w))
  = lemma_serialize_all_single_wire w;
    lemma_raw_appdata_count_serialize_all [w];
    lemma_raw_appdata_count_seq_equal
      (WF.serialize_all CW.tls_record_wire_format [w])
      (CW.wire_serialize w)

(** A single wire record contributes at most one ApplicationData record. **)
#push-options "--fuel 2 --ifuel 2"
let lemma_list_appdata_count_singleton (w:CW.wire_message)
  : Lemma (ensures list_appdata_count [w] <= 1)
  = ()
#pop-options

(** Local pre-application-data control predicate (matches
    `TLS13.System.ProgressCount.pre_appdata_control`): FALSE exactly at the
    application-data / closing / closed / failed controls. **)
let pre_appdata_ctrl (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> false
  | _ -> true

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
(** FORWARD-CLOSURE (model level): once out of the pre-application-data region, a
    legal step never returns to it. **)
let lemma_step_notpreappdata_stable
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            ~(pre_appdata_ctrl m.CS.model_control))
          (ensures ~(pre_appdata_ctrl m'.CS.model_control))
  = ()
#pop-options

(** A pure model step underlies any official endpoint step. **)
let model_stepped (m m':CS.connection_model) : prop =
  exists (conn_ev:CS.conn_event).
    CS.legal_event m conn_ev /\ CS.step_model m conn_ev == Some m'

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** Extract the underlying legal model step from a server step. **)
let lemma_server_step_model_stepped
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires ES.server_step st0 ev st1 out)
          (ensures model_stepped st0.CS.cs_model st1.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns model_stepped st0.CS.cs_model st1.CS.cs_model
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        introduce exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some st1.CS.cs_model
        with conn_ev and ()
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns model_stepped st0.CS.cs_model st1.CS.cs_model
      with _.
      (
        introduce exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some st1.CS.cs_model
        with conn_ev and ()
      )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** Extract the underlying legal model step from a client step. **)
let lemma_client_step_model_stepped
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires EC.client_step st0 ev st1 out)
          (ensures model_stepped st0.CS.cs_model st1.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns model_stepped st0.CS.cs_model st1.CS.cs_model
      with _.
      (
        introduce exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some st1.CS.cs_model
        with conn_ev and ()
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns model_stepped st0.CS.cs_model st1.CS.cs_model
      with _.
      (
        introduce exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some st1.CS.cs_model
        with conn_ev and ()
      )
#pop-options

(** A cleartext ServerHello / HelloRetryRequest / ChangeCipherSpec record has
    appdata-count 0: its outer content type is Handshake or ChangeCipherSpec,
    never ApplicationData.  (These are the only cleartext records a reachable
    server sends or a reachable client receives.) **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30 --split_queries always"
let lemma_cleartext_raw_count_zero (msg:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        ((M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) \/
         msg == M.TlsHandshake M.HelloRetryRequest \/
         msg == M.TlsChangeCipherSpec) /\
        (forall (sh:GSH.serverHello).
           msg == M.TlsHandshake (M.ServerHello sh) ==>
           B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640) /\
        CS.cleartext_tls_message_raw msg raw)
      (ensures raw_appdata_count raw == 0)
  = match msg with
    | M.TlsHandshake (M.ServerHello sh) ->
      lemma_cleartext_server_hello_parse_record sh raw;
      lemma_single_full_record_count raw T.Handshake
    | M.TlsHandshake M.HelloRetryRequest ->
      CSL.lemma_raw_records_exactly_one_parse_record raw T.Handshake;
      W.lemma_parse_record_implies_parse_record_wire raw;
      lemma_single_full_record_count raw T.Handshake
    | M.TlsChangeCipherSpec ->
      W.lemma_serialize_tls_message_change_cipher_spec ();
      WFL.lemma_parse_record_wire_serialize_record T.Change_cipher_spec (B.singleton 1uy);
      Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message msg);
      lemma_single_full_record_count raw T.Change_cipher_spec
#pop-options

(** A single protected ApplicationData record has appdata-count 1. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20 --split_queries always"
let lemma_protected_raw_count_one (raw:B.bytes)
  : Lemma
      (requires CS.raw_records_exactly raw T.Application_data 1)
      (ensures raw_appdata_count raw == 1)
  = CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data;
    W.lemma_parse_record_implies_parse_record_wire raw;
    lemma_single_full_record_count raw T.Application_data
#pop-options

(** ── SERVER SENT ≤ 4 : write-once protected-flight markers. ──────────────── **)

(** The number of the four server protected-flight fields that are set. **)
let server_sent_marker_count (m:CS.connection_model) : nat =
  let hs = m.CS.model_handshake in
  (if Some? hs.CS.hs_encrypted_extensions then 1 else 0) +
  (if Some? hs.CS.hs_certificate then 1 else 0) +
  (if hs.CS.hs_certificate_verify_verified then 1 else 0) +
  (if Some? hs.CS.hs_server_finished then 1 else 0)

(** Server controls strictly before the server has sent EncryptedExtensions. **)
let server_pre_flight_ctrl (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent -> true
  | _ -> false

(** Write-once shape: the four flight fields are all unset before the flight
    begins, and `hs_server_finished` stays unset until the ServerFinished send. **)
let server_flight_shape (m:CS.connection_model) : prop =
  let hs = m.CS.model_handshake in
  (server_pre_flight_ctrl m.CS.model_control ==>
     (hs.CS.hs_encrypted_extensions == None /\
      hs.CS.hs_certificate == None /\
      hs.CS.hs_certificate_verify_verified == false /\
      hs.CS.hs_server_finished == None)) /\
  (m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent ==>
     hs.CS.hs_server_finished == None)

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step server SEND marker fact: within the pre-application-data region, a
    legal server step preserves the write-once shape and its appdata SENT-delta
    count is bounded by the marker increase (each protected flight send flips
    exactly one fresh marker). **)
let lemma_server_marker_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok m.CS.model_control /\
        pre_appdata_ctrl m.CS.model_control /\
        pre_appdata_ctrl m'.CS.model_control /\
        server_flight_shape m /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        server_flight_shape m' /\
        server_sent_marker_count m + raw_appdata_count raw_sent
          <= server_sent_marker_count m')
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnProtectedHandshake _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_sent B.empty
       | CL.Sent ->
         if CS.network_message_is_cleartext CL.Sent dm.CL.message_value
         then
           (match dm.CL.message_value with
            | M.TlsHandshake (M.ServerHello _) ->
              lemma_cleartext_raw_count_zero dm.CL.message_value raw_sent
            | M.TlsChangeCipherSpec ->
              lemma_cleartext_raw_count_zero dm.CL.message_value raw_sent
            | _ -> ())
         else
           (assert (CS.protected_record_count CL.Sent dm.CL.message_value == 1);
            lemma_protected_raw_count_one raw_sent))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Server-step SEND marker fact, lifted to `server_step`: the wire-output
    appdata count of a step is bounded by the marker increase, and the write-once
    shape is preserved (within the pre-application-data region). **)
let lemma_server_step_sent_marker
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok st0.CS.cs_model.CS.model_control /\
        pre_appdata_ctrl st0.CS.cs_model.CS.model_control /\
        pre_appdata_ctrl st1.CS.cs_model.CS.model_control /\
        server_flight_shape st0.CS.cs_model)
      (ensures
        server_flight_shape st1.CS.cs_model /\
        server_sent_marker_count st0.CS.cs_model
          + list_appdata_count out.SM.so_wire_outputs
          <= server_sent_marker_count st1.CS.cs_model)
  = lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (server_flight_shape st1.CS.cs_model /\
         server_sent_marker_count st0.CS.cs_model
           + list_appdata_count out.SM.so_wire_outputs
           <= server_sent_marker_count st1.CS.cs_model)
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_server_marker_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (server_flight_shape st1.CS.cs_model /\
         server_sent_marker_count st0.CS.cs_model
           + list_appdata_count out.SM.so_wire_outputs
           <= server_sent_marker_count st1.CS.cs_model)
      with _.
      (
        lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          raw_sent;
        lemma_server_marker_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
      )
#pop-options

(** ── SERVER SENT ≤ 4 : trace-level forward closure + marker induction. ────── **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** `~pre_appdata` is forward-closed along a reachable server trace. **)
let rec lemma_server_trace_notpreappdata_forward
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            ~(pre_appdata_ctrl st0.CS.cs_model.CS.model_control))
          (ensures ~(pre_appdata_ctrl st1.CS.cs_model.CS.model_control))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (conn_ev:CS.conn_event).
        CS.legal_event st0.CS.cs_model conn_ev /\
        CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model
      returns ~(pre_appdata_ctrl s'.CS.cs_model.CS.model_control)
      with _.
        lemma_step_notpreappdata_stable st0.CS.cs_model conn_ev s'.CS.cs_model;
      lemma_server_trace_notpreappdata_forward init s' st1 rest
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level SEND marker telescoping: along any reachable server trace whose
    endpoint is still in the pre-application-data region, the total appdata SENT
    output count plus the initial marker count is bounded by the final marker
    count.  (All intermediate states are pre-application-data by forward
    closure, so `lemma_server_step_sent_marker` applies at every step.) **)
let rec lemma_server_trace_sent_marker
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control /\
            pre_appdata_ctrl st1.CS.cs_model.CS.model_control /\
            server_flight_shape st0.CS.cs_model)
          (ensures
            server_flight_shape st1.CS.cs_model /\
            server_sent_marker_count st0.CS.cs_model
              + list_appdata_count (SM.trace_wire_outputs trace)
              <= server_sent_marker_count st1.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      (* s' is pre_appdata: else st1 would be ~pre_appdata by forward closure. *)
      introduce ~(pre_appdata_ctrl s'.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_server_trace_notpreappdata_forward init s' st1 rest;
      lemma_server_step_sent_marker st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_sent_marker init s' st1 rest;
      lemma_list_appdata_count_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA 2 : SERVER SENT ≤ 4 in the pre-application-data region. ═══
    A reachable server that has not yet reached application data has SENT at most
    four ApplicationData-typed protected records (EncryptedExtensions,
    Certificate, CertificateVerify, ServerFinished). **)
let lemma_server_preappdata_sent_le4
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            pre_appdata_ctrl server.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_sent <= 4)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_sent <= 4
    with _.
    (
      lemma_server_trace_sent_marker init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    CLIENT SENT == 0 : a reachable client that has not yet reached application
    data has SENT ZERO ApplicationData-typed records.  It has only sent the
    cleartext ClientHello (which, under `supported_client_config_wire_profile`,
    serializes to a single non-wrapping cleartext record) and possibly a
    cleartext ChangeCipherSpec.  The first ApplicationData record a client sends
    is its protected Finished, whose send is exactly the transition INTO
    ControlApplicationData (hence excluded here).
    ═══════════════════════════════════════════════════════════════════════════ **)

(** The record-parse image of a cleartext ClientHello raw byte string equals its
    canonical handshake serialization — provided the supported wire profile,
    which (via `lemma_serialize_handshake_client_hello_record_bound`) bounds the
    ClientHello handshake fragment so it fits a single non-wrapping record. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_cleartext_client_hello_parse_record
  (ch:GCH.clientHello) (raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw)
      (ensures
        W.parse_record_wire raw ==
          Some (T.Handshake, W.serialize_handshake (M.ClientHello ch), B.length raw))
=
  let fragment = W.serialize_handshake (M.ClientHello ch) in
  WFL.lemma_serialize_handshake_client_hello_record_bound ch;
  W.lemma_serialize_tls_message_handshake (M.ClientHello ch);
  WFL.lemma_parse_record_wire_serialize_record T.Handshake fragment;
  assert (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch)) ==
          W.serialize_record T.Handshake fragment);
  assert (Seq.equal raw (W.serialize_record T.Handshake fragment));
  Seq.lemma_eq_elim raw (W.serialize_record T.Handshake fragment)
#pop-options

(** A cleartext (supported-profile) ClientHello record has appdata-count 0: its
    outer content type is Handshake, never ApplicationData. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20 --split_queries always"
let lemma_cleartext_client_hello_raw_count_zero (ch:GCH.clientHello) (raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw)
      (ensures raw_appdata_count raw == 0)
  = lemma_cleartext_client_hello_parse_record ch raw;
    lemma_single_full_record_count raw T.Handshake
#pop-options

(** Client start/config coherence: whenever a client model has stored its
    handshake-start parameters, they match the (immutable) config.  Set exactly
    at `LocalStartHandshake` whose legality forces `start_matches_config`, and
    preserved elsewhere (config is immutable). **)
let client_start_shape (m:CS.connection_model) : prop = WSS.client_start_shape m

(** A single legal step preserves `client_start_shape`. **)
let lemma_step_model_preserves_client_start_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\ CS.step_model m ev == Some m' /\ client_start_shape m)
      (ensures client_start_shape m')
  = WSS.lemma_step_model_preserves_client_start_shape m ev m'

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** A client that STAYS pre-application-data can only have SENT a cleartext
    message (ClientHello or ChangeCipherSpec).  The only protected Sent message a
    client emits before application data is its Finished, whose send transitions
    control INTO ControlApplicationData (so `m'` would not be pre-appdata); all
    other protected Sent messages are legal only at ControlApplicationData (so
    `m` would not be pre-appdata) or move to a terminal control. **)
let lemma_client_preappdata_sent_cleartext
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (SMKM.sent_tls_event msg) /\
            CS.step_model m (SMKM.sent_tls_event msg) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            pre_appdata_ctrl m.CS.model_control /\
            pre_appdata_ctrl m'.CS.model_control)
          (ensures CS.network_message_is_cleartext CL.Sent msg == true)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step client SEND count fact: within the pre-application-data region, a
    legal client step (whose config is a supported client wire profile and whose
    start parameters match that config) preserves `client_start_shape` and emits
    ZERO ApplicationData-typed bytes on its SENT delta.  A cleartext ClientHello
    send serializes to a single non-wrapping cleartext (Handshake) record and a
    cleartext ChangeCipherSpec to a single ChangeCipherSpec record — both
    appdata-count 0; any protected Sent message is ruled out by
    `lemma_client_preappdata_sent_cleartext`. **)
let lemma_client_marker_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WFL.supported_client_config_wire_profile m.CS.model_config /\
        client_start_shape m /\
        pre_appdata_ctrl m.CS.model_control /\
        pre_appdata_ctrl m'.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        client_start_shape m' /\ raw_appdata_count raw_sent == 0)
  = lemma_step_model_preserves_client_start_shape m conn_ev m';
    match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnProtectedHandshake _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnNetworkEvent dm ->
      let msg = dm.CL.message_value in
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_sent B.empty
       | CL.Sent ->
         assert (conn_ev == SMKM.sent_tls_event msg);
         if CS.network_message_is_cleartext CL.Sent msg
         then
           (match msg with
            | M.TlsHandshake (M.ClientHello ch) ->
              (match m.CS.model_handshake.CS.hs_start with
               | Some start ->
                 lemma_ch_profile_from_start_config m.CS.model_config start ch;
                 lemma_cleartext_client_hello_raw_count_zero ch raw_sent
               | None -> ())
            | M.TlsHandshake (M.ServerHello _) ->
              lemma_cleartext_raw_count_zero msg raw_sent
            | M.TlsChangeCipherSpec ->
              lemma_cleartext_raw_count_zero msg raw_sent
            | _ -> ())
         else
           lemma_client_preappdata_sent_cleartext m msg m')
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Client-step SEND count fact, lifted to `client_step`: the wire-output appdata
    count of a pre-application-data client step is 0, and `client_start_shape` is
    preserved. **)
let lemma_client_step_sent_zero
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WFL.supported_client_config_wire_profile st0.CS.cs_model.CS.model_config /\
        client_start_shape st0.CS.cs_model /\
        pre_appdata_ctrl st0.CS.cs_model.CS.model_control /\
        pre_appdata_ctrl st1.CS.cs_model.CS.model_control)
      (ensures
        client_start_shape st1.CS.cs_model /\
        list_appdata_count out.SM.so_wire_outputs == 0)
  = lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (client_start_shape st1.CS.cs_model /\
         list_appdata_count out.SM.so_wire_outputs == 0)
      with _.
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_client_marker_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (client_start_shape st1.CS.cs_model /\
         list_appdata_count out.SM.so_wire_outputs == 0)
      with _.
      (
        lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          raw_sent;
        lemma_client_marker_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
      )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** `~pre_appdata` is forward-closed along a reachable client trace. **)
let rec lemma_client_trace_notpreappdata_forward
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            ~(pre_appdata_ctrl st0.CS.cs_model.CS.model_control))
          (ensures ~(pre_appdata_ctrl st1.CS.cs_model.CS.model_control))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (conn_ev:CS.conn_event).
        CS.legal_event st0.CS.cs_model conn_ev /\
        CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model
      returns ~(pre_appdata_ctrl s'.CS.cs_model.CS.model_control)
      with _.
        lemma_step_notpreappdata_stable st0.CS.cs_model conn_ev s'.CS.cs_model;
      lemma_client_trace_notpreappdata_forward init s' st1 rest
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level SEND count telescoping: along any reachable client trace whose
    endpoint is still in the pre-application-data region, the total appdata SENT
    output count is 0 and `client_start_shape` is preserved.  (All intermediate
    states are pre-application-data by forward closure, so
    `lemma_client_step_sent_zero` applies at every step; config immutability
    threads the supported wire profile through the trace.) **)
let rec lemma_client_trace_sent_zero
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            WFL.supported_client_config_wire_profile st0.CS.cs_model.CS.model_config /\
            client_start_shape st0.CS.cs_model /\
            pre_appdata_ctrl st1.CS.cs_model.CS.model_control)
          (ensures
            client_start_shape st1.CS.cs_model /\
            list_appdata_count (SM.trace_wire_outputs trace) == 0)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      (* st0 is pre_appdata: else st1 would be ~pre_appdata by forward closure. *)
      introduce ~(pre_appdata_ctrl st0.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_client_trace_notpreappdata_forward init st0 st1 trace;
      (* s' is pre_appdata: else st1 would be ~pre_appdata by forward closure. *)
      introduce ~(pre_appdata_ctrl s'.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_client_trace_notpreappdata_forward init s' st1 rest;
      lemma_client_step_sent_zero st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_sent_zero init s' st1 rest;
      lemma_list_appdata_count_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA : CLIENT SENT == 0 in the pre-application-data region. ═══
    A reachable client with a SUPPORTED (bounded) config wire profile that has
    not yet reached application data has SENT ZERO ApplicationData-typed records:
    it has only sent the cleartext ClientHello (a single non-wrapping cleartext
    record under `supported_client_config_wire_profile`) and possibly a cleartext
    ChangeCipherSpec.  The first ApplicationData record a client sends is its
    protected Finished, whose send is exactly the transition INTO
    ControlApplicationData. **)
let lemma_client_preappdata_sent_no_appdata
  (cfg:CS.connection_config) (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            pre_appdata_ctrl client.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ClientEndpoint /\
            WFL.supported_client_config_wire_profile cfg)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_sent == 0)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_sent == 0
    with _.
    (
      lemma_client_trace_sent_zero init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

(** ── SERVER RECV ≤ 1 : post-CF potential. ──────────────────────────────────
    The server RECEIVES an ApplicationData record only once — the client
    Finished — after which it is in the post-CF region where no further receive
    keeps it in the pre-application-data region except a (cleartext, count-0)
    ChangeCipherSpec. **)

(** Post-CF potential: 1 iff the server is at or past receipt of client Finished. **)
let server_recv_prior (m:CS.connection_model) : nat =
  if server_post_cf_ctrl m.CS.model_control then 1 else 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** At a post-CF server control that is still pre-application-data
    (HsClientFinishedReceived / HsClientFinishedVerified), the ONLY legal
    RECEIVED message that keeps the server pre-application-data is a
    ChangeCipherSpec (a cleartext, count-0 record).  Any handshake/appdata
    receive is illegal there, and an Alert leaves the pre-application-data
    region. **)
let lemma_server_recv_postcf_preappdata_is_ccs
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (SMKM.received_tls_event msg) /\
            CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_post_cf_ctrl m.CS.model_control /\
            pre_appdata_ctrl m.CS.model_control /\
            pre_appdata_ctrl m'.CS.model_control)
          (ensures msg == M.TlsChangeCipherSpec)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 50 --split_queries always"
(** Per-step server RECV potential fact: within the pre-application-data region, a
    legal server step's appdata RECV-input count plus the pre-step post-CF
    potential is bounded by the post-step potential.  (An ApplicationData receive
    lands in the post-CF region and can only happen from the ~post-CF side, since
    a post-CF receive keeping pre-application-data must be a count-0
    ChangeCipherSpec.) **)
let lemma_server_step_recv_potential
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok st0.CS.cs_model.CS.model_control /\
        pre_appdata_ctrl st0.CS.cs_model.CS.model_control /\
        pre_appdata_ctrl st1.CS.cs_model.CS.model_control)
      (ensures
        list_appdata_count (WFSM.event_input_messages ev)
          + server_recv_prior st0.CS.cs_model
          <= server_recv_prior st1.CS.cs_model)
  = lemma_server_step_model_facts st0 ev st1 out;
    match ev with
    | SM.LocalEvent _ -> ()
    | SM.WireEvent wire ->
      if wire.CW.wm_content_type = T.Application_data
      then
        (lemma_server_step_recv_appdata_post_cf st0 wire st1 out;
         (* Show ~post_cf(st0): otherwise the receive would be a CCS whose wire
            content type is not ApplicationData, contradicting `wire` appdata. *)
         if server_post_cf_ctrl st0.CS.cs_model.CS.model_control
         then
           eliminate exists (msg:M.tls_message).
             (let conn_ev =
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = msg;
                } in
              CS.legal_connection_delta
                st0
                {
                  CS.delta_event = conn_ev;
                  CS.delta_raw_sent =
                    WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
                  CS.delta_raw_received = CW.wire_serialize wire;
                }
                st1 /\
              SMCan.sent_event_nonempty_seal_projection
                st0.CS.cs_model conn_ev
                (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
              SMCan.received_event_nonempty_decode_projection
                st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
              ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
           returns False
           with _.
           (
             let raw = CW.wire_serialize wire in
             assert (raw == wire.CW.wm_raw);
             assert (W.parse_record_wire raw ==
                     Some (wire.CW.wm_content_type, wire.CW.wm_fragment, B.length raw));
             lemma_server_recv_postcf_preappdata_is_ccs
               st0.CS.cs_model msg st1.CS.cs_model;
             lemma_cleartext_recv_not_appdata st0.CS.cs_model msg raw
           )
         else ())
      else ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level RECV potential telescoping: along any reachable server trace whose
    endpoint is still pre-application-data, the total appdata RECV-input count
    plus the initial post-CF potential is bounded by the final post-CF potential.
    (All intermediate states are pre-application-data by forward closure.) **)
let rec lemma_server_trace_recv_potential
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control /\
            pre_appdata_ctrl st1.CS.cs_model.CS.model_control)
          (ensures
            list_appdata_count (WFSM.trace_input_messages trace)
              + server_recv_prior st0.CS.cs_model
              <= server_recv_prior st1.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      introduce ~(pre_appdata_ctrl s'.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_server_trace_notpreappdata_forward init s' st1 rest;
      lemma_server_step_recv_potential st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_recv_potential init s' st1 rest;
      lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA 1 : SERVER RECV ≤ 1 in the pre-application-data region. ═══
    A reachable server that has not yet reached application data has RECEIVED at
    most one ApplicationData-typed record (the client Finished). **)
let lemma_server_preappdata_recv_le1
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            pre_appdata_ctrl server.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_received <= 1)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_received <= 1
    with _.
    (
      lemma_server_trace_recv_potential init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA 1' : SERVER RECV == 0 at HsServerFinishedSent. ═══
    A reachable server that has just sent its own Finished (control
    `HsServerFinishedSent`) has NOT yet received the client Finished, so it has
    RECEIVED zero ApplicationData-typed records.  This is the tight (==0)
    specialisation of `lemma_server_preappdata_recv_le1`: at `HsServerFinishedSent`
    the post-CF receive potential `server_recv_prior` is 0 (it is a pre-CF stage),
    so the same trace-potential telescoping pins the received count to 0. **)
let lemma_server_finished_sent_recv_eq0
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            server.CS.cs_model.CS.model_control
              == CS.ControlHandshaking CS.HsServerFinishedSent /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0
    with _.
    (
      lemma_server_trace_recv_potential init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes;
      // server_recv_prior(HsServerFinishedSent) == 0 (a pre-CF stage), so the
      // trace-potential bound `count(inputs) + 0 <= 0` forces count == 0.
      assert (server_recv_prior server.CS.cs_model == 0)
    )
#pop-options

(** ── CLIENT RECV ≥ 1 : control-based receive potential. ─────────────────────
    A client advances its handshake control by exactly one stage per received
    protected record (EncryptedExtensions, Certificate, CertificateVerify,
    ServerFinished), each an ApplicationData-typed record. **)

(** A received cleartext record (ServerHello / HelloRetryRequest /
    ChangeCipherSpec / ClientHello) has appdata-count 0. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_received_cleartext_count_zero (msg:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Received msg /\
        (forall (sh:GSH.serverHello).
           msg == M.TlsHandshake (M.ServerHello sh) ==>
           B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640) /\
        CS.received_cleartext_tls_message_raw msg raw)
      (ensures raw_appdata_count raw == 0)
  = match msg with
    | M.TlsHandshake (M.ClientHello _) ->
      eliminate exists (fragment:M.sealed_record).
        W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
        W.parse_tls_message T.Handshake fragment == Some msg
      returns raw_appdata_count raw == 0
      with _.
        lemma_single_full_record_count raw T.Handshake
    | M.TlsHandshake (M.ServerHello _) ->
      lemma_cleartext_raw_count_zero msg raw
    | M.TlsHandshake M.HelloRetryRequest ->
      lemma_cleartext_raw_count_zero msg raw
    | M.TlsChangeCipherSpec ->
      lemma_cleartext_raw_count_zero msg raw
    | _ -> ()
#pop-options

(** Control-based upper charge for protected server-flight messages. **)
let client_recv_potential (c:CS.connection_control_state) : nat =
  match c with
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived -> 1
  | CS.ControlHandshaking CS.HsCertificateReceived -> 2
  | CS.ControlHandshaking CS.HsCertificateValidated -> 2
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived -> 3
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified -> 3
  | CS.ControlHandshaking CS.HsServerFinishedReceived -> 4
  | CS.ControlHandshaking CS.HsServerFinishedVerified -> 4
  | CS.ControlApplicationData -> 4
  | CS.ControlClosing -> 4
  | CS.ControlClosed -> 4
  | _ -> 0

(** Lower-bound potential: pending protected bytes witness a record even before
    the first buffered message is drained; later controls also require one. **)
let client_recv_min_potential (m:CS.connection_model) : nat =
  if 0 < B.length
      m.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes
  then 1
  else
    match m.CS.model_control with
    | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
    | CS.ControlHandshaking CS.HsCertificateReceived
    | CS.ControlHandshaking CS.HsCertificateValidated
    | CS.ControlHandshaking CS.HsCertificateVerifyReceived
    | CS.ControlHandshaking CS.HsCertificateVerifyVerified
    | CS.ControlHandshaking CS.HsServerFinishedReceived
    | CS.ControlHandshaking CS.HsServerFinishedVerified
    | CS.ControlApplicationData
    | CS.ControlClosing
    | CS.ControlClosed -> 1
    | _ -> 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step client RECV potential fact: a legal client model step's appdata
    RECV-delta count plus the pre-step control potential is at least the post-step
    control potential.  (Each unit of potential increase corresponds to a received
    protected ApplicationData record; sends, local events and cleartext receives
    never increase the potential.) **)
let lemma_client_recv_potential_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        raw_appdata_count raw_received + client_recv_min_potential m
          >= client_recv_min_potential m')
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_received B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_received B.empty
    | CS.ConnProtectedHandshake step ->
      if step.CS.protected_handshake_head
      then lemma_protected_raw_count_one raw_received
      else (
        Seq.lemma_eq_elim raw_received B.empty;
        lemma_raw_appdata_count_empty ();
        lemma_raw_appdata_count_seq_equal raw_received B.empty
      )
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         Seq.lemma_eq_elim raw_received B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_received B.empty
       | CL.Received ->
         if CS.network_message_is_cleartext CL.Received dm.CL.message_value
         then lemma_received_cleartext_count_zero dm.CL.message_value raw_received
         else
           (assert (CS.protected_record_count CL.Received dm.CL.message_value == 1);
            lemma_protected_raw_count_one raw_received))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Client-step RECV potential fact, lifted to `client_step`. **)
let lemma_client_step_recv_potential
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_min_potential st0.CS.cs_model
          >= client_recv_min_potential st1.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_min_potential st0.CS.cs_model
          >= client_recv_min_potential st1.CS.cs_model)
      with _.
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_list_appdata_count_single_wire wire;
        lemma_client_recv_potential_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_min_potential st0.CS.cs_model
          >= client_recv_min_potential st1.CS.cs_model)
      with _.
        lemma_client_recv_potential_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level client RECV potential telescoping: along any reachable client
    trace, the total appdata RECV-input count plus the initial control potential
    is at least the final control potential. **)
let rec lemma_client_trace_recv_potential
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
          (ensures
            list_appdata_count (WFSM.trace_input_messages trace)
              + client_recv_min_potential st0.CS.cs_model
              >= client_recv_min_potential st1.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_recv_potential st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_recv_potential init s' st1 rest;
      lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Shared bridge: a reachable client whose control has receive-potential ≥ 1 has
    received at least one ApplicationData-typed record. **)
let lemma_client_recv_potential_ge1_implies_recv_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client_recv_min_potential client.CS.cs_model >= 1 /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_received >= 1)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_received >= 1
    with _.
    (
      lemma_client_trace_recv_potential init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (client_recv_min_potential init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
(** ═══ TARGET LEMMA 4 : CLIENT at HsServerFinishedVerified ⇒ RECV ≥ 1. ═══
    A reachable client that has verified the server Finished has RECEIVED at least
    one ApplicationData-typed record containing some or all of the protected
    server flight. **)
let lemma_client_hs_server_finished_verified_recv_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerFinishedVerified /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_received >= 1)
  = lemma_client_recv_potential_ge1_implies_recv_ge1 cfg client
#pop-options

(** ── CLIENT SENT ≥ 1 : control-based send potential. ────────────────────────
    A client that has reached the application-data region (ControlApplicationData
    / ControlClosing / ControlClosed) has SENT its protected Finished — one
    ApplicationData-typed record.  `ControlFailed` is assigned 0 (a client may
    fail before ever sending its Finished). **)
let client_sent_potential (c:CS.connection_control_state) : nat =
  match c with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed -> 1
  | _ -> 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step client SEND potential fact: a legal client model step's appdata
    SENT-delta count plus the pre-step send potential is at least the post-step
    send potential.  The only send that raises the potential is the protected
    Finished (HsServerFinishedVerified → ControlApplicationData), which is exactly
    one ApplicationData record. **)
let lemma_client_sent_potential_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        raw_appdata_count raw_sent + client_sent_potential m.CS.model_control
          >= client_sent_potential m'.CS.model_control)
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnProtectedHandshake _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_sent B.empty
       | CL.Sent ->
         if CS.network_message_is_cleartext CL.Sent dm.CL.message_value
         then ()
         else
           (match dm.CL.message_value with
            | M.TlsApplicationData _ -> ()
            | _ ->
              assert (CS.protected_record_count CL.Sent dm.CL.message_value == 1);
              lemma_protected_raw_count_one raw_sent))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Client-step SEND potential fact, lifted to `client_step`. **)
let lemma_client_step_sent_potential
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        list_appdata_count out.SM.so_wire_outputs
          + client_sent_potential st0.CS.cs_model.CS.model_control
          >= client_sent_potential st1.CS.cs_model.CS.model_control)
  = lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (list_appdata_count out.SM.so_wire_outputs
          + client_sent_potential st0.CS.cs_model.CS.model_control
          >= client_sent_potential st1.CS.cs_model.CS.model_control)
      with _.
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_client_sent_potential_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (list_appdata_count out.SM.so_wire_outputs
          + client_sent_potential st0.CS.cs_model.CS.model_control
          >= client_sent_potential st1.CS.cs_model.CS.model_control)
      with _.
      (
        lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          raw_sent;
        lemma_client_sent_potential_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
      )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level client SEND potential telescoping. **)
let rec lemma_client_trace_sent_potential
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
          (ensures
            list_appdata_count (SM.trace_wire_outputs trace)
              + client_sent_potential st0.CS.cs_model.CS.model_control
              >= client_sent_potential st1.CS.cs_model.CS.model_control)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_sent_potential st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_sent_potential init s' st1 rest;
      lemma_list_appdata_count_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Shared bridge: a reachable client whose control has send-potential ≥ 1 has
    SENT at least one ApplicationData-typed record. **)
let lemma_client_sent_potential_ge1_implies_sent_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client_sent_potential client.CS.cs_model.CS.model_control >= 1 /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_sent >= 1)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_sent >= 1
    with _.
    (
      lemma_client_trace_sent_potential init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (client_sent_potential init.CS.cs_model.CS.model_control == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** ═══ TARGET LEMMA 3 (corrected) : CLIENT past handshake ⇒ RECV ≥ 1 ∧ SENT ≥ 1.
    ═══
    A reachable client that has genuinely completed its handshake — i.e. is in the
    application-data region proper (ControlApplicationData / ControlClosing /
    ControlClosed) — has RECEIVED at least one ApplicationData-typed record (the
    protected server flight) and SENT at least one (its protected Finished).

    DEVIATION FROM THE LITERAL TASK: the literal precondition `~(pre_appdata
    client.control)` is UNSOUND — it also admits `ControlFailed`, which a client
    can enter at ANY point via a legal `LocalFail` local event (see
    `TLS13.Spec.StateMachine.legal_local_event`, the `LocalFail _, _ -> True`
    case).  The one-step trace `CS.initial cfg --LocalFail--> ControlFailed` is a
    reachable client with `~(pre_appdata ControlFailed)` yet RECV = SENT = 0, so
    `recv >= 1 /\ sent >= 1` is FALSE at `ControlFailed`.  We therefore exclude
    `ControlFailed` (the only other `~pre_appdata` control), which is exactly the
    set of clients that truly reached application data. **)
let lemma_client_postappdata_recv_ge1_sent_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            ~(pre_appdata_ctrl client.CS.cs_model.CS.model_control) /\
            ~(CS.ControlFailed? client.CS.cs_model.CS.model_control) /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures
            raw_appdata_count client.CS.cs_wire_log.CL.raw_received >= 1 /\
            raw_appdata_count client.CS.cs_wire_log.CL.raw_sent >= 1)
  = lemma_client_recv_potential_ge1_implies_recv_ge1 cfg client;
    lemma_client_sent_potential_ge1_implies_sent_ge1 cfg client
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PART 4 — per-step APPLICATION-DATA COUNT deltas at the application-data
    control (used by the System `client_appdata_len_ok` conjunct).

    These are single-endpoint facts: a client that SENDS while at/into the
    application-data control emits ≥ 1 ApplicationData record, and a client that
    RECEIVES while at the application-data control consumes exactly 1
    ApplicationData record.  Plus the two "no local/receive enters application
    data" facts and the reachable-parses witnesses used to split the count over
    an append.
    ───────────────────────────────────────────────────────────────────────── **)

(** `list_has_appdata` gives a POSITIVE appdata count. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let rec lemma_list_has_appdata_count_ge1 (msgs:list CW.wire_message)
  : Lemma (requires list_has_appdata msgs)
          (ensures list_appdata_count msgs >= 1)
          (decreases msgs)
  = match msgs with
    | [] -> ()
    | m :: rest ->
      if m.CW.wm_content_type = T.Application_data then ()
      else begin
        eliminate exists (m0:CW.wire_message).
          L.memP m0 msgs /\ m0.CW.wm_content_type == T.Application_data
        returns list_has_appdata rest
        with _.
          introduce exists (m':CW.wire_message).
            L.memP m' rest /\ m'.CW.wm_content_type == T.Application_data
          with m0 and ();
        lemma_list_has_appdata_count_ge1 rest
      end
#pop-options

(** A wire record serializes to a NON-EMPTY byte log (the record header alone is
    5 bytes; the parse consumes a positive prefix). **)
let lemma_wire_serialize_nonempty (w:CW.wire_message)
  : Lemma (ensures B.length (CW.wire_serialize w) > 0)
  = W.lemma_parse_record_wire_some_consumed_positive
      w.CW.wm_raw w.CW.wm_content_type w.CW.wm_fragment (B.length w.CW.wm_raw)

(** A byte log with EXACTLY ZERO records is empty. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_raw_records_exactly_zero_empty (raw:B.bytes) (outer:T.content_type)
  : Lemma (requires CS.raw_records_exactly raw outer 0)
          (ensures Seq.equal raw B.empty)
  = let parsed = CL.parse_record_prefix raw in
    assert (L.length parsed.CL.values == 0);
    (match parsed.CL.values with | [] -> () | _ :: _ -> ());
    assert (parsed.CL.values == []);
    assert (CL.serialize_tls_records parsed.CL.values == B.empty);
    assert (parsed.CL.consumed == 0);
    Seq.lemma_eq_elim (Seq.slice raw parsed.CL.consumed (B.length raw)) raw;
    Seq.lemma_eq_elim raw B.empty
#pop-options

(** MODEL — a client RECEIVE at the application-data control is never a cleartext
    message (cleartext handshake / CCS records are all illegal at
    `ControlApplicationData`, i.e. `step_model` returns `None`). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_client_recv_at_appdata_not_cleartext
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (CS.ConnNetworkEvent dm) /\
            CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata m.CS.model_control /\
            dm.CL.message_direction == CL.Received)
          (ensures ~(CS.network_message_is_cleartext CL.Received dm.CL.message_value))
  = ()
#pop-options

(** MODEL — a client RECEIVE at the application-data control consumes EXACTLY one
    ApplicationData-typed record. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_client_recv_at_appdata_appdata_record
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message)
  (m':CS.connection_model) (raw_received:B.bytes)
  : Lemma (requires
            CS.legal_event m (CS.ConnNetworkEvent dm) /\
            CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata m.CS.model_control /\
            dm.CL.message_direction == CL.Received /\
            CS.network_message_raw_delta_legal m dm raw_received)
          (ensures CS.raw_records_exactly raw_received T.Application_data 1)
  = lemma_client_recv_at_appdata_not_cleartext m dm m';
    assert (CS.network_message_is_cleartext CL.Received dm.CL.message_value == false);
    assert (CS.protected_record_count CL.Received dm.CL.message_value == 1)
#pop-options

(** MODEL — a client SEND that STAYS at the application-data control is never a
    cleartext message (only `TlsApplicationData` / `TlsKeyUpdate` sends keep the
    client at `ControlApplicationData`, both protected). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_client_send_stay_appdata_not_cleartext
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m (CS.ConnNetworkEvent dm) /\
            CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata m.CS.model_control /\
            client_at_appdata m'.CS.model_control /\
            dm.CL.message_direction == CL.Sent)
          (ensures ~(CS.network_message_is_cleartext CL.Sent dm.CL.message_value))
  = ()
#pop-options

(** Local re-proof of the (un-exported) `raw_records_exactly` first-record fact:
    a POSITIVE record count means the first `parse_record` succeeds with the
    common outer type, consuming a positive prefix.  Mirrors
    `TLS13.ConnectionState.Lemmas.lemma_raw_records_exactly_nonempty_parse_record`
    (which is not in the `.fsti`), over the transparent `ConnectionLog` module. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_ws_raw_records_nonempty_parse_record
  (raw:B.bytes) (outer:T.content_type) (count:nat)
  : Lemma
      (requires CS.raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
  = let parsed = CL.parse_record_prefix raw in
    assert (L.length parsed.CL.values == count);
    assert (CS.all_records_outer_type outer parsed.CL.values);
    match W.parse_record raw with
    | None ->
      assert (B.length raw + 1 > 0);
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    | Some (content_type, fragment, consumed) ->
      W.lemma_parse_record_serializes raw;
      if consumed = 0 || consumed > B.length raw then (
        assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
        assert (parsed.CL.values == []);
        assert False
      ) else (
        let rest = Seq.slice raw consumed (B.length raw) in
        let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
        let record =
          { M.record_outer_type = content_type;
            M.record_fragment = fragment } in
        assert (CL.parse_record_prefix raw ==
          {
            CL.values = record :: tail.CL.values;
            CL.consumed = consumed + tail.CL.consumed;
            CL.residual = tail.CL.residual;
          });
        assert (parsed.CL.values == record :: tail.CL.values);
        assert (CS.all_records_outer_type outer (record :: tail.CL.values));
        assert (content_type == outer)
      )
#pop-options

(** MODEL — a client SEND that STAYS at the application-data control emits a
    byte log whose FIRST record is ApplicationData-typed. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_client_send_stay_appdata_first_record
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message)
  (m':CS.connection_model) (raw_sent:B.bytes)
  : Lemma (requires
            CS.legal_event m (CS.ConnNetworkEvent dm) /\
            CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata m.CS.model_control /\
            client_at_appdata m'.CS.model_control /\
            dm.CL.message_direction == CL.Sent /\
            CS.network_message_raw_delta_legal m dm raw_sent /\
            B.length raw_sent > 0)
          (ensures
            (match W.parse_record_wire raw_sent with
             | Some (ct, _, _) -> ct == T.Application_data
             | None -> False))
  = lemma_client_send_stay_appdata_not_cleartext m dm m';
    assert (CS.network_message_is_cleartext CL.Sent dm.CL.message_value == false);
    let n = CS.protected_record_count CL.Sent dm.CL.message_value in
    assert (CS.raw_records_exactly raw_sent T.Application_data n);
    if n = 0 then begin
      lemma_raw_records_exactly_zero_empty raw_sent T.Application_data;
      assert (Seq.equal raw_sent B.empty);
      assert False
    end;
    assert (n > 0);
    lemma_ws_raw_records_nonempty_parse_record raw_sent T.Application_data n;
    W.lemma_parse_record_implies_parse_record_wire raw_sent
#pop-options

(** MODEL — a client event that STAYS at the application-data control and produces
    a NON-EMPTY sent-delta emits a byte log whose FIRST record is ApplicationData
    (handles every `conn_ev` shape; empty-delta shapes are ruled out by length>0). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_stay_appdata_raw_sent_first_appdata
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent:B.bytes)
  : Lemma (requires
            CS.legal_event m conn_ev /\
            CS.step_model m conn_ev == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata m.CS.model_control /\
            client_at_appdata m'.CS.model_control /\
            CS.event_raw_delta_legal m conn_ev raw_sent B.empty /\
            B.length raw_sent > 0)
          (ensures
            (match W.parse_record_wire raw_sent with
             | Some (ct, _, _) -> ct == T.Application_data
             | None -> False))
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty
    | CS.ConnProtectedHandshake _ ->
      Seq.lemma_eq_elim raw_sent B.empty
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty
       | CL.Sent ->
         lemma_client_send_stay_appdata_first_record m dm m' raw_sent)
#pop-options

(** CLIENT-STEP level — a client SEND (single wire output) that STAYS at the
    application-data control emits ≥ 1 ApplicationData record. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_send_stay_appdata_count_ge1
  (st0:CS.connection_state) (local:CTy.client_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  : Lemma (requires
            EC.client_step st0 (SM.LocalEvent local) st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata st0.CS.cs_model.CS.model_control /\
            client_at_appdata st1.CS.cs_model.CS.model_control /\
            out.SM.so_wire_outputs == [w])
          (ensures
            raw_appdata_count
              (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) >= 1)
  = let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.client_local_event_matches st0 local conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns
      raw_appdata_count
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) >= 1
    with _.
    (
      lemma_wire_serialize_nonempty w;
      lemma_serialize_all_single_wire w;
      // raw_sent == serialize_all [w] (Seq.equal from client_wire_outputs_match).
      Seq.lemma_eq_elim raw_sent
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs);
      assert (B.length raw_sent > 0);
      lemma_client_stay_appdata_raw_sent_first_appdata
        st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent;
      PNTWL.lemma_wire_parse_serialize_all_inverse out.SM.so_wire_outputs;
      lemma_first_record_appdata raw_sent out.SM.so_wire_outputs;
      lemma_list_has_appdata_count_ge1 out.SM.so_wire_outputs;
      lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs
    )
#pop-options

(** CLIENT-STEP level — a client RECEIVE at the application-data control consumes
    EXACTLY one ApplicationData record. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_recv_at_appdata_count1
  (st0:CS.connection_state) (wire:CW.wire_message)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            EC.client_step #CTy.client_local_event st0 (SM.WireEvent wire) st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata st0.CS.cs_model.CS.model_control)
          (ensures raw_appdata_count (CW.wire_serialize wire) == 1)
  = eliminate exists (conn_ev:CS.conn_event).
      (EC.client_wire_received_event st0 wire conn_ev /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent =
             WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns raw_appdata_count (CW.wire_serialize wire) == 1
    with _.
    (
      match conn_ev with
      | CS.ConnLocalEvent _ -> ()
      | CS.ConnNetworkEvent dm ->
        lemma_client_recv_at_appdata_appdata_record
          st0.CS.cs_model dm st1.CS.cs_model (CW.wire_serialize wire);
        lemma_protected_raw_count_one (CW.wire_serialize wire)
      | CS.ConnProtectedHandshake step ->
        // A head protected-handshake step consumes exactly one Application_data
        // record, straight from [event_raw_delta_legal].
        lemma_protected_raw_count_one (CW.wire_serialize wire)
    )
#pop-options

(** MODEL — a step with an EMPTY sent-delta never enters the application-data
    control (the unique entry, the protected Finished send, has a non-empty
    ApplicationData sent-delta). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_client_empty_delta_not_into_appdata
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent:B.bytes)
  : Lemma (requires
            CS.legal_event m conn_ev /\
            CS.step_model m conn_ev == Some m' /\
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            ~(client_at_appdata m.CS.model_control) /\
            CS.event_raw_delta_legal m conn_ev raw_sent B.empty /\
            Seq.equal raw_sent B.empty)
          (ensures ~(client_at_appdata m'.CS.model_control))
  = if client_at_appdata m'.CS.model_control then begin
      lemma_client_into_appdata_raw_sent_appdata m conn_ev m' raw_sent;
      // raw_records_exactly raw_sent ApplicationData 1 with raw_sent empty: impossible.
      lemma_ws_raw_records_nonempty_parse_record raw_sent T.Application_data 1
    end
#pop-options

(** CLIENT-STEP level — a client LOCAL step emitting NO wire output never enters
    the application-data control. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_local_noout_not_into_appdata
  (st0:CS.connection_state) (local:CTy.client_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            EC.client_step st0 (SM.LocalEvent local) st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            out.SM.so_wire_outputs == [] /\
            ~(client_at_appdata st0.CS.cs_model.CS.model_control))
          (ensures ~(client_at_appdata st1.CS.cs_model.CS.model_control))
  = let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.client_local_event_matches st0 local conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns ~(client_at_appdata st1.CS.cs_model.CS.model_control)
    with _.
    (
      lemma_serialize_all_nil_wire ();
      // client_wire_outputs_match: Seq.equal (serialize_all []) raw_sent, so raw_sent empty.
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_client_empty_delta_not_into_appdata st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent
    )
#pop-options

(** CLIENT-STEP level — a client RECEIVE never moves control INTO the
    application-data control from outside it. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_wire_recv_not_into_appdata
  (st0:CS.connection_state) (wire:CW.wire_message)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma (requires
            EC.client_step #CTy.client_local_event st0 (SM.WireEvent wire) st1 out /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_at_appdata st1.CS.cs_model.CS.model_control)
          (ensures client_at_appdata st0.CS.cs_model.CS.model_control)
  = eliminate exists (conn_ev:CS.conn_event).
      (EC.client_wire_received_event st0 wire conn_ev /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent =
             WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns client_at_appdata st0.CS.cs_model.CS.model_control
    with _.
    (
      if client_at_appdata st0.CS.cs_model.CS.model_control then ()
      else
        match conn_ev with
        | CS.ConnLocalEvent _ -> ()
        | CS.ConnNetworkEvent dm ->
          lemma_client_recv_not_into_appdata
            st0.CS.cs_model dm.CL.message_value st1.CS.cs_model
        | CS.ConnProtectedHandshake step ->
          lemma_client_protected_not_into_appdata
            st0.CS.cs_model step st1.CS.cs_model
    )
#pop-options

(** REACHABLE PARSES — a reachable client's outgoing byte log cleanly decomposes
    into a wire-record list (the append witness for `lemma_raw_appdata_count_append`). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_raw_sent_parses
  (cfg:CS.connection_config) (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures
            (exists (msgs:list CW.wire_message).
              WF.parses_as CW.tls_record_wire_format
                client.CS.cs_wire_log.CL.raw_sent msgs Seq.empty))
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns
      (exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          client.CS.cs_wire_log.CL.raw_sent msgs Seq.empty)
    with _.
    (
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent sm_bytes);
      Seq.lemma_eq_elim client.CS.cs_wire_log.CL.raw_sent sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse out_msgs;
      introduce exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          client.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
      with out_msgs and ()
    )
#pop-options

(** REACHABLE PARSES — a reachable client's incoming byte log cleanly decomposes
    into a wire-record list. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_raw_received_parses
  (cfg:CS.connection_config) (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures
            (exists (msgs:list CW.wire_message).
              WF.parses_as CW.tls_record_wire_format
                client.CS.cs_wire_log.CL.raw_received msgs Seq.empty))
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns
      (exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          client.CS.cs_wire_log.CL.raw_received msgs Seq.empty)
    with _.
    (
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_received sm_bytes);
      Seq.lemma_eq_elim client.CS.cs_wire_log.CL.raw_received sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      introduce exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          client.CS.cs_wire_log.CL.raw_received msgs Seq.empty
      with in_msgs and ()
    )
#pop-options

(** REACHABLE PARSES — a reachable server's incoming byte log cleanly decomposes
    into a wire-record list (the append witness for `lemma_raw_appdata_count_append`). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_raw_received_parses
  (cfg:CS.connection_config) (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures
            (exists (msgs:list CW.wire_message).
              WF.parses_as CW.tls_record_wire_format
                server.CS.cs_wire_log.CL.raw_received msgs Seq.empty))
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns
      (exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received msgs Seq.empty)
    with _.
    (
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      Seq.lemma_eq_elim server.CS.cs_wire_log.CL.raw_received sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      introduce exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received msgs Seq.empty
      with in_msgs and ()
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    SERVER at ControlApplicationData ⇒ RECEIVED ≥ 1 ApplicationData record.

    A LOWER-bound RECV potential telescoping (dual to the `recv_le1` cluster).
    ───────────────────────────────────────────────────────────────────────── **)

(** Client-Finished-region potential: 1 iff the server has reached receipt of the
    client Finished AND has not yet moved to Closing/Closed/Failed.  Entering this
    3-set from OUTSIDE requires receiving the client Finished (an ApplicationData
    record); leaving it to Closing/Closed/Failed only DECREASES the potential. **)
let server_cf_region_prior (m:CS.connection_model) : nat =
  match m.CS.model_control with
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData -> 1
  | _ -> 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step server CF-region LOWER fact: a legal server-role step's appdata
    RECV-delta count plus the pre-step CF-region potential is at least the
    post-step CF-region potential.  (Entering the 3-set from outside requires a
    protected ApplicationData receive — the client Finished; sends, local events
    and cleartext receives never raise the potential.) **)
let lemma_server_cf_region_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok m.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        server_cf_region_prior m'
          <= raw_appdata_count raw_received + server_cf_region_prior m)
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_received B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_received B.empty
    | CS.ConnProtectedHandshake step ->
      if step.CS.protected_handshake_head
      then lemma_protected_raw_count_one raw_received
      else (
        Seq.lemma_eq_elim raw_received B.empty;
        lemma_raw_appdata_count_empty ();
        lemma_raw_appdata_count_seq_equal raw_received B.empty
      )
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         Seq.lemma_eq_elim raw_received B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_received B.empty
       | CL.Received ->
         if CS.network_message_is_cleartext CL.Received dm.CL.message_value
         then lemma_received_cleartext_count_zero dm.CL.message_value raw_received
         else
           (assert (CS.protected_record_count CL.Received dm.CL.message_value == 1);
            lemma_protected_raw_count_one raw_received))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Server-step CF-region LOWER fact, lifted to `server_step`. **)
let lemma_server_step_cf_region_lower
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok st0.CS.cs_model.CS.model_control)
      (ensures
        server_cf_region_prior st1.CS.cs_model
          <= list_appdata_count (WFSM.event_input_messages ev)
             + server_cf_region_prior st0.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (server_cf_region_prior st1.CS.cs_model
          <= list_appdata_count (WFSM.event_input_messages ev)
             + server_cf_region_prior st0.CS.cs_model)
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_list_appdata_count_single_wire wire;
        lemma_server_cf_region_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (server_cf_region_prior st1.CS.cs_model
          <= list_appdata_count (WFSM.event_input_messages ev)
             + server_cf_region_prior st0.CS.cs_model)
      with _.
        lemma_server_cf_region_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level server CF-region LOWER telescoping: along ANY reachable
    server-role trace whose start state is `server_ctrl_ok`, the total appdata
    RECV-input count plus the initial CF-region potential is at least the final
    CF-region potential.  (No forward-closure hypothesis is needed — only
    `server_ctrl_ok` preservation, via `lemma_server_step_model_facts`.) **)
let rec lemma_server_trace_cf_region_lower
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control)
          (ensures
            server_cf_region_prior st1.CS.cs_model
              <= list_appdata_count (WFSM.trace_input_messages trace)
                 + server_cf_region_prior st0.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_cf_region_lower st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_cf_region_lower init s' st1 rest;
      lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ SERVER at ControlApplicationData ⇒ RECEIVED ≥ 1 ApplicationData record.
    A reachable server that has reached application data has RECEIVED at least one
    ApplicationData-typed record (the client's protected Finished). **)
let lemma_server_appdata_received_appdata
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            server.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_received >= 1)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_received >= 1
    with _.
    (
      lemma_server_trace_cf_region_lower init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Server-side handshake field shape (role-pinned), reachable from `initial`.

    A single legal step keeps this exact control->field characterization; unlike
    the per-endpoint `server_stage_ok` (lower bounds only), the shape carries the
    UPPER bounds plus the `verified ==> cert/cv` coupling at the wide
    `HsServerEncryptedFlightSent` stage, which is exactly what makes it INDUCTIVE.
    Lifting it over the reachability closure gives `server_stage_ok` at every
    reachable (consistent) server state — the fact the `TLS13.System` step-shapes
    need to re-establish the moved `server_stage_ok` invariant conjunct.
    ───────────────────────────────────────────────────────────────────────── **)
let server_stage_shape_m (m:CS.connection_model) : prop =
  let h = m.CS.model_handshake in
  m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  (match m.CS.model_control with
   | CS.ControlNew
   | CS.ControlHandshaking CS.HsAwaitingClientHello ->
     h.CS.hs_client_hello == None /\ h.CS.hs_server_hello == None /\
     h.CS.hs_encrypted_extensions == None /\
     h.CS.hs_certificate == None /\ h.CS.hs_certificate_verify == None /\
     h.CS.hs_certificate_verify_verified == false /\
     h.CS.hs_server_finished == None /\ h.CS.hs_client_finished == None
   | CS.ControlHandshaking CS.HsClientHelloReceived ->
     Some? h.CS.hs_client_hello /\
     h.CS.hs_server_hello == None /\ h.CS.hs_encrypted_extensions == None /\
     h.CS.hs_certificate == None /\ h.CS.hs_certificate_verify == None /\
     h.CS.hs_certificate_verify_verified == false /\
     h.CS.hs_server_finished == None /\ h.CS.hs_client_finished == None
   | CS.ControlHandshaking CS.HsServerHelloSent ->
     Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
     h.CS.hs_encrypted_extensions == None /\
     h.CS.hs_certificate == None /\ h.CS.hs_certificate_verify == None /\
     h.CS.hs_certificate_verify_verified == false /\
     h.CS.hs_server_finished == None /\ h.CS.hs_client_finished == None
   | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
     Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
     Some? h.CS.hs_encrypted_extensions /\
     h.CS.hs_server_finished == None /\ h.CS.hs_client_finished == None /\
     (Some? h.CS.hs_certificate_verify ==> Some? h.CS.hs_certificate) /\
     (h.CS.hs_certificate_verify_verified ==>
        (Some? h.CS.hs_certificate /\ Some? h.CS.hs_certificate_verify))
   | CS.ControlHandshaking CS.HsServerFinishedSent ->
     Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
     Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
     Some? h.CS.hs_certificate_verify /\
     h.CS.hs_certificate_verify_verified == true /\
     Some? h.CS.hs_server_finished /\ h.CS.hs_client_finished == None
   | CS.ControlHandshaking CS.HsClientFinishedReceived
   | CS.ControlHandshaking CS.HsClientFinishedVerified
   | CS.ControlApplicationData ->
     Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
     Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
     Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished /\
     Some? h.CS.hs_client_finished
   | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> True
   | _ -> False)

let server_stage_shape (st:CS.connection_state) : prop =
  server_stage_shape_m st.CS.cs_model

(** A single legal model step preserves the server field shape. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 100"
let lemma_step_model_preserves_server_stage_shape
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m0 ev /\ CS.step_model m0 ev == Some m1 /\
        server_stage_shape_m m0)
      (ensures server_stage_shape_m m1)
  = ()
#pop-options

(** A single legal connection delta preserves the server field shape. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_connection_delta_preserves_server_stage_shape
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_single_step st0 st1 /\ server_stage_shape st0)
      (ensures server_stage_shape st1)
  = assert (exists (delta:CS.connection_delta). CS.legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_model_preserves_server_stage_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

(** The server field shape holds at the initial state of any server config. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_initial_server_stage_shape (cfg:CS.connection_config)
  : Lemma
      (requires cfg.CS.config_role == CS.ServerEndpoint)
      (ensures server_stage_shape (CS.initial cfg))
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_single_step_server_stage_shape (u:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (server_stage_shape y); (SMR.connection_state_single_step x y)}
          server_stage_shape x /\ SMR.connection_state_single_step x y ==>
          server_stage_shape y)
  = introduce forall (x:CS.connection_state) (y:CS.connection_state).
      server_stage_shape x /\ SMR.connection_state_single_step x y ==>
      server_stage_shape y
    with
      introduce _ ==> _ with _.
      lemma_connection_delta_preserves_server_stage_shape x y
#pop-options

(** A consistent (reachable) server-role state satisfies the server field shape,
    hence in particular the `server_stage_ok` lower bounds. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_connection_state_consistent_server_stage_shape (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures server_stage_shape st)
  = let p = server_stage_shape in
    lemma_initial_server_stage_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_server_stage_shape ();
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure
      SMR.connection_state_single_step
      p
      stable;
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st)
#pop-options


(** ═══════════════════════════════════════════════════════════════════════════
    MILESTONE 3 — recv-region / sent-marker / client-finished-flag cross-endpoint
    ORDERING count bounds (re-ported onto the reorganized StateMachine model).
    ═══════════════════════════════════════════════════════════════════════════ **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ SERVER SENT == 0 at HsServerHelloSent. ═══
    A reachable server whose control is exactly `HsServerHelloSent` has SENT ZERO
    ApplicationData-typed records: it has only sent the cleartext ServerHello (and
    possibly a cleartext ChangeCipherSpec) — the protected server flight begins
    with the EncryptedExtensions send, which advances the control OUT of
    `HsServerHelloSent`.  Proof: `server_pre_flight_ctrl HsServerHelloSent` holds,
    so `server_flight_shape` forces all four flight markers unset, hence
    `server_sent_marker_count == 0` upper-bounds the sent count. **)
let lemma_server_hsserverhellosent_sent_zero
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            server.CS.cs_model.CS.model_control
              == CS.ControlHandshaking CS.HsServerHelloSent /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_sent == 0)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_sent == 0
    with _.
    (
      lemma_server_trace_sent_marker init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (server_pre_flight_ctrl server.CS.cs_model.CS.model_control);
      assert (server_sent_marker_count server.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ SERVER RECV == 0 at HsServerHelloSent. ═══
    A reachable server whose control is exactly `HsServerHelloSent` has RECEIVED
    ZERO ApplicationData-typed records: it has only received the cleartext
    ClientHello.  The first (and only) ApplicationData record the server receives
    is the client Finished, which lands in the post-CF region.  Proof:
    `server_recv_prior HsServerHelloSent == 0` (not post-CF), so the RECV potential
    telescoping upper-bounds the received count by 0. **)
let lemma_server_hsserverhellosent_recv_zero
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            server.CS.cs_model.CS.model_control
              == CS.ControlHandshaking CS.HsServerHelloSent /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0
    with _.
    (
      lemma_server_trace_recv_potential init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (server_recv_prior server.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    CLIENT RECV ≤ 3 : upper bound in the server-flight-receiving region.

    A reachable client whose control is still in the handshake-receiving region
    (New / HsStarted / HsClientHelloSent / HsServerHelloReceived /
    HsEncryptedExtensionsReceived / HsCertificateReceived / HsCertificateValidated
    / HsCertificateVerifyReceived / HsCertificateVerifyVerified — every control at
    which the client has NOT yet delivered the server Finished, i.e. its read epoch
    is still Handshake) has RECEIVED at most three ApplicationData-typed records
    (EncryptedExtensions, Certificate, CertificateVerify).  The fourth protected
    record — the server Finished — is delivered ATOMICALLY into
    HsServerFinishedVerified (Model-Fix-1), leaving the region.  We reuse
    `client_recv_potential` (which equals the exact received-record count on this
    region) as an UPPER charge.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** The handshake-receiving region: client controls with read epoch Handshake,
    strictly before the server-Finished delivery, excluding ControlFailed. **)
let client_recv_region_ctrl (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsStarted
  | CS.ControlHandshaking CS.HsClientHelloSent
  | CS.ControlHandshaking CS.HsServerHelloReceived
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified -> true
  | _ -> false

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
(** FORWARD-CLOSURE (model level): once out of the receiving region, a legal step
    never returns.  Every region control is reached ONLY from another region
    control (the region is a strict prefix of the client handshake), so no
    ~region control can step into it. **)
let lemma_step_notregion_stable
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            ~(client_recv_region_ctrl m.CS.model_control))
          (ensures ~(client_recv_region_ctrl m'.CS.model_control))
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** `~(client_recv_region_ctrl)` is forward-closed along a reachable client
    trace. **)
let rec lemma_client_trace_notregion_forward
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            ~(client_recv_region_ctrl st0.CS.cs_model.CS.model_control))
          (ensures ~(client_recv_region_ctrl st1.CS.cs_model.CS.model_control))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (conn_ev:CS.conn_event).
        CS.legal_event st0.CS.cs_model conn_ev /\
        CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model
      returns ~(client_recv_region_ctrl s'.CS.cs_model.CS.model_control)
      with _.
        lemma_step_notregion_stable st0.CS.cs_model conn_ev s'.CS.cs_model;
      lemma_client_trace_notregion_forward init s' st1 rest
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step client RECV UPPER charge: within the receiving region, a legal client
    step's appdata RECV-delta count plus the pre-step control potential is at most
    the post-step control potential.  (Each region-internal protected receive
    advances the control by exactly one `client_recv_potential` unit; local/send
    and cleartext receives leave both unchanged.) **)
let lemma_client_recv_upper_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        client_recv_region_ctrl m.CS.model_control /\
        client_recv_region_ctrl m'.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        raw_appdata_count raw_received + client_recv_potential m.CS.model_control
          <= client_recv_potential m'.CS.model_control)
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_received B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_received B.empty
    | CS.ConnProtectedHandshake step ->
      if step.CS.protected_handshake_head
      then lemma_protected_raw_count_one raw_received
      else (
        Seq.lemma_eq_elim raw_received B.empty;
        lemma_raw_appdata_count_empty ();
        lemma_raw_appdata_count_seq_equal raw_received B.empty
      )
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         Seq.lemma_eq_elim raw_received B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_received B.empty
       | CL.Received ->
         if CS.network_message_is_cleartext CL.Received dm.CL.message_value
         then lemma_received_cleartext_count_zero dm.CL.message_value raw_received
         else
           (assert (CS.protected_record_count CL.Received dm.CL.message_value == 1);
            lemma_protected_raw_count_one raw_received))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Client-step RECV UPPER charge, lifted to `client_step`. **)
let lemma_client_step_recv_upper
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        client_recv_region_ctrl st0.CS.cs_model.CS.model_control /\
        client_recv_region_ctrl st1.CS.cs_model.CS.model_control)
      (ensures
        list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_potential st0.CS.cs_model.CS.model_control
          <= client_recv_potential st1.CS.cs_model.CS.model_control)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_potential st0.CS.cs_model.CS.model_control
          <= client_recv_potential st1.CS.cs_model.CS.model_control)
      with _.
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_list_appdata_count_single_wire wire;
        lemma_client_recv_upper_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_potential st0.CS.cs_model.CS.model_control
          <= client_recv_potential st1.CS.cs_model.CS.model_control)
      with _.
        lemma_client_recv_upper_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level client RECV UPPER telescoping: along any reachable client trace
    whose endpoint is still in the receiving region, the total appdata RECV-input
    count plus the initial control potential is at most the final control
    potential.  (All intermediate states are in the region by forward closure.) **)
let rec lemma_client_trace_recv_upper
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            client_recv_region_ctrl st1.CS.cs_model.CS.model_control)
          (ensures
            list_appdata_count (WFSM.trace_input_messages trace)
              + client_recv_potential st0.CS.cs_model.CS.model_control
              <= client_recv_potential st1.CS.cs_model.CS.model_control)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      (* st0 is in-region: else st1 would be ~region by forward closure. *)
      introduce ~(client_recv_region_ctrl st0.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_client_trace_notregion_forward init st0 st1 trace;
      (* s' is in-region: else st1 would be ~region by forward closure. *)
      introduce ~(client_recv_region_ctrl s'.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_client_trace_notregion_forward init s' st1 rest;
      lemma_client_step_recv_upper st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_recv_upper init s' st1 rest;
      lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA : CLIENT RECV ≤ 3 in the receiving region. ═══
    A reachable client still in the handshake-receiving region has RECEIVED at
    most three ApplicationData-typed records. **)
let lemma_client_reachable_recv_region_le3
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client_recv_region_ctrl client.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_received <= 3)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_received <= 3
    with _.
    (
      lemma_client_trace_recv_upper init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (client_recv_potential init.CS.cs_model.CS.model_control == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ CLIENT RECV == 0 at HsServerHelloReceived. ═══
    A reachable client whose control is exactly `HsServerHelloReceived` has
    RECEIVED ZERO ApplicationData-typed records: it has only received the cleartext
    ServerHello.  The first protected record the client receives is
    EncryptedExtensions, whose receipt advances the control OUT of
    `HsServerHelloReceived`.  `HsServerHelloReceived` is inside the
    `client_recv_region_ctrl` region where `client_recv_potential` is the EXACT
    received-record count; there it equals 0, so the RECV UPPER telescoping bounds
    the received count by 0. **)
let lemma_client_hsserverhelloreceived_recv_zero
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            client.CS.cs_model.CS.model_control
              == CS.ControlHandshaking CS.HsServerHelloReceived /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_received == 0)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_received == 0
    with _.
    (
      assert (client_recv_region_ctrl client.CS.cs_model.CS.model_control);
      lemma_client_trace_recv_upper init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (client_recv_potential init.CS.cs_model.CS.model_control == 0);
      assert (client_recv_potential client.CS.cs_model.CS.model_control == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SERVER SENT ≥ marker : lower bound.  A reachable server has SENT at least
    `server_sent_marker_count` ApplicationData-typed records — one per protected
    flight field that is set (EncryptedExtensions / Certificate / CertificateVerify
    / ServerFinished).  Dual to the `server_sent_marker_count` upper cluster: here
    each set marker is BACKED by (at least) one sent ApplicationData record.  Gated
    on `server_ctrl_ok` (forward-closed), so no client-control receive can flip a
    server marker without a send.
    ═══════════════════════════════════════════════════════════════════════════ **)

#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
(** Per-step server SEND marker LOWER fact: within the server-control region, a
    legal server step's post-step marker count is at most the pre-step marker count
    plus the appdata SENT-delta count (each fresh marker is backed by ≥ 1 sent
    ApplicationData record). **)
let lemma_server_marker_step_lower
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok m.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        server_ctrl_ok m'.CS.model_control /\
        server_sent_marker_count m'
          <= server_sent_marker_count m + raw_appdata_count raw_sent)
  = lemma_server_ctrl_ok_step m conn_ev m';
    match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnProtectedHandshake step ->
      assert_norm (
        CS.legal_event m (CS.ConnProtectedHandshake step) ==
        CS.legal_protected_handshake_step m step);
      assert (m.CS.model_config.CS.config_role == CS.ClientEndpoint);
      assert False
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_sent B.empty
       | CL.Sent ->
         if CS.network_message_is_cleartext CL.Sent dm.CL.message_value
         then
           (match dm.CL.message_value with
            | M.TlsHandshake (M.ServerHello _) ->
              lemma_cleartext_raw_count_zero dm.CL.message_value raw_sent
            | M.TlsChangeCipherSpec ->
              lemma_cleartext_raw_count_zero dm.CL.message_value raw_sent
            | _ -> ())
         else
           (match dm.CL.message_value with
            | M.TlsApplicationData _ ->
              (* An appdata send touches no protected flight field, so the marker
                 count is unchanged; the lower bound holds with any raw count. *)
              ()
            | _ ->
              assert (CS.protected_record_count CL.Sent dm.CL.message_value == 1);
              lemma_protected_raw_count_one raw_sent))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Server-step SEND marker LOWER fact, lifted to `server_step`. **)
let lemma_server_step_sent_marker_lower
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_ctrl_ok st0.CS.cs_model.CS.model_control)
      (ensures
        server_ctrl_ok st1.CS.cs_model.CS.model_control /\
        server_sent_marker_count st1.CS.cs_model
          <= server_sent_marker_count st0.CS.cs_model
             + list_appdata_count out.SM.so_wire_outputs)
  = lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (server_ctrl_ok st1.CS.cs_model.CS.model_control /\
         server_sent_marker_count st1.CS.cs_model
           <= server_sent_marker_count st0.CS.cs_model
              + list_appdata_count out.SM.so_wire_outputs)
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_server_marker_step_lower
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (server_ctrl_ok st1.CS.cs_model.CS.model_control /\
         server_sent_marker_count st1.CS.cs_model
           <= server_sent_marker_count st0.CS.cs_model
              + list_appdata_count out.SM.so_wire_outputs)
      with _.
      (
        lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          raw_sent;
        lemma_server_marker_step_lower
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
      )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level SEND marker LOWER telescoping: along any reachable server trace
    starting in a server control, the final marker count is at most the initial
    marker count plus the total appdata SENT output count.  (server_ctrl_ok is
    forward-closed, so `lemma_server_step_sent_marker_lower` applies at every
    step.) **)
let rec lemma_server_trace_sent_marker_lower
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_ctrl_ok st0.CS.cs_model.CS.model_control)
          (ensures
            server_ctrl_ok st1.CS.cs_model.CS.model_control /\
            server_sent_marker_count st1.CS.cs_model
              <= server_sent_marker_count st0.CS.cs_model
                 + list_appdata_count (SM.trace_wire_outputs trace))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_sent_marker_lower st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_sent_marker_lower init s' st1 rest;
      lemma_list_appdata_count_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA : SERVER SENT ≥ marker. ═══
    A reachable server has SENT at least `server_sent_marker_count` ApplicationData
    records. **)
let lemma_server_reachable_sent_ge_marker
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures
            raw_appdata_count server.CS.cs_wire_log.CL.raw_sent
              >= server_sent_marker_count server.CS.cs_model)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns
      raw_appdata_count server.CS.cs_wire_log.CL.raw_sent
        >= server_sent_marker_count server.CS.cs_model
    with _.
    (
      lemma_server_trace_sent_marker_lower init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (server_sent_marker_count init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    CLIENT SENT ≥ 1 (field-keyed) : a reachable client whose own Finished field
    is populated has SENT at least one ApplicationData-typed record.

    Unlike `client_sent_potential` (which is control-keyed and drops to 0 at
    `ControlFailed`), this bound is keyed on the persistent field
    `hs_client_finished`, which the client sets EXACTLY when it SENDS its
    protected Finished (HsServerFinishedVerified → ControlApplicationData,
    ConnectionState.fst:1948) and which is never cleared.  It therefore survives
    a later fail into `ControlFailed`.  This is the client-side lower bound for
    the deliver-to-server ordering lemma (threshold 1-vs-0).
    ═══════════════════════════════════════════════════════════════════════════ **)

(** Field-keyed client SEND flag: 1 once the client has stored its own Finished. **)
let client_finished_sent_flag (m:CS.connection_model) : nat =
  if Some? m.CS.model_handshake.CS.hs_client_finished then 1 else 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 40 --split_queries always"
(** Per-step client SEND flag fact: the only client step that raises the flag is
    the protected Finished send (which emits exactly one ApplicationData record),
    so the flag delta is charged to the appdata SENT-delta count. **)
let lemma_client_finished_flag_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        raw_appdata_count raw_sent + client_finished_sent_flag m
          >= client_finished_sent_flag m')
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnProtectedHandshake _ ->
      Seq.lemma_eq_elim raw_sent B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_sent B.empty
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         Seq.lemma_eq_elim raw_sent B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_sent B.empty
       | CL.Sent ->
         if CS.network_message_is_cleartext CL.Sent dm.CL.message_value
         then ()
         else
           (match dm.CL.message_value with
            | M.TlsApplicationData _ -> ()
            | _ ->
              assert (CS.protected_record_count CL.Sent dm.CL.message_value == 1);
              lemma_protected_raw_count_one raw_sent))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
(** Client-step SEND flag fact, lifted to `client_step`. **)
let lemma_client_step_finished_flag
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        list_appdata_count out.SM.so_wire_outputs
          + client_finished_sent_flag st0.CS.cs_model
          >= client_finished_sent_flag st1.CS.cs_model)
  = lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (list_appdata_count out.SM.so_wire_outputs
          + client_finished_sent_flag st0.CS.cs_model
          >= client_finished_sent_flag st1.CS.cs_model)
      with _.
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_client_finished_flag_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns
        (list_appdata_count out.SM.so_wire_outputs
          + client_finished_sent_flag st0.CS.cs_model
          >= client_finished_sent_flag st1.CS.cs_model)
      with _.
      (
        lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          raw_sent;
        lemma_client_finished_flag_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
      )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level client SEND flag telescoping. **)
let rec lemma_client_trace_finished_flag
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
          (ensures
            list_appdata_count (SM.trace_wire_outputs trace)
              + client_finished_sent_flag st0.CS.cs_model
              >= client_finished_sent_flag st1.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_finished_flag st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_finished_flag init s' st1 rest;
      lemma_list_appdata_count_append
        tr.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA : CLIENT SENT ≥ 1 (field-keyed). ═══
    A reachable client whose own Finished field is set has SENT at least one
    ApplicationData-typed record. **)
let lemma_client_finished_reachable_sent_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            client_reachable (CS.initial cfg) client /\
            Some? client.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures raw_appdata_count client.CS.cs_wire_log.CL.raw_sent >= 1)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    returns raw_appdata_count client.CS.cs_wire_log.CL.raw_sent >= 1
    with _.
    (
      lemma_client_trace_finished_flag init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (client_finished_sent_flag init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent sm_bytes);
      lemma_raw_appdata_count_serialize_all out_msgs;
      lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SERVER RECV ≤ 0 : a reachable server still in its handshake RECEIVE region
    (every control up to and including HsServerFinishedSent, i.e. before it
    delivers the client Finished) has RECEIVED zero ApplicationData-typed
    records.  The client Finished is the FIRST protected record the server ever
    receives, and it is delivered ATOMICALLY into ControlApplicationData
    (Model-Fix-1), leaving the region.  This is the server-side upper bound for
    the deliver-to-server ordering lemma (threshold 1-vs-0).
    ═══════════════════════════════════════════════════════════════════════════ **)

(** The server handshake-receiving region: server controls strictly before the
    client-Finished delivery (read epoch still Initial/Handshake), excluding
    ControlFailed and every post-delivery control. **)
let server_recv_region_ctrl (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent -> true
  | _ -> false

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
(** FORWARD-CLOSURE (model level): once out of the receiving region, a legal step
    never returns.  Every region control is reached only from another region
    control (the region is a strict prefix of the server handshake). **)
let lemma_step_server_notrecvregion_stable
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            ~(server_recv_region_ctrl m.CS.model_control))
          (ensures ~(server_recv_region_ctrl m'.CS.model_control))
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
(** `~(server_recv_region_ctrl)` is forward-closed along a reachable server
    trace. **)
let rec lemma_server_trace_notrecvregion_forward
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            ~(server_recv_region_ctrl st0.CS.cs_model.CS.model_control))
          (ensures ~(server_recv_region_ctrl st1.CS.cs_model.CS.model_control))
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (conn_ev:CS.conn_event).
        CS.legal_event st0.CS.cs_model conn_ev /\
        CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model
      returns ~(server_recv_region_ctrl s'.CS.cs_model.CS.model_control)
      with _.
        lemma_step_server_notrecvregion_stable st0.CS.cs_model conn_ev s'.CS.cs_model;
      lemma_server_trace_notrecvregion_forward init s' st1 rest
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
(** Per-step server RECV UPPER fact: within the receiving region, a legal server
    step receives NO ApplicationData record.  Local/send steps receive nothing;
    a cleartext receive (ClientHello / ChangeCipherSpec) has count 0; a protected
    receive (the client Finished) delivers into ControlApplicationData, leaving
    the region — so it never keeps the server in-region. **)
let lemma_server_recv_upper_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_recv_region_ctrl m.CS.model_control /\
        server_recv_region_ctrl m'.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures raw_appdata_count raw_received <= 0)
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_received B.empty;
      lemma_raw_appdata_count_empty ();
      lemma_raw_appdata_count_seq_equal raw_received B.empty
    | CS.ConnProtectedHandshake step ->
      assert_norm (
        CS.legal_event m (CS.ConnProtectedHandshake step) ==
        CS.legal_protected_handshake_step m step);
      assert (m.CS.model_config.CS.config_role == CS.ClientEndpoint);
      assert False
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         Seq.lemma_eq_elim raw_received B.empty;
         lemma_raw_appdata_count_empty ();
         lemma_raw_appdata_count_seq_equal raw_received B.empty
       | CL.Received ->
         if CS.network_message_is_cleartext CL.Received dm.CL.message_value
         then lemma_received_cleartext_count_zero dm.CL.message_value raw_received
         else
           (* A protected receive delivers the client Finished and lands at
              ControlApplicationData, leaving the region: m' is NOT in-region,
              contradicting the hypothesis, so this arm is vacuous. *)
           assert (~(server_recv_region_ctrl m'.CS.model_control)))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 50 --split_queries always"
(** Server-step RECV UPPER fact, lifted to `server_step`. **)
let lemma_server_step_recv_upper
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_recv_region_ctrl st0.CS.cs_model.CS.model_control /\
        server_recv_region_ctrl st1.CS.cs_model.CS.model_control)
      (ensures list_appdata_count (WFSM.event_input_messages ev) <= 0)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent {
             CL.message_direction = CL.Received; CL.message_value = msg; } in
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns (list_appdata_count (WFSM.event_input_messages ev) <= 0)
      with _.
      (
        let conn_ev = CS.ConnNetworkEvent {
             CL.message_direction = CL.Received; CL.message_value = msg; } in
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        lemma_list_appdata_count_single_wire wire;
        lemma_server_recv_upper_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns (list_appdata_count (WFSM.event_input_messages ev) <= 0)
      with _.
        lemma_server_recv_upper_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level server RECV UPPER telescoping: along any reachable server trace
    whose endpoint is still in the receiving region, the total appdata RECV-input
    count is 0 (all intermediate states are in the region by forward closure). **)
let rec lemma_server_trace_recv_upper
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            server_recv_region_ctrl st1.CS.cs_model.CS.model_control)
          (ensures list_appdata_count (WFSM.trace_input_messages trace) <= 0)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      introduce ~(server_recv_region_ctrl st0.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_server_trace_notrecvregion_forward init st0 st1 trace;
      introduce ~(server_recv_region_ctrl s'.CS.cs_model.CS.model_control) ==> False
      with _.
        lemma_server_trace_notrecvregion_forward init s' st1 rest;
      lemma_server_step_recv_upper st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_recv_upper init s' st1 rest;
      lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** ═══ TARGET LEMMA : SERVER RECV ≤ 0 in the receiving region. ═══
    A reachable server still in its handshake-receiving region has RECEIVED zero
    ApplicationData-typed records. **)
let lemma_server_reachable_recv_region_le0
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            server_reachable (CS.initial cfg) server /\
            server_recv_region_ctrl server.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures raw_appdata_count server.CS.cs_wire_log.CL.raw_received <= 0)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns raw_appdata_count server.CS.cs_wire_log.CL.raw_received <= 0
    with _.
    (
      lemma_server_trace_recv_upper init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      lemma_raw_appdata_count_serialize_all in_msgs;
      lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options
