module TLS13.System.WireStep

(**
  Pure step-inversion helper lemmas for the wire-level combined system
  (TLS13.System).  These are self-contained facts about the ConnectionState
  step relation used to discharge the wire/projection FACTS of `tls_system_inv`:

    * handshake-hello field MONOTONICITY across a single legal step
      (once `hs_client_hello`/`hs_server_hello` is `Some x`, it stays `Some x`);
    * the config -> supported-wire-profile derivation for a freshly-sent
      ClientHello.

  Everything here is pure F* over `TLS13.Spec.ConnectionState`; no admits.
**)

module CS  = TLS13.Spec.ConnectionState
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
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module CW  = TLS13.Impl.CanonicalWire
module CTy = TLS13.Impl.CanonicalTypes
module SM  = Common.StateMachine
module WFSM = Common.WireFormatStateMachine
module WF  = Common.WireFormat
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module CT  = TLS13.Impl.Client.Types

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
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_step_model_preserves_hellos
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires CS.legal_event m0 ev /\ CS.step_model m0 ev == Some m1 /\ hellos_shape m0)
      (ensures hellos_shape m1 /\ hs_hellos_stable m0 m1)
  = ()
#pop-options

(** config profile + start/config + CH/start  ==>  supported CH wire profile. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_ch_profile_from_start_config
  (cfg:CS.connection_config) (start:CS.handshake_start) (ch:M.client_hello)
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
  (sh:M.server_hello) (raw:B.bytes)
  : Lemma
      (requires
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello sh)) raw)
      (ensures
        W.parse_record_wire raw ==
          Some (T.Handshake, W.serialize_handshake (M.ServerHello sh), B.length raw))
=
  let fragment = W.serialize_handshake (M.ServerHello sh) in
  W.lemma_serialize_server_hello_len sh;
  W.lemma_serialize_tls_message_handshake (M.ServerHello sh);
  assert (B.length fragment <= M.server_hello_max_len);
  assert (M.server_hello_max_len <= 16640);
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
        CS.cipher_suite_offered ch.M.cipher_suites sel.CS.server_selected_cipher_suite
      | Some _, None -> False
      | None, _ -> True)
     /\
     (match st.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
            st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
      | Some (sh:M.server_hello), Some sel ->
        sh.M.cipher_suite == sel.CS.server_selected_cipher_suite /\
        B.length (sh.M.body <: B.bytes) == 0
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
        CS.connection_state_single_step st0 st1)
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
            (CS.connection_state_single_step x y)}
          server_hello_cipher_body_reachable_shape x /\
          CS.connection_state_single_step x y ==>
          server_hello_cipher_body_reachable_shape y)
=
  introduce forall x y.
    server_hello_cipher_body_reachable_shape x /\
    CS.connection_state_single_step x y ==>
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
      (requires CS.connection_state_consistent st)
      (ensures
        (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
         Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
         Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello) ==>
        (let sh : M.server_hello = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_server_hello in
         let ch : M.client_hello = Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_hello in
         CS.cipher_suite_offered ch.M.cipher_suites sh.M.cipher_suite /\
         B.length (sh.M.body <: B.bytes) == 0))
=
  let p = server_hello_cipher_body_reachable_shape in
  lemma_initial_server_hello_cipher_body_reachable_shape
    st.CS.cs_model.CS.model_config;
  lemma_single_step_server_hello_cipher_body_reachable_shape ();
  let stable :
    squash (
      forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (CS.connection_state_single_step x y)}
        p x /\ CS.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    CS.connection_state_single_step
    p
    stable;
  assert (p (CS.initial st.CS.cs_model.CS.model_config));
  assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
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

(** Client is reachable from its `CS.initial cfg` via `client_step`. **)
let client_reachable (init st:CS.connection_state) : prop =
  SM.valid_state (ClientCP.client_state_machine init) st

(** Server is reachable from its `CS.initial cfg` via `server_step`. **)
let server_reachable (init st:CS.connection_state) : prop =
  SM.valid_state (ServerCP.server_state_machine init) st

(** One official client step extends reachability. **)
let lemma_client_reachable_step
  (init st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires client_reachable init st0 /\ ClientCP.client_step st0 ev st1 out)
      (ensures client_reachable init st1)
  = SM.lemma_valid_state_after_step (ClientCP.client_state_machine init) st0 ev st1 out

(** One official server step extends reachability. **)
let lemma_server_reachable_step
  (init st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires server_reachable init st0 /\ ServerCP.server_step st0 ev st1 out)
      (ensures server_reachable init st1)
  = SM.lemma_valid_state_after_step (ServerCP.server_state_machine init) st0 ev st1 out

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30 --split_queries always"
(** Reachability from `CS.initial cfg` yields the byte-level `valid_byte_trace`. **)
let lemma_client_valid_byte_trace_of_reachable
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma
      (requires client_reachable (CS.initial cfg) client)
      (ensures
        WFSM.valid_byte_trace
          (ClientCP.client_system (CS.initial cfg))
          client.CS.cs_wire_log.CL.raw_received
          client
          client.CS.cs_wire_log.CL.raw_sent
          Seq.empty)
  = let init = CS.initial cfg in
    let sm = ClientCP.client_state_machine init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event CTy.local_output)).
      SM.trace_reaches sm init trace client
    returns
      WFSM.valid_byte_trace (ClientCP.client_system init)
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
                                   CTy.client_local_event CTy.local_output)).
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
      (requires server_reachable (CS.initial cfg) server)
      (ensures
        WFSM.valid_byte_trace
          (ServerCP.server_system (CS.initial cfg))
          server.CS.cs_wire_log.CL.raw_received
          server
          server.CS.cs_wire_log.CL.raw_sent
          Seq.empty)
  = let init = CS.initial cfg in
    let sm = ServerCP.server_state_machine init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event CTy.local_output)).
      SM.trace_reaches sm init trace server
    returns
      WFSM.valid_byte_trace (ServerCP.server_system init)
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
                                   CTy.server_local_event CTy.local_output)).
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
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires ServerCP.server_step st0 (SM.WireEvent wire) st1 out)
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
       CS.sent_event_nonempty_seal_projection
         st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       CS.received_event_nonempty_decode_projection
         st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
       ServerCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
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
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires ClientCP.client_step st0 (SM.WireEvent wire) st1 out)
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
          B.empty)
  = eliminate exists msg content_type fragment.
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
       CS.sent_event_nonempty_seal_projection
         st0.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       CS.received_event_nonempty_decode_projection
         st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
       CT.network_input_message_projection
         st0 content_type fragment msg (CW.wire_serialize wire) /\
       ClientCP.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
        B.empty
    with _. ()
#pop-options

(** The initial state is reachable (empty trace). **)
let lemma_client_reachable_initial (cfg:CS.connection_config)
  : Lemma (ensures client_reachable (CS.initial cfg) (CS.initial cfg))
  = let sm = ClientCP.client_state_machine (CS.initial cfg) in
    assert (SM.trace_reaches sm sm.SM.sm_initial_state [] (CS.initial cfg));
    introduce exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event CTy.local_output)).
      SM.trace_reaches sm sm.SM.sm_initial_state trace (CS.initial cfg)
    with [] and ()

let lemma_server_reachable_initial (cfg:CS.connection_config)
  : Lemma (ensures server_reachable (CS.initial cfg) (CS.initial cfg))
  = let sm = ServerCP.server_state_machine (CS.initial cfg) in
    assert (SM.trace_reaches sm sm.SM.sm_initial_state [] (CS.initial cfg));
    introduce exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event CTy.local_output)).
      SM.trace_reaches sm sm.SM.sm_initial_state trace (CS.initial cfg)
    with [] and ()

module CHPB = TLS13.Wire.Spec.Reveal.ClientHello.Parseback

(**
  NON-VACUITY WITNESS (single-delivery inhabitation).

  This lemma refutes the exact unsatisfiability that made the OLD
  semantic-channel design vacuous.  In that design, delivering a ClientHello to
  the server required the SAME raw bytes to satisfy both

    * the sender's cleartext projection for its stored ClientHello, whose
      [body] is empty (Impl.Serializer stores [body = B.empty]); and
    * the receiver's [received_cleartext_tls_message_raw] projection, whose
      ClientHello special case forces a body-full parse (>= 5 bytes).

  Those two constraints are JOINTLY UNSATISFIABLE on a single message value, so
  the server could never leave [HsAwaitingClientHello] and the flagship
  agreement theorem was vacuously true.

  Here, over the WIRE-LEVEL channel, the very same two projections ARE jointly
  satisfiable: from one supported (body-empty) sender ClientHello [sent_ch] we
  exhibit a common [raw] and a DISTINCT body-full received ClientHello [recv_ch]
  (with [recv_ch.body == serialize_handshake (ClientHello sent_ch)]) satisfying
  BOTH projections.  Hence a CH deliver-to-server transition
  (`TLS13.System.tls_step_deliver_to_server`) is inhabited -- not identically
  [False] -- and the vacuity source is gone.
**)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let lemma_ch_deliver_projection_inhabited (sent_ch:M.client_hello)
  : Lemma
      (requires WFL.exact_client_hello_wire_parseback_profile sent_ch)
      (ensures
        (exists (raw:B.bytes) (recv_ch:M.client_hello).
          CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello sent_ch)) raw /\
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello recv_ch)) raw /\
          recv_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch) /\
          B.length sent_ch.M.body == 0))
  = let hs = M.ClientHello sent_ch in
    let msg = M.TlsHandshake hs in
    // raw is the sender's cleartext serialization of its stored (body-empty) CH.
    let frag0 = W.serialize_handshake hs in
    let raw = CS.serialized_cleartext_tls_message msg in
    // Sender-side cleartext projection holds reflexively (ClientHello is not HRR).
    assert (CS.cleartext_tls_message_raw msg raw);
    // Pin the record framing:  raw == serialize_record Handshake frag0.
    W.lemma_serialize_tls_message_handshake hs;
    assert (Seq.equal raw (W.serialize_record T.Handshake frag0));
    // The handshake fragment fits a single record.
    WFL.lemma_serialize_handshake_client_hello_record_bound sent_ch;
    // Record round-trip:  parse_record_wire raw == Some (Handshake, frag0, len raw).
    WFL.lemma_parse_record_wire_serialize_record T.Handshake frag0;
    // Handshake-message round-trip:  frag0 parses back to a body-full CH.
    CHPB.lemma_parse_tls_message_serialize_client_hello sent_ch;
    eliminate exists (parsed_ch:M.client_hello).
        W.parse_tls_message T.Handshake frag0 ==
          Some (M.TlsHandshake (M.ClientHello parsed_ch)) /\
        Seq.equal sent_ch.M.random parsed_ch.M.random /\
        sent_ch.M.server_name == parsed_ch.M.server_name /\
        Seq.equal sent_ch.M.key_share parsed_ch.M.key_share /\
        sent_ch.M.cipher_suites == parsed_ch.M.cipher_suites /\
        sent_ch.M.signature_schemes == parsed_ch.M.signature_schemes /\
        parsed_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch)
    returns
      (exists (raw:B.bytes) (recv_ch:M.client_hello).
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello sent_ch)) raw /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello recv_ch)) raw /\
        recv_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch) /\
        B.length sent_ch.M.body == 0)
    with _. begin
      // Assemble the receiver-side projection existential with fragment = frag0.
      introduce exists (fragment:B.bytes).
          W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
          W.parse_tls_message T.Handshake fragment ==
            Some (M.TlsHandshake (M.ClientHello parsed_ch))
      with frag0 and ();
      assert (CS.received_cleartext_tls_message_raw
                (M.TlsHandshake (M.ClientHello parsed_ch)) raw);
      introduce exists (raw':B.bytes) (recv_ch:M.client_hello).
          CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello sent_ch)) raw' /\
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello recv_ch)) raw' /\
          recv_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch) /\
          B.length sent_ch.M.body == 0
      with raw parsed_ch and ()
    end
#pop-options
