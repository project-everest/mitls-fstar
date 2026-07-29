module HTTP.Impl.Server.Log

(**
  Pure ghost-log / reachable-trace machinery **refining the executable HTTP
  Content-Length response sender against the spec state machine**
  `HTTP.Protocol.Length.http_server_wfsm`.

  Until now the HTTP sample had two verified layers that never met:

    * `HTTP.Wire.*` + `HTTP.Impl.*` — the wire codecs and Pulse loops that the
      C server actually runs (parse/serialize round-trips, framing, limits).

    * `HTTP.Protocol.Length` — a `Common.StateMachine` / `Common.FileTransfer`
      model of the protocol, verified in isolation (including the capstone
      reassembly theorem `lemma_http_server_reconstitution`).

  This module is the connective tissue: it defines the ghost log that a running
  server carries (the bytes it has received, the bytes it has written, and the
  abstract spec state it claims to be in) and proves that

    (a) the log is only ever advanced by *real spec transitions*
        (`hs_step_rel`, closed under `Common.ProtocolImplementation.state_ahead`
        and `histories_ahead`, so it is a legal monotonic-reference preorder);

    (b) the invariant `server_trace_ok` implies the generic refinement predicate
        `Common.WireFormatStateMachine.valid_byte_trace` — i.e. the observed
        byte histories are explained by SOME reachable trace of the spec state
        machine; and

    (c) [capstone] the bytes the server has actually written to the socket are
        *exactly* the concatenation of the abstract body blocks
        (`lemma_server_sent_bytes_are_body`), hence on `FT_Completed` exactly the
        file being served (`lemma_server_completed_sent_is_file`).

  This is the structural analogue of `TFTP.Impl.Server.Log` /
  `YModem.Impl.Server.Log`, re-threaded through `HTTP.Protocol.Length`.  Two
  things make the HTTP sender considerably *simpler* than either:

    * NO WIRE INPUT.  `http_server_step` maps every `SM.WireEvent` to `False`:
      the Content-Length response sender is driven purely by local events
      (start / send / complete / abort).  We turn that into a theorem
      (`lemma_server_trace_no_wire_inputs`) and use it to discharge the input
      side of `valid_byte_trace` outright — no `parses_as` obligation, and hence
      none of TFTP's `all_server_inputs_ok` sublanguage machinery.

    * NO ACK / NO RETRANSMIT.  There is no stop-and-wait window, so the concrete
      status flag encodes only progress:

        0uy  InProgress, body segments still queued  (hss_pending =/= [])
        1uy  InProgress, all segments written        (hss_pending == [])
        2uy  Completed
        3uy  Aborted

  All of this is pure F* (no Pulse).  The Pulse `protocol_implementation`
  instance that allocates a monotonic ghost reference over
  `hs_state_ahead_preorder` and folds `server_trace_ok` into its invariant is the
  next slice (`HTTP.Impl.Server.CanonicalProtocol`).  Verified but NOT extracted.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module ID = FStar.IndefiniteDescription
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16

module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP = Common.TCP
module CPI = Common.ProtocolImplementation
module FT = Common.FileTransfer

module HP = HTTP.Protocol.Length

open HTTP.Wire.Length

#set-options "--fuel 2 --ifuel 2 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   The sender ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type http_server_log = {
  hsl_received : TCP.bytes;              // all wire bytes received (always empty: see below)
  hsl_sent     : TCP.bytes;              // wire output bytes (emitted body segments)
  hsl_state    : HP.http_server_state;   // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:HP.http_server_state) : http_server_log =
  { hsl_received = received; hsl_sent = sent; hsl_state = st }

(* Agreement between the concrete 1-cell status flag carried by the Pulse handle
   and the abstract state (see the module docstring for the four values). *)
noextract
let hs_status_flag_ok (s:U8.t) (st:HP.http_server_state) : prop =
  (s == 0uy /\ st.HP.hss_status == FT.FT_InProgress /\ Cons? st.HP.hss_pending) \/
  (s == 1uy /\ st.HP.hss_status == FT.FT_InProgress /\ st.HP.hss_pending == []) \/
  (s == 2uy /\ st.HP.hss_status == FT.FT_Completed) \/
  (s == 3uy /\ st.HP.hss_status == FT.FT_Aborted)

noextract
let server_trace =
  list (SM.transition HP.http_server_state http_message HP.http_server_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   Generic serialize / trace list-append lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* Serializing a list is the concatenation of serializing the two halves. *)
let rec lemma_serialize_all_append
  (#msg:Type0) (fmt:WF.wire_format msg) (l1 l2:list msg)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all fmt (L.append l1 l2))
          (Seq.append (WF.serialize_all fmt l1) (WF.serialize_all fmt l2)))
      (decreases l1)
=
  match l1 with
  | [] -> Seq.append_empty_l (WF.serialize_all fmt l2)
  | x :: r ->
    lemma_serialize_all_append fmt r l2;
    Seq.lemma_eq_elim
      (WF.serialize_all fmt (L.append r l2))
      (Seq.append (WF.serialize_all fmt r) (WF.serialize_all fmt l2));
    Seq.append_assoc
      (fmt.WF.wf_serialize x)
      (WF.serialize_all fmt r)
      (WF.serialize_all fmt l2)

(* serialize_all of a singleton is just the serialization of that element. *)
let lemma_http_serialize_all_singleton (msg:http_message)
  : Lemma (WF.serialize_all http_wire_format [msg] == http_serialize msg)
=
  Seq.append_empty_r (http_serialize msg)

(* A single emitted body segment serializes to exactly its own payload bytes. *)
let lemma_serialize_all_body (p:body_payload)
  : Lemma (Seq.equal (WF.serialize_all http_wire_format [Msg_body p]) p)
=
  lemma_http_serialize_all_singleton (Msg_body p)

(* The wire outputs of a concatenated trace is the concatenation of the wire
   outputs. *)
let rec lemma_trace_wire_outputs_append
  (#st #wm #le #lo:Type0)
  (t1 t2:list (SM.transition st wm le lo))
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

(* Likewise for the input messages. *)
let rec lemma_trace_input_messages_append
  (#st #wm #le #lo:Type0)
  (t1 t2:list (SM.transition st wm le lo))
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
   The response sender is input-free

   `http_server_step` sends every `SM.WireEvent` to `False`, so no reachable
   trace of the sender ever consumes a wire message.  This is what lets us
   discharge the input side of `valid_byte_trace` without any prefix-parser
   sublanguage argument (TFTP needs one; YMODEM uses the stream laws).
   ─────────────────────────────────────────────────────────────────────────── *)

let rec lemma_server_trace_no_wire_inputs
  (st0:HP.http_server_state) (trace:server_trace) (st1:HP.http_server_state)
  : Lemma
      (requires SM.trace_reaches HP.http_server_state_machine st0 trace st1)
      (ensures WFSM.trace_input_messages trace == [])
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    (* A WireEvent transition is impossible: its step relation is `False`. *)
    assert (HP.http_server_step st0 tr.SM.tr_event tr.SM.tr_next_state tr.SM.tr_output);
    assert (SM.LocalEvent? tr.SM.tr_event);
    lemma_server_trace_no_wire_inputs tr.SM.tr_next_state rest st1

(* ───────────────────────────────────────────────────────────────────────────
   Single-step relation + its RTC-closure preorder
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let hs_step_body
  (log0 log1:http_server_log)
  (ev:SM.event http_message HP.http_server_local)
  (out:SM.step_output http_message unit)
  : prop =
  HP.http_server_step log0.hsl_state ev log1.hsl_state out /\
  Seq.equal log1.hsl_received
    (Seq.append log0.hsl_received
       (WF.serialize_all http_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.hsl_sent
    (Seq.append log0.hsl_sent
       (WF.serialize_all http_wire_format out.SM.so_wire_outputs))

noextract
let hs_step_rel (log0 log1:http_server_log) : prop =
  exists ev out. hs_step_body log0 log1 ev out

(* Introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_hs_step_rel_intro
  (log0 log1:http_server_log)
  (ev:SM.event http_message HP.http_server_local)
  (out:SM.step_output http_message unit)
  : Lemma (requires hs_step_body log0 log1 ev out) (ensures hs_step_rel log0 log1)
=
  ()

noextract
let hs_state_ahead_preorder : Pre.preorder http_server_log =
  RTC.closure hs_step_rel

(* ── state_ahead: a single step advances the state machine ────────────────── *)

let lemma_hs_step_state_ahead (log0 log1:http_server_log)
  : Lemma
      (requires hs_step_rel log0 log1)
      (ensures CPI.state_ahead HP.http_server_wfsm log0.hsl_state log1.hsl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event http_message HP.http_server_local)
      (fun ev -> exists out. hs_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output http_message unit)
      (fun out -> hs_step_body log0 log1 ev out) in
  let tr : SM.transition HP.http_server_state http_message HP.http_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.hsl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    HP.http_server_wfsm.WFSM.wfsm_state_machine log0.hsl_state [tr] log1.hsl_state);
  assert (exists trace.
    SM.trace_reaches
      HP.http_server_wfsm.WFSM.wfsm_state_machine log0.hsl_state trace log1.hsl_state)

let lemma_hs_closure_state_ahead (log0 log1:http_server_log)
  : Lemma
      (requires hs_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead HP.http_server_wfsm log0.hsl_state log1.hsl_state)
=
  RTC.induct
    hs_step_rel
    (fun x y -> CPI.state_ahead HP.http_server_wfsm x.hsl_state y.hsl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        HP.http_server_wfsm.WFSM.wfsm_state_machine x.hsl_state)
    (fun x y -> lemma_hs_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        HP.http_server_wfsm.WFSM.wfsm_state_machine x.hsl_state y.hsl_state z.hsl_state)
    log0
    log1
    ()

(* ── histories_ahead: a single step extends both byte histories ───────────── *)

let lemma_hs_step_histories_ahead (log0 log1:http_server_log)
  : Lemma
      (requires hs_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.hsl_received log1.hsl_received /\
        TCP.bytes_extends log0.hsl_sent log1.hsl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event http_message HP.http_server_local)
      (fun ev -> exists out. hs_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output http_message unit)
      (fun out -> hs_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.hsl_received log1.hsl_received
    (WF.serialize_all http_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.hsl_sent log1.hsl_sent
    (WF.serialize_all http_wire_format out.SM.so_wire_outputs)

let lemma_hs_closure_histories_ahead (log0 log1:http_server_log)
  : Lemma
      (requires hs_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.hsl_received log1.hsl_received /\
        TCP.bytes_extends log0.hsl_sent log1.hsl_sent)
=
  RTC.induct
    hs_step_rel
    (fun x y ->
      TCP.bytes_extends x.hsl_received y.hsl_received /\
      TCP.bytes_extends x.hsl_sent y.hsl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.hsl_received;
      CPI.lemma_bytes_extends_refl x.hsl_sent)
    (fun x y -> lemma_hs_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.hsl_received y.hsl_received z.hsl_received;
      CPI.lemma_bytes_extends_trans x.hsl_sent y.hsl_sent z.hsl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let server_trace_witness
  (received sent:TCP.bytes)
  (log:http_server_log)
  (trace:server_trace)
  : prop =
  SM.trace_reaches
    HP.http_server_wfsm.WFSM.wfsm_state_machine
    HP.http_server_initial
    trace
    log.hsl_state /\
  Seq.equal
    received
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.hsl_received /\
  Seq.equal sent log.hsl_sent

noextract
let server_trace_ok
  (received sent:TCP.bytes)
  (log:http_server_log)
  : prop =
  exists trace. server_trace_witness received sent log trace

(* `server_trace_ok` refines the byte histories into a valid state-machine
   trace.  Because the sender consumes no wire input, the input side is
   discharged by the *datagram* disjunct of `valid_byte_trace` with an empty
   message list — no prefix-parser argument is required. *)
let lemma_server_trace_ok_valid
  (received sent:TCP.bytes)
  (log:http_server_log)
  : Lemma
      (requires server_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          HP.http_server_wfsm
          received
          log.hsl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost server_trace (server_trace_witness received sent log) in
  lemma_server_trace_no_wire_inputs HP.http_server_initial trace log.hsl_state;
  assert (WFSM.trace_input_messages trace == []);
  assert (Seq.equal (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace))
                    Seq.empty);
  Seq.lemma_eq_elim
    received
    (Seq.append
      (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace))
      Seq.empty);
  assert (exists trace'.
    SM.trace_reaches
      HP.http_server_wfsm.WFSM.wfsm_state_machine
      HP.http_server_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.hsl_state /\
    (WF.parses_as
       http_wire_format received (WFSM.trace_input_messages trace') Seq.empty
     \/
     Seq.equal
       received
       (Seq.append
         (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace'))
         Seq.empty)) /\
    Seq.equal
      sent
      (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace')))

(* Corollary: a server satisfying the invariant has received nothing.  This is
   the byte-level statement of "the Content-Length response sender is driven
   entirely by local events". *)
let lemma_server_trace_ok_received_empty
  (received sent:TCP.bytes)
  (log:http_server_log)
  : Lemma
      (requires server_trace_ok received sent log)
      (ensures Seq.equal received Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost server_trace (server_trace_witness received sent log) in
  lemma_server_trace_no_wire_inputs HP.http_server_initial trace log.hsl_state

(* The freshly-created sender at the initial state: reached by the empty trace,
   so both byte histories are empty. *)
let lemma_initial_trace_ok ()
  : Lemma
      (server_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty HP.http_server_initial))
=
  let trace : server_trace = [] in
  assert (SM.trace_reaches
    HP.http_server_wfsm.WFSM.wfsm_state_machine
    HP.http_server_initial
    trace
    HP.http_server_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace));
  assert (server_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty HP.http_server_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_server_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:HP.http_server_state)
  (ev:SM.event http_message HP.http_server_local)
  (st1:HP.http_server_state)
  (out:SM.step_output http_message unit)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        HP.http_server_step st0 ev st1 out)
      (ensures
        server_trace_ok
          (Seq.append received0
             (WF.serialize_all http_wire_format (WFSM.event_input_messages ev)))
          (Seq.append sent0
             (WF.serialize_all http_wire_format out.SM.so_wire_outputs))
          (mk_log
             (Seq.append received0
                (WF.serialize_all http_wire_format (WFSM.event_input_messages ev)))
             (Seq.append sent0
                (WF.serialize_all http_wire_format out.SM.so_wire_outputs))
             st1))
=
  let log0 = mk_log received0 sent0 st0 in
  let trace0 =
    ID.indefinite_description_ghost server_trace (server_trace_witness received0 sent0 log0) in
  let tr : SM.transition HP.http_server_state http_message HP.http_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches HP.http_server_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    HP.http_server_wfsm.WFSM.wfsm_state_machine
    HP.http_server_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  (* input-message serialization grows by serialize_all (event_input_messages ev) *)
  lemma_trace_input_messages_append trace0 [tr];
  lemma_serialize_all_append
    http_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace0));
  L.append_l_nil (WFSM.event_input_messages ev);
  (* wire-output serialization grows by serialize_all out.so_wire_outputs *)
  lemma_trace_wire_outputs_append trace0 [tr];
  lemma_serialize_all_append
    http_wire_format (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs;
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace0));
  L.append_l_nil out.SM.so_wire_outputs;
  let received1 =
    Seq.append received0
      (WF.serialize_all http_wire_format (WFSM.event_input_messages ev)) in
  let sent1 =
    Seq.append sent0
      (WF.serialize_all http_wire_format out.SM.so_wire_outputs) in
  assert (Seq.equal received1
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace1)));
  assert (Seq.equal sent1
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace1)));
  assert (server_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   Wire-output lists, step outputs, next-state helpers
   ─────────────────────────────────────────────────────────────────────────── *)

noextract let no_wire_outputs : list http_message = []
noextract let body_wire_outputs (p:body_payload) : list http_message = [Msg_body p]
noextract let no_local_outputs : list unit = []

noextract
let empty_output : SM.step_output http_message unit =
  { SM.so_wire_outputs = no_wire_outputs; SM.so_local_outputs = no_local_outputs }

noextract
let body_output (p:body_payload) : SM.step_output http_message unit =
  { SM.so_wire_outputs = body_wire_outputs p; SM.so_local_outputs = no_local_outputs }

(* Server_start installs the target and queues the pre-framed body plan. *)
noextract
let start_next_state (filename:TCP.bytes) (plan:list TCP.bytes)
  : HP.http_server_state =
  { HP.hss_filename = Some filename; HP.hss_sent = [];
    HP.hss_pending = plan; HP.hss_status = FT.FT_InProgress }

(* Server_send moves the head of `pending` onto `sent`. *)
noextract
let send_next_state (st0:HP.http_server_state{Cons? st0.HP.hss_pending})
  : HP.http_server_state =
  { st0 with HP.hss_sent = L.append st0.HP.hss_sent [L.hd st0.HP.hss_pending];
             HP.hss_pending = L.tl st0.HP.hss_pending }

(* Server_complete: the whole declared Content-Length was written. *)
noextract
let complete_next_state (st0:HP.http_server_state) : HP.http_server_state =
  { st0 with HP.hss_status = FT.FT_Completed }

(* Server_abort: connection torn down mid-body. *)
noextract
let abort_next_state (st0:HP.http_server_state) : HP.http_server_state =
  { st0 with HP.hss_status = FT.FT_Aborted }

(* ───────────────────────────────────────────────────────────────────────────
   Step-witnesses: the enabled spec transitions
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_start_step
  (st0:HP.http_server_state) (filename:TCP.bytes) (plan:list TCP.bytes)
  : Lemma
      (requires st0.HP.hss_filename == None /\ HP.plan_wf plan)
      (ensures
        HP.http_server_step st0 (SM.LocalEvent (HP.Server_start filename plan))
          (start_next_state filename plan) empty_output)
=
  ()

let lemma_send_step (st0:HP.http_server_state) (p:body_payload)
  : Lemma
      (requires
        Some? st0.HP.hss_filename /\
        st0.HP.hss_status == FT.FT_InProgress /\
        Cons? st0.HP.hss_pending /\
        HP.plan_wf st0.HP.hss_pending /\
        (p <: TCP.bytes) == L.hd st0.HP.hss_pending)
      (ensures
        HP.http_server_step st0 (SM.LocalEvent HP.Server_send)
          (send_next_state st0) (body_output p))
=
  assert (HP.http_server_send st0 (send_next_state st0) p)

let lemma_complete_step (st0:HP.http_server_state)
  : Lemma
      (requires
        st0.HP.hss_status == FT.FT_InProgress /\
        Some? st0.HP.hss_filename /\
        st0.HP.hss_pending == [])
      (ensures
        HP.http_server_step st0 (SM.LocalEvent HP.Server_complete)
          (complete_next_state st0) empty_output)
=
  ()

let lemma_abort_step (st0:HP.http_server_state)
  : Lemma
      (requires st0.HP.hss_status == FT.FT_InProgress)
      (ensures
        HP.http_server_step st0 (SM.LocalEvent HP.Server_abort)
          (abort_next_state st0) empty_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   `output_written` helpers (bridge to the Pulse buffer discipline)
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_output_written_empty (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz Seq.empty)
=
  assert (Seq.equal (CPI.output_prefix o 0sz) Seq.empty)

let lemma_empty_output_written (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz (WF.serialize_all http_wire_format no_wire_outputs))
=
  assert (WF.serialize_all http_wire_format no_wire_outputs == Seq.empty);
  lemma_output_written_empty o

(* If the output buffer holds exactly the body segment, `output_written` holds
   at that produced-length. *)
let lemma_body_output_written
  (o:TCP.bytes) (produced_len:SZ.t) (p:body_payload)
  : Lemma
      (requires
        SZ.v produced_len == Seq.length o /\
        (o <: TCP.bytes) == (p <: TCP.bytes))
      (ensures
        CPI.output_written o produced_len
          (WF.serialize_all http_wire_format (body_wire_outputs p)))
=
  lemma_http_serialize_all_singleton (Msg_body p);
  Seq.lemma_eq_intro (CPI.output_prefix o produced_len) (p <: TCP.bytes)

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas: each concrete server operation extends the canonical trace
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_start_advance
  (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  (filename:TCP.bytes) (plan:list TCP.bytes)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.HP.hss_filename == None /\ HP.plan_wf plan)
      (ensures (
        let st1 = start_next_state filename plan in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        hs_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = start_next_state filename plan in
  lemma_start_step st0 filename plan;
  assert (WF.serialize_all http_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (HP.Server_start filename plan)) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_hs_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (HP.Server_start filename plan)) empty_output

let lemma_send_advance
  (received0 sent0:TCP.bytes) (st0:HP.http_server_state) (p:body_payload)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.HP.hss_filename /\
        st0.HP.hss_status == FT.FT_InProgress /\
        Cons? st0.HP.hss_pending /\
        HP.plan_wf st0.HP.hss_pending /\
        (p <: TCP.bytes) == L.hd st0.HP.hss_pending)
      (ensures (
        let sent1 = Seq.append sent0 p in
        let st1 = send_next_state st0 in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st1) /\
        hs_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)))
=
  let st1 = send_next_state st0 in
  lemma_send_step st0 p;
  lemma_serialize_all_body p;
  Seq.lemma_eq_elim (WF.serialize_all http_wire_format (body_wire_outputs p)) p;
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent HP.Server_send) st1 (body_output p);
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 p in
  lemma_hs_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)
    (SM.LocalEvent HP.Server_send) (body_output p)

let lemma_complete_advance (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.HP.hss_status == FT.FT_InProgress /\
        Some? st0.HP.hss_filename /\
        st0.HP.hss_pending == [])
      (ensures (
        let st1 = complete_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        hs_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = complete_next_state st0 in
  lemma_complete_step st0;
  assert (WF.serialize_all http_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent HP.Server_complete) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_hs_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent HP.Server_complete) empty_output

let lemma_abort_advance (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.HP.hss_status == FT.FT_InProgress)
      (ensures (
        let st1 = abort_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        hs_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = abort_next_state st0 in
  lemma_abort_step st0;
  assert (WF.serialize_all http_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent HP.Server_abort) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_hs_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent HP.Server_abort) empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Capstone: the bytes on the wire ARE the file

   `server_trace_ok` says the byte histories are explained by SOME reachable
   trace.  The theorems below pin that down to the strongest possible statement
   for a Content-Length sender: the bytes actually written to the socket are
   *exactly* `ft_concat` of the abstract delivered blocks, hence — once the spec
   state reaches `FT_Completed` — exactly the file being served.
   ─────────────────────────────────────────────────────────────────────────── *)

(* Two inductive invariants of the sender state, needed to pin down the bytes:
     * before the request is bound, nothing has been queued or sent; and
     * completion only happens with an empty pending queue. *)
noextract
let server_state_inv (st:HP.http_server_state) : prop =
  (st.HP.hss_filename == None ==>
     (st.HP.hss_sent == [] /\ st.HP.hss_pending == [])) /\
  (st.HP.hss_status == FT.FT_Completed ==> st.HP.hss_pending == [])

let lemma_server_state_inv_initial ()
  : Lemma (server_state_inv HP.http_server_initial)
=
  ()

(* The heart of the refinement: relative to any start state, the bytes emitted
   along a trace are exactly the newly-delivered blocks. *)
let rec lemma_trace_sent_blocks
  (st0:HP.http_server_state) (trace:server_trace) (st1:HP.http_server_state)
  : Lemma
      (requires
        SM.trace_reaches HP.http_server_state_machine st0 trace st1 /\
        server_state_inv st0)
      (ensures
        server_state_inv st1 /\
        Seq.equal
          (Seq.append
            (FT.ft_concat st0.HP.hss_sent)
            (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace)))
          (FT.ft_concat st1.HP.hss_sent))
      (decreases trace)
=
  match trace with
  | [] ->
    Seq.append_empty_r (FT.ft_concat st0.HP.hss_sent)
  | tr :: rest ->
    let stm = tr.SM.tr_next_state in
    assert (HP.http_server_step st0 tr.SM.tr_event stm tr.SM.tr_output);
    assert (SM.LocalEvent? tr.SM.tr_event);
    (* one step: the emitted bytes are exactly the newly-delivered blocks *)
    (match tr.SM.tr_event with
     | SM.LocalEvent (HP.Server_start _ _) ->
       (* `hss_filename == None` forces `hss_sent == []` by the invariant *)
       assert (st0.HP.hss_sent == []);
       assert (stm.HP.hss_sent == [])
     | SM.LocalEvent HP.Server_send ->
       let d =
         ID.indefinite_description_ghost body_payload
           (fun (d:body_payload) ->
             HP.http_server_send st0 stm d /\
             tr.SM.tr_output.SM.so_wire_outputs == [Msg_body d]) in
       lemma_serialize_all_body d;
       HP.lemma_ft_concat_append st0.HP.hss_sent [d];
       Seq.append_empty_r (d <: TCP.bytes)
     | SM.LocalEvent HP.Server_complete -> ()
     | SM.LocalEvent HP.Server_abort -> ());
    assert (Seq.equal
      (Seq.append
        (FT.ft_concat st0.HP.hss_sent)
        (WF.serialize_all http_wire_format tr.SM.tr_output.SM.so_wire_outputs))
      (FT.ft_concat stm.HP.hss_sent));
    lemma_trace_sent_blocks stm rest st1;
    (* stitch the head step onto the inductive tail *)
    lemma_trace_wire_outputs_append [tr] rest;
    lemma_serialize_all_append
      http_wire_format
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    L.append_l_nil tr.SM.tr_output.SM.so_wire_outputs;
    Seq.append_assoc
      (FT.ft_concat st0.HP.hss_sent)
      (WF.serialize_all http_wire_format tr.SM.tr_output.SM.so_wire_outputs)
      (WF.serialize_all http_wire_format (SM.trace_wire_outputs rest))

(* CAPSTONE 1.  Every byte the server has written to the socket is accounted for
   by an abstract delivered block, and vice versa. *)
let lemma_server_sent_bytes_are_body
  (received sent:TCP.bytes) (st:HP.http_server_state)
  : Lemma
      (requires server_trace_ok received sent (mk_log received sent st))
      (ensures
        server_state_inv st /\
        Seq.equal sent (FT.ft_concat st.HP.hss_sent))
=
  let log = mk_log received sent st in
  let trace =
    ID.indefinite_description_ghost server_trace (server_trace_witness received sent log) in
  lemma_server_state_inv_initial ();
  lemma_trace_sent_blocks HP.http_server_initial trace st;
  assert (FT.ft_concat HP.http_server_initial.HP.hss_sent == Seq.empty);
  Seq.append_empty_l (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace))

(* CAPSTONE 2.  Once the spec state reports `FT_Completed`, the bytes written are
   *exactly* the file being served — no truncation, no padding, no duplication.
   This is the end-to-end guarantee the executable Content-Length sender was
   built to provide, now stated over the real socket byte history. *)
let lemma_server_completed_sent_is_file
  (received sent:TCP.bytes) (st:HP.http_server_state)
  : Lemma
      (requires
        server_trace_ok received sent (mk_log received sent st) /\
        st.HP.hss_status == FT.FT_Completed)
      (ensures
        Seq.equal sent (HP.http_full st) /\
        (match HP.http_content st with
         | None -> True
         | Some content -> Seq.equal sent content))
=
  lemma_server_sent_bytes_are_body received sent st;
  assert (st.HP.hss_pending == []);
  L.append_l_nil st.HP.hss_sent;
  assert (HP.http_full st == FT.ft_concat st.HP.hss_sent)

(* CAPSTONE 3.  The same fact routed through the generic `Common.FileTransfer`
   view, so it composes with `HP.lemma_http_server_reconstitution`: the socket
   byte history is the reassembly of the file-transfer blocks, and on completion
   that reassembly is exact. *)
let lemma_server_sent_is_reassembly
  (received sent:TCP.bytes) (st:HP.http_server_state)
  : Lemma
      (requires server_trace_ok received sent (mk_log received sent st))
      (ensures
        Seq.equal sent (FT.ft_concat (HP.http_server_project st).FT.ftv_blocks) /\
        (st.HP.hss_status == FT.FT_Completed /\ Some? st.HP.hss_filename ==>
          (match (HP.http_server_project st).FT.ftv_content with
           | None -> False
           | Some content -> FT.reassembly_exact (HP.http_server_project st).FT.ftv_blocks content)))
=
  lemma_server_sent_bytes_are_body received sent st;
  HP.lemma_http_server_reconstitution st

(* ───────────────────────────────────────────────────────────────────────────
   Bridge to `Common.ProtocolImplementation.{local,network}_process_correct`

   These are the obligations the Pulse `protocol_implementation` instance in
   `HTTP.Impl.Server.CanonicalProtocol` has to discharge at each of its exits.
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let hs_result (status:CPI.process_status) (consumed_len produced_len:SZ.t)
  : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

(* A local event that really fired: `StepOk`, appending the produced bytes. *)
let lemma_local_stepok
  (ev:HP.http_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  (produced_len:SZ.t)
  (st1:HP.http_server_state)
  (wire_outputs:list http_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        HP.http_server_step st0 (SM.LocalEvent ev) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all http_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct HP.http_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (hs_result CPI.StepOk 0sz produced_len)
          received0
          (Seq.append sent0 produced)
          st1 wire_outputs [])
=
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }))

(* A local event that is not enabled: a sound `IllegalTransition` no-op. *)
let lemma_local_illegal
  (ev:HP.http_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct HP.http_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (hs_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          [] [])
=
  assert (WF.serialize_all http_wire_format ([] <: list http_message) == Seq.empty);
  lemma_output_written_empty out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine HP.http_server_wfsm st0 st0 [] [])

(* THE network handler of the response sender.  `http_server_step` maps every
   `SM.WireEvent` to `False`, so no wire input can ever advance this endpoint:
   the only sound answer is the no-progress `IllegalTransition` no-op, and it is
   sound *unconditionally* — whatever bytes arrive.  This is the refinement-level
   statement of `lemma_server_trace_no_wire_inputs`. *)
let lemma_network_noop
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:HP.http_server_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct HP.http_server_wfsm input input_len
          old_out old_out out_len
          received0 sent0 st0
          (hs_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (WF.serialize_all http_wire_format ([] <: list http_message) == Seq.empty);
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine HP.http_server_wfsm
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])
