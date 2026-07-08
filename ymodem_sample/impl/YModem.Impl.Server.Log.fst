module YModem.Impl.Server.Log

(**
  Pure (non-Pulse) ghost-log / reachable-trace machinery for the YMODEM *server*
  `protocol_implementation` instance (`YModem.Impl.Server.CanonicalProtocol`).

  The YMODEM server (sender) consumes NO wire input (every transition is a
  `LocalEvent`), so its whole observable history is: an empty received stream and
  a `sent` stream that is the serialization of the sequence of data packets it has
  emitted.  We record the correspondence with a *reachable-trace* invariant, in
  direct analogy with `Calc.Server.CanonicalProtocol`:

    * `server_trace_ok received sent st` says there is a trace of the server state
      machine from the initial state to `st` whose (empty) input serialization is
      `received` and whose wire-output serialization is `sent`
      (`lemma_server_trace_ok_valid` turns this into `WFSM.valid_byte_trace`);

    * a monotonic ghost-log preorder `ys_log_evolves` (the reflexive-transitive
      closure of a single-local-step relation `ys_step_rel`) drives the
      snapshot/recall obligations via the closure lemmas
      (`lemma_ys_closure_state_ahead` / `lemma_ys_closure_histories_ahead`).

  All of this is ordinary F*; the Pulse instance module simply calls these
  lemmas.  (Factoring the pure reasoning out keeps the Pulse VCs small and avoids
  quantifier-instantiation trouble inside Pulse-generated queries.)
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SM = Common.StateMachine
module WFSM = Common.WireFormatStateMachine
module WF = Common.WireFormat
module TCP = Common.TCP
module RTC = FStar.ReflexiveTransitiveClosure
module Pre = FStar.Preorder
module ID = FStar.IndefiniteDescription
module CPI = Common.ProtocolImplementation
module FT = Common.FileTransfer
module U8 = FStar.UInt8

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

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
   Reachable-trace invariant (server_trace_ok)
   ─────────────────────────────────────────────────────────────────────────── *)

let ys_trace =
  list (SM.transition YP.ymodem_server_state ymodem_packet YP.ymodem_server_local unit)

(* A trace of the server state machine reaching `st` from the initial state,
   whose input serialization is `received` (necessarily empty — the server
   consumes no wire input) and whose wire-output serialization is `sent`. *)
let server_trace_witness
  (received sent:TCP.bytes) (st:YP.ymodem_server_state) (trace:ys_trace)
  : prop =
  SM.trace_reaches YP.ymodem_server_state_machine YP.ymodem_server_initial trace st /\
  Seq.equal received Seq.empty /\
  WFSM.trace_input_messages trace == [] /\
  Seq.equal sent (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace))

let server_trace_ok
  (received sent:TCP.bytes) (st:YP.ymodem_server_state)
  : prop =
  exists (trace:ys_trace). server_trace_witness received sent st trace

(* The empty history at the initial state is a valid trace. *)
let lemma_server_trace_ok_initial ()
  : Lemma (ensures server_trace_ok Seq.empty Seq.empty YP.ymodem_server_initial)
=
  assert (SM.trace_reaches
    YP.ymodem_server_state_machine YP.ymodem_server_initial [] YP.ymodem_server_initial);
  assert (server_trace_witness Seq.empty Seq.empty YP.ymodem_server_initial [])

(* server_trace_ok refines the framework's `valid_byte_trace`. *)
let lemma_server_trace_ok_valid
  (received sent:TCP.bytes) (st:YP.ymodem_server_state)
  : Lemma
      (requires server_trace_ok received sent st)
      (ensures
        WFSM.valid_byte_trace YP.ymodem_server_wfsm received st sent Seq.empty)
=
  let trace = ID.indefinite_description_ghost ys_trace (server_trace_witness received sent st) in
  assert (server_trace_witness received sent st trace);
  assert (WFSM.trace_input_messages trace == []);
  assert (WF.parses_as ymodem_wire_format received [] Seq.empty);
  assert (WF.parses_as ymodem_wire_format received (WFSM.trace_input_messages trace) Seq.empty);
  assert (
    SM.trace_reaches
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      st /\
    WF.parses_as
      YP.ymodem_server_wfsm.WFSM.wfsm_wire_format
      received
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      sent
      (WF.serialize_all
        YP.ymodem_server_wfsm.WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace)))

(* Extending a valid trace by one local step (any server local event). *)
let lemma_server_trace_ok_step
  (received sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  (ev:YP.ymodem_server_local) (st1:YP.ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  : Lemma
      (requires
        server_trace_ok received sent0 st0 /\
        YP.ymodem_server_step st0 (SM.LocalEvent ev) st1 out)
      (ensures
        server_trace_ok
          received
          (Seq.append sent0 (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))
          st1)
=
  let trace0 = ID.indefinite_description_ghost ys_trace (server_trace_witness received sent0 st0) in
  assert (server_trace_witness received sent0 st0 trace0);
  let tr : SM.transition YP.ymodem_server_state ymodem_packet YP.ymodem_server_local unit =
    { SM.tr_event = SM.LocalEvent ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches YP.ymodem_server_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    YP.ymodem_server_state_machine YP.ymodem_server_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  (* trace_input_messages trace1 == [] *)
  lemma_trace_input_messages_append trace0 [tr];
  assert (WFSM.trace_input_messages trace1 == []);
  (* wire outputs / serialization *)
  lemma_trace_wire_outputs_append trace0 [tr];
  assert (SM.trace_wire_outputs trace1 ==
          L.append (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs);
  lemma_serialize_all_append
    ymodem_wire_format (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs;
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace0));
  let sent1 = Seq.append sent0 (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs) in
  assert (Seq.equal
    sent1
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace1)));
  assert (server_trace_witness received sent1 st1 trace1)

(* ───────────────────────────────────────────────────────────────────────────
   Monotonic ghost-log preorder
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ys_log = {
  ysl_received : TCP.bytes;
  ysl_sent     : TCP.bytes;
  ysl_state    : YP.ymodem_server_state;
}

let mk_log (received sent:TCP.bytes) (st:YP.ymodem_server_state) : ys_log =
  { ysl_received = received; ysl_sent = sent; ysl_state = st }

let initial_ys_log : ys_log = mk_log Seq.empty Seq.empty YP.ymodem_server_initial

(* A single server local step: some local event carries `log0` to `log1`,
   leaving `received` unchanged and appending the step's serialized wire outputs
   to `sent`. *)
let ys_step_body
  (log0 log1:ys_log)
  (ev:YP.ymodem_server_local)
  (out:SM.step_output ymodem_packet unit)
  : prop =
  YP.ymodem_server_step log0.ysl_state (SM.LocalEvent ev) log1.ysl_state out /\
  log1.ysl_received == log0.ysl_received /\
  Seq.equal
    log1.ysl_sent
    (Seq.append log0.ysl_sent (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))

let ys_step_rel (log0 log1:ys_log) : prop =
  exists (ev:YP.ymodem_server_local) (out:SM.step_output ymodem_packet unit).
    ys_step_body log0 log1 ev out

(* Convenience: introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_ys_step_rel_intro
  (log0 log1:ys_log)
  (ev:YP.ymodem_server_local)
  (out:SM.step_output ymodem_packet unit)
  : Lemma
      (requires ys_step_body log0 log1 ev out)
      (ensures ys_step_rel log0 log1)
=
  ()

let ys_log_evolves : Pre.preorder ys_log = RTC.closure ys_step_rel

(* A single step advances the state machine (state_ahead). *)
let lemma_ys_step_state_ahead (log0 log1:ys_log)
  : Lemma
      (requires ys_step_rel log0 log1)
      (ensures CPI.state_ahead YP.ymodem_server_wfsm log0.ysl_state log1.ysl_state)
=
  let ev =
    ID.indefinite_description_ghost YP.ymodem_server_local
      (fun ev -> exists out. ys_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost (SM.step_output ymodem_packet unit)
      (fun out -> ys_step_body log0 log1 ev out) in
  let tr : SM.transition YP.ymodem_server_state ymodem_packet YP.ymodem_server_local unit =
    { SM.tr_event = SM.LocalEvent ev; SM.tr_next_state = log1.ysl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine log0.ysl_state [tr] log1.ysl_state);
  assert (exists trace.
    SM.trace_reaches
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine log0.ysl_state trace log1.ysl_state)

(* A single step extends both histories (histories_ahead). *)
let lemma_ys_step_histories_ahead (log0 log1:ys_log)
  : Lemma
      (requires ys_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.ysl_received log1.ysl_received /\
        TCP.bytes_extends log0.ysl_sent log1.ysl_sent)
=
  let ev =
    ID.indefinite_description_ghost YP.ymodem_server_local
      (fun ev -> exists out. ys_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost (SM.step_output ymodem_packet unit)
      (fun out -> ys_step_body log0 log1 ev out) in
  assert (ys_step_body log0 log1 ev out);
  CPI.lemma_bytes_extends_refl log0.ysl_received;
  CPI.lemma_bytes_extends_append_equal
    log0.ysl_sent
    log1.ysl_sent
    (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs)

(* Closure lemmas (RTC.induct), mirroring Calc.Server.CanonicalProtocol. *)
let lemma_ys_closure_state_ahead (log0 log1:ys_log)
  : Lemma
      (requires ys_log_evolves log0 log1)
      (ensures CPI.state_ahead YP.ymodem_server_wfsm log0.ysl_state log1.ysl_state)
=
  RTC.induct
    ys_step_rel
    (fun x y -> CPI.state_ahead YP.ymodem_server_wfsm x.ysl_state y.ysl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        YP.ymodem_server_wfsm.WFSM.wfsm_state_machine x.ysl_state)
    (fun x y -> lemma_ys_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        YP.ymodem_server_wfsm.WFSM.wfsm_state_machine x.ysl_state y.ysl_state z.ysl_state)
    log0
    log1
    ()

let lemma_ys_closure_histories_ahead (log0 log1:ys_log)
  : Lemma
      (requires ys_log_evolves log0 log1)
      (ensures
        TCP.bytes_extends log0.ysl_received log1.ysl_received /\
        TCP.bytes_extends log0.ysl_sent log1.ysl_sent)
=
  RTC.induct
    ys_step_rel
    (fun x y ->
      TCP.bytes_extends x.ysl_received y.ysl_received /\
      TCP.bytes_extends x.ysl_sent y.ysl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.ysl_received;
      CPI.lemma_bytes_extends_refl x.ysl_sent)
    (fun x y -> lemma_ys_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.ysl_received y.ysl_received z.ysl_received;
      CPI.lemma_bytes_extends_trans x.ysl_sent y.ysl_sent z.ysl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Pure per-event state-transition helpers (drive `ymodem_server_step`)
   ─────────────────────────────────────────────────────────────────────────── *)

let no_wire_output : SM.step_output ymodem_packet unit =
  { SM.so_wire_outputs = []; SM.so_local_outputs = [] }

(* YmodemStart: set filename/len/pending, no wire output. *)
let ymodem_start_result
  (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : YP.ymodem_server_state =
  {
    yss_filename = Some filename;
    yss_len      = len;
    yss_sent     = [];
    yss_pending  = plan;
    yss_status   = FT.FT_InProgress;
  }

let lemma_ymodem_start_step
  (st0:YP.ymodem_server_state)
  (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : Lemma
      (requires st0.yss_filename == None /\ YP.plan_wf plan)
      (ensures
        YP.ymodem_server_step
          st0
          (SM.LocalEvent (YP.YmodemStart filename len plan))
          (ymodem_start_result filename len plan)
          no_wire_output)
=
  ()

(* YmodemSendBlock: move the head of pending to sent; the wire output is the
   packet whose 128-byte payload is that head.  Kept total (the `[]` case is
   unreachable under the precondition of `lemma_ymodem_send_result_ok`) so it can
   be bound directly as an erased value from Pulse. *)
let ymodem_send_result (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  match st0.yss_pending with
  | [] -> st0
  | h :: rest -> { st0 with yss_sent = L.append st0.yss_sent [h]; yss_pending = rest }

let lemma_ymodem_send_result_ok
  (st0:YP.ymodem_server_state) (pkt:ymodem_packet)
  : Lemma
      (requires
        Some? st0.yss_filename /\
        st0.yss_status == FT.FT_InProgress /\
        Cons? st0.yss_pending /\
        YP.plan_wf st0.yss_pending /\
        YP.block_payload pkt == L.hd st0.yss_pending)
      (ensures YP.ymodem_server_send st0 (ymodem_send_result st0) pkt)
=
  ()

let lemma_ymodem_sendblock_step
  (st0 st1:YP.ymodem_server_state) (pkt:ymodem_packet)
  : Lemma
      (requires YP.ymodem_server_send st0 st1 pkt)
      (ensures
        YP.ymodem_server_step
          st0
          (SM.LocalEvent YP.YmodemSendBlock)
          st1
          ({ SM.so_wire_outputs = [pkt]; SM.so_local_outputs = [] }))
=
  ()

(* YmodemEot: complete the transfer, no wire output. *)
let ymodem_eot_result (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with yss_status = FT.FT_Completed }

let lemma_ymodem_eot_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        Some? st0.yss_filename /\
        st0.yss_status == FT.FT_InProgress /\
        st0.yss_pending == [])
      (ensures
        YP.ymodem_server_step
          st0
          (SM.LocalEvent YP.YmodemEot)
          (ymodem_eot_result st0)
          no_wire_output)
=
  ()

(* YmodemAbort: abort the transfer, no wire output. *)
let ymodem_abort_result (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with yss_status = FT.FT_Aborted }

let lemma_ymodem_abort_step (st0:YP.ymodem_server_state)
  : Lemma
      (ensures
        YP.ymodem_server_step
          st0
          (SM.LocalEvent YP.YmodemAbort)
          (ymodem_abort_result st0)
          no_wire_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Framework-level correctness helpers

   These package the `Common.ProtocolImplementation` correctness predicates for
   the two shapes the Pulse instance produces: a local `StepOk` (any server
   event, emitting the serialization of its wire outputs) and a network no-op
   (the server has no valid wire transition, so `pi_process_network` reports an
   `IllegalTransition` that leaves everything unchanged — the third, "no
   progress" disjunct of `network_error_refines_state_machine`).
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let ys_result (status:CPI.process_status) (produced_len:FStar.SizeT.t) : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = 0sz;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

(* Writing nothing is a valid `output_written` for any buffer. *)
let lemma_output_written_empty (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz Seq.empty)
=
  assert (Seq.equal (CPI.output_prefix o 0sz) Seq.empty)

(* Same, phrased against the (empty) serialization of no wire outputs, so the
   `sent` term matches the invariant produced by `advance_and_fold_step`. *)
let lemma_output_written_empty_wire (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz (WF.serialize_all ymodem_wire_format []))
=
  assert (WF.serialize_all ymodem_wire_format ([] <: list ymodem_packet) == Seq.empty);
  lemma_output_written_empty o

(* Serializing a single packet is its `ymodem_serialize` image. *)
let lemma_serialize_all_singleton (pkt:ymodem_packet)
  : Lemma
      (Seq.equal (WF.serialize_all ymodem_wire_format [pkt]) (ymodem_serialize pkt))
=
  Seq.append_empty_r (ymodem_serialize pkt)

(* Writing the 133-byte serialization of `pkt` is a valid `output_written` at
   produced-length 133. *)
let lemma_output_written_block (o:TCP.bytes) (pkt:ymodem_packet)
  : Lemma
      (requires Seq.length o == 133 /\ o == ymodem_serialize pkt)
      (ensures CPI.output_written o 133sz (WF.serialize_all ymodem_wire_format [pkt]))
=
  lemma_serialize_all_singleton pkt;
  assert (Seq.equal (CPI.output_prefix o 133sz) o);
  assert (Seq.equal (CPI.output_prefix o 133sz) (WF.serialize_all ymodem_wire_format [pkt]))

(* A local `StepOk`: the state machine takes the local step `ev`, the buffer
   holds `produced` (the serialization of the step's wire outputs), and `sent`
   grows by `produced`. *)
let lemma_local_stepok
  (ev:YP.ymodem_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:FStar.SizeT.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  (produced_len:FStar.SizeT.t)
  (st1:YP.ymodem_server_state)
  (wire_outputs:list ymodem_packet)
  (produced:TCP.bytes)
  : Lemma
      (requires
        FStar.SizeT.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        YP.ymodem_server_step st0 (SM.LocalEvent ev) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all ymodem_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct YP.ymodem_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (ys_result CPI.StepOk produced_len)
          received0
          (Seq.append sent0 produced)
          st1 wire_outputs [])
=
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }));
  assert (Seq.equal (Seq.append sent0 produced) (Seq.append sent0 produced))

(* A network no-op: the server has no wire transition, so report an
   `IllegalTransition` that consumes nothing, produces nothing, and changes no
   abstract state. *)
let lemma_network_noop
  (input:TCP.bytes) (input_len:FStar.SizeT.t)
  (old_out:TCP.bytes) (out_len:FStar.SizeT.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct YP.ymodem_server_wfsm input input_len
          old_out old_out out_len
          received0 sent0 st0
          (ys_result CPI.IllegalTransition 0sz)
          received0 sent0 st0
          Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (WF.serialize_all ymodem_wire_format ([] <: list ymodem_packet) == Seq.empty);
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine YP.ymodem_server_wfsm
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])
