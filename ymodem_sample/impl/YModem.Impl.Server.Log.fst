module YModem.Impl.Server.Log

(**
  Pure ghost-log / reachable-trace machinery for the YMODEM *server* (sender)
  `Common.ProtocolImplementation.protocol_implementation` instance, refined
  against the *reliable-delivery (ARQ)* spec state machine
  `YModem.Protocol.ymodem_server_wfsm`.

  Unlike the prior download-only sender (which consumed NO wire input, so its
  received stream was always empty), the ARQ sender both EMITS wire output (SOH
  data blocks and the EOT marker) and now CONSUMES wire input (the receiver's
  single-byte ACK / NAK / CAN control frames).  So a single step now grows BOTH
  byte histories: a `WireEvent` grows `ysl_received` by the consumed control
  frame and `ysl_sent` by whatever it re-emits (a retransmitted data block on a
  NAK, or the re-emitted EOT); a `LocalEvent` (start/send/eot/complete/timeout/
  abort) leaves `ysl_received` unchanged and grows `ysl_sent` by the serialized
  wire outputs of the step.

  So this is the exact structural analogue of `YModem.Impl.Client.Log` (the
  unified `WireEvent`-or-`LocalEvent` step, its RTC-closure preorder and the
  canonical reachable-trace invariant `server_trace_ok`), re-threaded through the
  server state type `YModem.Protocol.ymodem_server_state`.

  All of this is pure F* (no Pulse); the Pulse instance in
  `YModem.Impl.Server.CanonicalProtocol` allocates a monotonic ghost reference
  over `ys_state_ahead_preorder` and folds `server_trace_ok` into its invariant.
  Verified but NOT extracted.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module ID = FStar.IndefiniteDescription
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module LP = LowParse.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8

module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP = Common.TCP
module CPI = Common.ProtocolImplementation
module FT = Common.FileTransfer

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire
open YModem.Impl.Control

#set-options "--fuel 2 --ifuel 2 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   The sender ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_server_log = {
  ysl_received : TCP.bytes;                 // all wire bytes received (ACK/NAK/CAN control frames)
  ysl_sent     : TCP.bytes;                 // wire output bytes (emitted SOH data blocks + EOT)
  ysl_state    : YP.ymodem_server_state;    // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:YP.ymodem_server_state) : ymodem_server_log =
  { ysl_received = received; ysl_sent = sent; ysl_state = st }

(* Agreement between the concrete 1-cell status flag carried by the Pulse handle
   and the abstract state.  Because the ARQ sender must (a) advance a positional
   ACK exactly when a block is outstanding, (b) retransmit-vs-re-emit-EOT on a
   NAK / timeout depending on the phase, and (c) abort on a CAN only while in
   progress, the concrete flag encodes the runtime phase *and* whether a block is
   in flight (stop-and-wait window 1: `acked + 1 == length sent` while one block
   is outstanding, `acked == length sent` otherwise):

     0uy  InProgress, SP_Data, nothing in flight    (acked == length sent)
     1uy  InProgress, SP_Data, one block in flight   (acked + 1 == length sent)
     2uy  InProgress, SP_Eot                         (acked == length sent)
     3uy  Completed
     4uy  Aborted

  Both `pi_process_network` and `pi_process_local` read this runtime cell: the
  network handler to decide whether an ACK / NAK / CAN is enabled and, for the
  NAK, whether to retransmit a data block or re-emit the EOT; the local handler
  to decide, for a `Server_timeout`, the same retransmit-vs-EOT branch (its
  output depends on the erased phase, which the handler cannot read directly). *)
noextract
let ys_status_flag_ok (s:U8.t) (st:YP.ymodem_server_state) : prop =
  (s == 0uy /\ st.YP.yss_status == FT.FT_InProgress /\ st.YP.yss_phase == YP.SP_Data /\
     st.YP.yss_acked == L.length st.YP.yss_sent) \/
  (s == 1uy /\ st.YP.yss_status == FT.FT_InProgress /\ st.YP.yss_phase == YP.SP_Data /\
     st.YP.yss_acked + 1 == L.length st.YP.yss_sent) \/
  (s == 2uy /\ st.YP.yss_status == FT.FT_InProgress /\ st.YP.yss_phase == YP.SP_Eot /\
     st.YP.yss_acked == L.length st.YP.yss_sent) \/
  (s == 3uy /\ st.YP.yss_status == FT.FT_Completed) \/
  (s == 4uy /\ st.YP.yss_status == FT.FT_Aborted)

noextract
let server_trace =
  list (SM.transition YP.ymodem_server_state ymodem_message YP.ymodem_server_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   Generic serialize / trace list-append lemmas  (copy-verbatim from the client)
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
let lemma_ym_serialize_all_singleton (msg:ymodem_message)
  : Lemma (WF.serialize_all ymodem_wire_format [msg] == ymodem_serialize msg)
=
  Seq.append_empty_r (ymodem_serialize msg)

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
   Single-step relation + its RTC-closure preorder

   ONE unified step: some event `ev` carries `log0` to `log1`, growing the
   received history by the serialized input messages of `ev`
   (`serialize_all [msg]` for a WireEvent, `Seq.empty` for a LocalEvent) and the
   sent history by the serialized wire outputs of the step.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let ys_step_body
  (log0 log1:ymodem_server_log)
  (ev:SM.event ymodem_message YP.ymodem_server_local)
  (out:SM.step_output ymodem_message unit)
  : prop =
  YP.ymodem_server_step log0.ysl_state ev log1.ysl_state out /\
  Seq.equal log1.ysl_received
    (Seq.append log0.ysl_received
       (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.ysl_sent
    (Seq.append log0.ysl_sent
       (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))

noextract
let ys_step_rel (log0 log1:ymodem_server_log) : prop =
  exists ev out. ys_step_body log0 log1 ev out

(* Introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_ys_step_rel_intro
  (log0 log1:ymodem_server_log)
  (ev:SM.event ymodem_message YP.ymodem_server_local)
  (out:SM.step_output ymodem_message unit)
  : Lemma (requires ys_step_body log0 log1 ev out) (ensures ys_step_rel log0 log1)
=
  ()

noextract
let ys_state_ahead_preorder : Pre.preorder ymodem_server_log =
  RTC.closure ys_step_rel

(* ── state_ahead: a single step advances the state machine ────────────────── *)

let lemma_ys_step_state_ahead (log0 log1:ymodem_server_log)
  : Lemma
      (requires ys_step_rel log0 log1)
      (ensures CPI.state_ahead YP.ymodem_server_wfsm log0.ysl_state log1.ysl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event ymodem_message YP.ymodem_server_local)
      (fun ev -> exists out. ys_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output ymodem_message unit)
      (fun out -> ys_step_body log0 log1 ev out) in
  let tr : SM.transition YP.ymodem_server_state ymodem_message YP.ymodem_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.ysl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine log0.ysl_state [tr] log1.ysl_state);
  assert (exists trace.
    SM.trace_reaches
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine log0.ysl_state trace log1.ysl_state)

let lemma_ys_closure_state_ahead (log0 log1:ymodem_server_log)
  : Lemma
      (requires ys_state_ahead_preorder log0 log1)
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

(* ── histories_ahead: a single step extends both byte histories ───────────── *)

let lemma_ys_step_histories_ahead (log0 log1:ymodem_server_log)
  : Lemma
      (requires ys_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.ysl_received log1.ysl_received /\
        TCP.bytes_extends log0.ysl_sent log1.ysl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event ymodem_message YP.ymodem_server_local)
      (fun ev -> exists out. ys_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output ymodem_message unit)
      (fun out -> ys_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.ysl_received log1.ysl_received
    (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.ysl_sent log1.ysl_sent
    (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs)

let lemma_ys_closure_histories_ahead (log0 log1:ymodem_server_log)
  : Lemma
      (requires ys_state_ahead_preorder log0 log1)
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
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let server_trace_witness
  (received sent:TCP.bytes)
  (log:ymodem_server_log)
  (trace:server_trace)
  : prop =
  SM.trace_reaches
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_server_initial
    trace
    log.ysl_state /\
  Seq.equal
    received
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.ysl_received /\
  Seq.equal sent log.ysl_sent

noextract
let server_trace_ok
  (received sent:TCP.bytes)
  (log:ymodem_server_log)
  : prop =
  exists trace. server_trace_witness received sent log trace

(* server_trace_ok refines the byte history into a valid state-machine trace. *)
let lemma_server_trace_ok_valid
  (received sent:TCP.bytes)
  (log:ymodem_server_log)
  : Lemma
      (requires server_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          YP.ymodem_server_wfsm
          received
          log.ysl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost server_trace (server_trace_witness received sent log) in
  WF.lemma_parse_serialize_all_inverse
    ymodem_wire_format
    ymodem_wire_format_stream_laws
    (WFSM.trace_input_messages trace);
  Seq.lemma_eq_elim
    received
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace));
  assert (WF.parses_as
    ymodem_wire_format
    received
    (WFSM.trace_input_messages trace)
    Seq.empty);
  assert (exists trace'.
    SM.trace_reaches
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine
      YP.ymodem_server_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.ysl_state /\
    WF.parses_as
      ymodem_wire_format
      received
      (WFSM.trace_input_messages trace')
      Seq.empty /\
    Seq.equal
      sent
      (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace')))

(* The freshly-created sender at the initial state: reached by the empty trace,
   so both byte histories are empty. *)
let lemma_initial_trace_ok ()
  : Lemma
      (server_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty YP.ymodem_server_initial))
=
  let trace : server_trace = [] in
  assert (SM.trace_reaches
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_server_initial
    trace
    YP.ymodem_server_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace));
  assert (server_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty YP.ymodem_server_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step

   A generic single-transition extension: the byte histories grow by the
   serialized input messages of `ev` and the serialized wire outputs of the step.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_server_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:YP.ymodem_server_state)
  (ev:SM.event ymodem_message YP.ymodem_server_local)
  (st1:YP.ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        YP.ymodem_server_step st0 ev st1 out)
      (ensures
        server_trace_ok
          (Seq.append received0
             (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev)))
          (Seq.append sent0
             (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))
          (mk_log
             (Seq.append received0
                (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev)))
             (Seq.append sent0
                (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))
             st1))
=
  let log0 = mk_log received0 sent0 st0 in
  let trace0 =
    ID.indefinite_description_ghost server_trace (server_trace_witness received0 sent0 log0) in
  let tr : SM.transition YP.ymodem_server_state ymodem_message YP.ymodem_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches YP.ymodem_server_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_server_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  (* input-message serialization grows by serialize_all (event_input_messages ev) *)
  lemma_trace_input_messages_append trace0 [tr];
  lemma_serialize_all_append
    ymodem_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace0));
  L.append_l_nil (WFSM.event_input_messages ev);
  (* wire-output serialization grows by serialize_all out.so_wire_outputs *)
  lemma_trace_wire_outputs_append trace0 [tr];
  lemma_serialize_all_append
    ymodem_wire_format (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs;
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace0));
  L.append_l_nil out.SM.so_wire_outputs;
  let received1 =
    Seq.append received0
      (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev)) in
  let sent1 =
    Seq.append sent0
      (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs) in
  assert (Seq.equal received1
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace1)));
  assert (Seq.equal sent1
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace1)));
  assert (server_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   process_result values, wire-output lists, step outputs, next-state helpers

   `ys_result` is `unfold`, so field projections of a literal result (its
   `process_status` / `process_consumed_len` / `process_produced_len`) reduce in
   SMT.  That lets the generic StepOk / no-op packaging lemmas below discharge
   `Common.ProtocolImplementation.{network,local}_process_correct` WITHOUT the
   `norm [delta_only …]; smt ()` tactic the client needed for its `inline_let`
   result constants.
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let ys_result (status:CPI.process_status) (consumed_len produced_len:SZ.t) : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

noextract let no_wire_outputs : list ymodem_message = []
noextract let soh_wire_outputs (body:ymodem_soh_body) : list ymodem_message = [Body_soh body]
noextract let eot_wire_outputs : list ymodem_message = [Body_eot ()]
noextract let no_local_outputs : list unit = []

noextract
let empty_output : SM.step_output ymodem_message unit =
  { SM.so_wire_outputs = no_wire_outputs; SM.so_local_outputs = no_local_outputs }
noextract
let soh_output (body:ymodem_soh_body) : SM.step_output ymodem_message unit =
  { SM.so_wire_outputs = soh_wire_outputs body; SM.so_local_outputs = no_local_outputs }
noextract
let eot_output : SM.step_output ymodem_message unit =
  { SM.so_wire_outputs = eot_wire_outputs; SM.so_local_outputs = no_local_outputs }

(* The started state Server_start installs (filename known, plan queued). *)
noextract
let start_next_state (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : YP.ymodem_server_state =
  { YP.yss_filename = Some filename; YP.yss_len = len; YP.yss_sent = [];
    YP.yss_pending = plan; YP.yss_acked = 0; YP.yss_phase = YP.SP_Data;
    YP.yss_status = FT.FT_InProgress }

(* Server_send moves the head of `pending` onto `sent` (stop-and-wait). *)
noextract
let send_next_state (st0:YP.ymodem_server_state{Cons? st0.YP.yss_pending})
  : YP.ymodem_server_state =
  { st0 with YP.yss_sent = L.append st0.YP.yss_sent [L.hd st0.YP.yss_pending];
             YP.yss_pending = L.tl st0.YP.yss_pending }

(* Server_eot: enter the EOT handshake (only the phase changes). *)
noextract
let eot_next_state (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with YP.yss_phase = YP.SP_Eot }

(* Server_complete: the EOT was acked (only the status flips). *)
noextract
let complete_next_state (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with YP.yss_status = FT.FT_Completed }

(* Server_abort / Body_can: cancel (only the status flips). *)
noextract
let abort_next_state (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with YP.yss_status = FT.FT_Aborted }

(* Body_ack: advance the acked prefix by one (stop-and-wait window closes). *)
noextract
let ack_next_state (st0:YP.ymodem_server_state) : YP.ymodem_server_state =
  { st0 with YP.yss_acked = st0.YP.yss_acked + 1 }

(* ───────────────────────────────────────────────────────────────────────────
   Step-witnesses: the enabled spec transitions

   Each proves `ymodem_server_step st0 ev st1 out` from the handler-visible
   guard.  The three output-carrying data transitions (Server_send and the two
   NAK/timeout data retransmits) hide an existential over the emitted body, so
   they `introduce` that witness explicitly.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_start_step
  (st0:YP.ymodem_server_state) (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : Lemma
      (requires st0.YP.yss_filename == None /\ YP.plan_wf plan)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent (YP.Server_start filename len plan))
          (start_next_state filename len plan) empty_output)
=
  ()

let lemma_send_step (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        Some? st0.YP.yss_filename /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_status == FT.FT_InProgress /\
        L.length st0.YP.yss_sent == st0.YP.yss_acked /\
        Cons? st0.YP.yss_pending /\ YP.plan_wf st0.YP.yss_pending /\
        YP.block_payload body == L.hd st0.YP.yss_pending)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_send)
          (send_next_state st0) (soh_output body))
=
  introduce exists (body':ymodem_soh_body).
    YP.ymodem_server_send st0 (send_next_state st0) body' /\
    (soh_output body).SM.so_wire_outputs == [Body_soh body']
  with body
  and ()

let lemma_eot_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        st0.YP.yss_phase == YP.SP_Data /\ st0.YP.yss_status == FT.FT_InProgress /\
        Some? st0.YP.yss_filename /\ st0.YP.yss_pending == [] /\
        st0.YP.yss_acked == L.length st0.YP.yss_sent)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_eot)
          (eot_next_state st0) eot_output)
=
  ()

let lemma_complete_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        st0.YP.yss_phase == YP.SP_Eot /\ st0.YP.yss_status == FT.FT_InProgress /\
        Some? st0.YP.yss_filename /\ st0.YP.yss_pending == [] /\
        st0.YP.yss_acked == L.length st0.YP.yss_sent)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_complete)
          (complete_next_state st0) empty_output)
=
  ()

let lemma_timeout_data_step (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent /\
        YP.block_payload body == L.index st0.YP.yss_sent st0.YP.yss_acked)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_timeout) st0 (soh_output body))
=
  introduce exists (body':ymodem_soh_body).
    YP.block_payload body' == L.index st0.YP.yss_sent st0.YP.yss_acked /\
    (soh_output body).SM.so_wire_outputs == [Body_soh body']
  with body
  and ()

let lemma_timeout_eot_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Eot)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_timeout) st0 eot_output)
=
  ()

let lemma_abort_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires st0.YP.yss_status == FT.FT_InProgress)
      (ensures
        YP.ymodem_server_step st0 (SM.LocalEvent YP.Server_abort)
          (abort_next_state st0) empty_output)
=
  ()

let lemma_ack_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        st0.YP.yss_phase == YP.SP_Data /\ st0.YP.yss_status == FT.FT_InProgress /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent)
      (ensures
        YP.ymodem_server_step st0 (SM.WireEvent (Body_ack ()))
          (ack_next_state st0) empty_output)
=
  ()

let lemma_nak_data_step (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent /\
        YP.block_payload body == L.index st0.YP.yss_sent st0.YP.yss_acked)
      (ensures
        YP.ymodem_server_step st0 (SM.WireEvent (Body_nak ())) st0 (soh_output body))
=
  introduce exists (body':ymodem_soh_body).
    YP.block_payload body' == L.index st0.YP.yss_sent st0.YP.yss_acked /\
    (soh_output body).SM.so_wire_outputs == [Body_soh body']
  with body
  and ()

let lemma_nak_eot_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Eot)
      (ensures
        YP.ymodem_server_step st0 (SM.WireEvent (Body_nak ())) st0 eot_output)
=
  ()

let lemma_can_step (st0:YP.ymodem_server_state)
  : Lemma
      (requires st0.YP.yss_status == FT.FT_InProgress)
      (ensures
        YP.ymodem_server_step st0 (SM.WireEvent (Body_can ()))
          (abort_next_state st0) empty_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Output-byte / produced helpers
   ─────────────────────────────────────────────────────────────────────────── *)

(* Writing nothing is a valid `output_written` at produced-length 0. *)
let lemma_output_written_empty (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz Seq.empty)
=
  assert (Seq.equal (CPI.output_prefix o 0sz) Seq.empty)

let lemma_empty_output_written (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz (WF.serialize_all ymodem_wire_format no_wire_outputs))
=
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_output_written_empty o

(* The serialized wire output of an EOT step is the single byte 0x04. *)
let lemma_eot_produced ()
  : Lemma (WF.serialize_all ymodem_wire_format eot_wire_outputs == Seq.create 1 4uy)
=
  lemma_serialize_all_control (Body_eot ())

(* Writing 0x04 at index 0 discharges `output_written` for the serialized EOT. *)
let lemma_eot_output_written (o:TCP.bytes)
  : Lemma
      (requires Seq.length o >= 1 /\ Seq.index o 0 == 4uy)
      (ensures
        CPI.output_written o 1sz (WF.serialize_all ymodem_wire_format eot_wire_outputs))
=
  lemma_eot_produced ();
  Seq.lemma_index_create 1 4uy 0;
  Seq.lemma_eq_intro (CPI.output_prefix o 1sz) (Seq.create 1 4uy)

(* A serialized SOH data block is exactly 133 bytes long. *)
let lemma_soh_serialize_length (body:ymodem_soh_body)
  : Lemma (Seq.length (ymodem_serialize (Body_soh body)) == 133)
=
  ymodem_message_bytesize_eq (Body_soh body)

(* If the 133-byte prefix of `o` is the serialized data block, `output_written`
   holds at produced-length 133. *)
let lemma_soh_output_written (o:TCP.bytes) (body:ymodem_soh_body)
  : Lemma
      (requires
        Seq.length o >= 133 /\
        Seq.equal (Seq.slice o 0 133) (ymodem_serialize (Body_soh body)))
      (ensures
        CPI.output_written o 133sz (WF.serialize_all ymodem_wire_format (soh_wire_outputs body)))
=
  lemma_soh_serialize_length body;
  lemma_ym_serialize_all_singleton (Body_soh body);
  Seq.lemma_eq_intro (CPI.output_prefix o 133sz) (ymodem_serialize (Body_soh body))

(* ───────────────────────────────────────────────────────────────────────────
   Message identification from an observed (length, lead-byte)

   The Pulse `process_network` observes the input as exactly one serialized
   message (`input == ymodem_serialize msg` for some msg — the network frame
   precondition), plus its byte length and lead byte.  These lemmas turn those
   observations into the concrete control-message identity, so the caller never
   needs the erased `msg` witness.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_input_is_serialize_ack (input:TCP.bytes)
  : Lemma
      (requires
        (exists (msg:ymodem_message). input == ymodem_serialize msg) /\
        Seq.length input == 1 /\ Seq.index input 0 == 6uy)
      (ensures input == ymodem_serialize (Body_ack ()))
=
  eliminate exists (msg:ymodem_message). input == ymodem_serialize msg
  returns input == ymodem_serialize (Body_ack ())
  with _pf.
  ( match msg with
    | Body_soh body -> lemma_soh_serialize_length body
    | Body_ack _ -> ()
    | Body_eot _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 4uy 0
    | Body_nak _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 21uy 0
    | Body_can _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 24uy 0
    | Body_crc_c _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 67uy 0 )

let lemma_input_is_serialize_nak (input:TCP.bytes)
  : Lemma
      (requires
        (exists (msg:ymodem_message). input == ymodem_serialize msg) /\
        Seq.length input == 1 /\ Seq.index input 0 == 21uy)
      (ensures input == ymodem_serialize (Body_nak ()))
=
  eliminate exists (msg:ymodem_message). input == ymodem_serialize msg
  returns input == ymodem_serialize (Body_nak ())
  with _pf.
  ( match msg with
    | Body_soh body -> lemma_soh_serialize_length body
    | Body_nak _ -> ()
    | Body_eot _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 4uy 0
    | Body_ack _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 6uy 0
    | Body_can _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 24uy 0
    | Body_crc_c _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 67uy 0 )

let lemma_input_is_serialize_can (input:TCP.bytes)
  : Lemma
      (requires
        (exists (msg:ymodem_message). input == ymodem_serialize msg) /\
        Seq.length input == 1 /\ Seq.index input 0 == 24uy)
      (ensures input == ymodem_serialize (Body_can ()))
=
  eliminate exists (msg:ymodem_message). input == ymodem_serialize msg
  returns input == ymodem_serialize (Body_can ())
  with _pf.
  ( match msg with
    | Body_soh body -> lemma_soh_serialize_length body
    | Body_can _ -> ()
    | Body_eot _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 4uy 0
    | Body_ack _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 6uy 0
    | Body_nak _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 21uy 0
    | Body_crc_c _ -> lemma_serialize_control msg; Seq.lemma_index_create 1 67uy 0 )

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas: re-establish `server_trace_ok` and expose `ys_step_rel`
   (the monotone step used to advance the ghost reference) for each transition,
   phrased in the handler's natural terms (the consumed control byte and the
   emitted serialization).  Each bridges `serialize_all (event_input_messages
   ev)` / `serialize_all out.so_wire_outputs` to those concrete byte sequences
   via the control-byte / singleton lemmas, then calls the generic
   `lemma_server_trace_ok_step` (canonical trace extension) and
   `lemma_ys_step_rel_intro` (monotone-step witness).
   ─────────────────────────────────────────────────────────────────────────── *)

(* ── wire events (grow both histories) ────────────────────────────────────── *)

let lemma_ack_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_phase == YP.SP_Data /\ st0.YP.yss_status == FT.FT_InProgress /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent)
      (ensures (
        let received1 = Seq.append received0 (Seq.create 1 6uy) in
        server_trace_ok received1 sent0 (mk_log received1 sent0 (ack_next_state st0)) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 (ack_next_state st0))))
=
  let st1 = ack_next_state st0 in
  lemma_ack_step st0;
  lemma_serialize_all_control (Body_ack ());
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Body_ack ())) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (Seq.create 1 6uy) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Body_ack ())) empty_output

let lemma_nak_data_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent /\
        YP.block_payload body == L.index st0.YP.yss_sent st0.YP.yss_acked)
      (ensures (
        let received1 = Seq.append received0 (Seq.create 1 21uy) in
        let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
        server_trace_ok received1 sent1 (mk_log received1 sent1 st0) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st0)))
=
  lemma_nak_data_step st0 body;
  lemma_serialize_all_control (Body_nak ());
  lemma_ym_serialize_all_singleton (Body_soh body);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Body_nak ())) st0 (soh_output body);
  let received1 = Seq.append received0 (Seq.create 1 21uy) in
  let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent1 st0)
    (SM.WireEvent (Body_nak ())) (soh_output body)

let lemma_nak_eot_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Eot)
      (ensures (
        let received1 = Seq.append received0 (Seq.create 1 21uy) in
        let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
        server_trace_ok received1 sent1 (mk_log received1 sent1 st0) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st0)))
=
  lemma_nak_eot_step st0;
  lemma_serialize_all_control (Body_nak ());
  lemma_eot_produced ();
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Body_nak ())) st0 eot_output;
  let received1 = Seq.append received0 (Seq.create 1 21uy) in
  let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent1 st0)
    (SM.WireEvent (Body_nak ())) eot_output

let lemma_can_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (Seq.create 1 24uy) in
        server_trace_ok received1 sent0 (mk_log received1 sent0 (abort_next_state st0)) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 (abort_next_state st0))))
=
  let st1 = abort_next_state st0 in
  lemma_can_step st0;
  lemma_serialize_all_control (Body_can ());
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Body_can ())) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (Seq.create 1 24uy) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Body_can ())) empty_output

(* ── local events (received unchanged; sent grows only for output events) ── *)

let lemma_start_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_filename == None /\ YP.plan_wf plan)
      (ensures (
        let st1 = start_next_state filename len plan in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = start_next_state filename len plan in
  lemma_start_step st0 filename len plan;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (YP.Server_start filename len plan)) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (YP.Server_start filename len plan)) empty_output

let lemma_send_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.YP.yss_filename /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_status == FT.FT_InProgress /\
        L.length st0.YP.yss_sent == st0.YP.yss_acked /\
        Cons? st0.YP.yss_pending /\ YP.plan_wf st0.YP.yss_pending /\
        YP.block_payload body == L.hd st0.YP.yss_pending)
      (ensures (
        let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
        let st1 = send_next_state st0 in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st1) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)))
=
  let st1 = send_next_state st0 in
  lemma_send_step st0 body;
  lemma_ym_serialize_all_singleton (Body_soh body);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_send) st1 (soh_output body);
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)
    (SM.LocalEvent YP.Server_send) (soh_output body)

let lemma_eot_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_phase == YP.SP_Data /\ st0.YP.yss_status == FT.FT_InProgress /\
        Some? st0.YP.yss_filename /\ st0.YP.yss_pending == [] /\
        st0.YP.yss_acked == L.length st0.YP.yss_sent)
      (ensures (
        let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
        let st1 = eot_next_state st0 in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st1) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)))
=
  let st1 = eot_next_state st0 in
  lemma_eot_step st0;
  lemma_eot_produced ();
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_eot) st1 eot_output;
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)
    (SM.LocalEvent YP.Server_eot) eot_output

let lemma_complete_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_phase == YP.SP_Eot /\ st0.YP.yss_status == FT.FT_InProgress /\
        Some? st0.YP.yss_filename /\ st0.YP.yss_pending == [] /\
        st0.YP.yss_acked == L.length st0.YP.yss_sent)
      (ensures (
        let st1 = complete_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = complete_next_state st0 in
  lemma_complete_step st0;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_complete) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent YP.Server_complete) empty_output

let lemma_timeout_data_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Data /\
        st0.YP.yss_acked < L.length st0.YP.yss_sent /\
        YP.block_payload body == L.index st0.YP.yss_sent st0.YP.yss_acked)
      (ensures (
        let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st0) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)))
=
  lemma_timeout_data_step st0 body;
  lemma_ym_serialize_all_singleton (Body_soh body);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_timeout) st0 (soh_output body);
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (ymodem_serialize (Body_soh body)) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)
    (SM.LocalEvent YP.Server_timeout) (soh_output body)

let lemma_timeout_eot_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress /\ st0.YP.yss_phase == YP.SP_Eot)
      (ensures (
        let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st0) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)))
=
  lemma_timeout_eot_step st0;
  lemma_eot_produced ();
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_timeout) st0 eot_output;
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (Seq.create 1 4uy) in
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)
    (SM.LocalEvent YP.Server_timeout) eot_output

let lemma_abort_advance (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.yss_status == FT.FT_InProgress)
      (ensures (
        let st1 = abort_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ys_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = abort_next_state st0 in
  lemma_abort_step st0;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent YP.Server_abort) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ys_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent YP.Server_abort) empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Process-correctness packaging (the pure postconditions of the handlers)

   Because `ys_result` is `unfold`, a literal result's status/consumed/produced
   fields reduce in SMT, so these lemmas discharge the
   `Common.ProtocolImplementation.{network,local}_process_correct` predicates
   with NO reflection tactic.  Two StepOk shapes (network: consumes one control
   frame + emits the serialization of the step's wire outputs; local: consumes
   nothing + emits the same) and two sound no-ops (the third "no progress"
   disjunct of `network_error_refines_state_machine`, the second of
   `local_error_refines_state_machine`).
   ─────────────────────────────────────────────────────────────────────────── *)

(* A network StepOk: the whole 1-byte input is one serialized control message
   `msg`; the machine takes `WireEvent msg`; the buffer holds `produced` (the
   serialization of the step's wire outputs); `received`/`sent` grow by the
   consumed frame / `produced`. *)
let lemma_network_stepok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  (msg:ymodem_message)
  (st1:YP.ymodem_server_state)
  (produced_len:SZ.t)
  (wire_outputs:list ymodem_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == ymodem_serialize msg /\
        YP.ymodem_server_step st0 (SM.WireEvent msg) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all ymodem_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.network_process_correct YP.ymodem_server_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          (ys_result CPI.StepOk input_len produced_len)
          (Seq.append received0 input) (Seq.append sent0 produced) st1
          input wire_outputs [])
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_ymodem_parse_serialize_exact msg;
  Seq.append_empty_r input;
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }));
  (* each conjunct of the StepOk disjunct, as an explicit hypothesis *)
  assert (CPI.consumed_by_parse
            YP.ymodem_server_wfsm.WFSM.wfsm_wire_format
            (CPI.input_bytes input input_len) msg input Seq.empty);
  assert (YP.ymodem_server_wfsm.WFSM.wfsm_state_machine.SM.sm_step
            st0 (SM.WireEvent msg) st1 (CPI.step_output wire_outputs []));
  let result = ys_result CPI.StepOk input_len produced_len in
  assert_norm (result.CPI.process_status == CPI.StepOk);
  assert_norm (result.CPI.process_consumed_len == input_len);
  assert_norm (result.CPI.process_produced_len == produced_len);
  introduce exists (msg':ymodem_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      YP.ymodem_server_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v result.CPI.process_consumed_len == Seq.length input /\
    YP.ymodem_server_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output wire_outputs []) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_server_wfsm.WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written out_bytes result.CPI.process_produced_len produced' /\
    Seq.equal (Seq.append received0 input) (Seq.append received0 input) /\
    Seq.equal (Seq.append sent0 produced) (Seq.append sent0 produced')
  with msg Seq.empty produced
  and ();
  match result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct YP.ymodem_server_wfsm
              input input_len old_out out_bytes out_len
              received0 sent0 st0
              result
              (Seq.append received0 input) (Seq.append sent0 produced) st1
              input wire_outputs [])
    by (
      FStar.Tactics.norm
        [delta_only [`%CPI.network_process_correct]; iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* A local StepOk: the machine takes `LocalEvent ev`, the buffer holds `produced`
   (the serialization of the step's wire outputs), `received` is unchanged and
   `sent` grows by `produced`. *)
let lemma_local_stepok
  (ev:YP.ymodem_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  (produced_len:SZ.t)
  (st1:YP.ymodem_server_state)
  (wire_outputs:list ymodem_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        YP.ymodem_server_step st0 (SM.LocalEvent ev) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all ymodem_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct YP.ymodem_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (ys_result CPI.StepOk 0sz produced_len)
          received0
          (Seq.append sent0 produced)
          st1 wire_outputs [])
=
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }))

(* A network no-op: no valid wire transition, so report an IllegalTransition
   that consumes nothing, produces nothing, and changes no abstract state (the
   third, "no progress" disjunct of `network_error_refines_state_machine`). *)
let lemma_network_noop
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct YP.ymodem_server_wfsm input input_len
          old_out old_out out_len
          received0 sent0 st0
          (ys_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (WF.serialize_all ymodem_wire_format ([] <: list ymodem_message) == Seq.empty);
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine YP.ymodem_server_wfsm
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])

(* A refused local event: a sound IllegalTransition no-op (the second, "no
   change" disjunct of `local_error_refines_state_machine`). *)
let lemma_local_illegal
  (ev:YP.ymodem_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_server_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct YP.ymodem_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (ys_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          [] [])
=
  assert (WF.serialize_all ymodem_wire_format ([] <: list ymodem_message) == Seq.empty);
  lemma_output_written_empty out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine
    YP.ymodem_server_wfsm st0 st0 [] [])
