module YModem.Impl.Client.Log

(**
  Pure ghost-log / reachable-trace machinery for the YMODEM *client* (receiver)
  `Common.ProtocolImplementation.protocol_implementation` instance, refined
  against the *reliable-delivery (ARQ)* spec state machine
  `YModem.Protocol.ymodem_client_wfsm`.

  This is the receiver analogue of `Calc.Log` + the trace lemmas of
  `Calc.Server.CanonicalProtocol`, but — unlike the prior download-only client —
  the ARQ receiver both CONSUMES wire input (SOH data packets and the single-byte
  EOT/CAN control frames) and EMITS wire output (a `Body_ack ()` on every SOH data
  block and on the EOT).  So a single `WireEvent` step now grows BOTH byte
  histories: `ycl_received` by the consumed frame and `ycl_sent` by the emitted
  ACK.  The lone local event `Client_start` initialises the receiver (setting the
  filename) and touches neither history.

  It bundles the receiver's wire history (`ycl_received`), its wire-output history
  (`ycl_sent`) and its abstract spec state (`ycl_state`) into a
  `ymodem_client_log`, equips it with the reflexive-transitive closure of a
  single-step relation (`yc_step_rel`, one `WireEvent`-or-`LocalEvent` transition)
  as a monotonicity preorder, and proves the closure lemmas
  (`state_ahead` / `histories_ahead`) plus the canonical reachable-trace
  invariant (`client_trace_ok`) that refines a byte history into a valid state
  machine trace (`valid_byte_trace`).

  All of this is pure F* (no Pulse); the Pulse instance in
  `YModem.Impl.Client.CanonicalProtocol` allocates a monotonic ghost reference
  over `yc_state_ahead_preorder` and folds `client_trace_ok` into its invariant.
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
   The receiver ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_log = {
  ycl_received : TCP.bytes;                 // all wire bytes received (SOH + control frames)
  ycl_sent     : TCP.bytes;                 // wire output bytes (the emitted ACKs)
  ycl_state    : YP.ymodem_client_state;    // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:YP.ymodem_client_state) : ymodem_client_log =
  { ycl_received = received; ycl_sent = sent; ycl_state = st }

(* Agreement between the concrete 1-byte status cell carried by the Pulse handle
   and the abstract state.  Four runtime values, because the ARQ receiver is born
   *un-started* (the initial state has `ycs_filename == None`) and the concrete
   `Client_start` step must be distinguishable from the started/in-progress state
   (both are `FT_InProgress`):

     0uy  not-yet-started   (ycs_filename == None,   FT_InProgress)
     1uy  started/receiving (Some? ycs_filename,     FT_InProgress)
     2uy  completed         (Some? ycs_filename,     FT_Completed)
     3uy  aborted           (Some? ycs_filename,     FT_Aborted)

  Both `pi_process_network` and `pi_process_local` read this runtime cell and
  branch on it: neither process fn may branch on the erased abstract state, so the
  runtime source of truth for the transfer status (and, crucially, for whether a
  filename is known) is this concrete flag. *)
noextract
let yc_status_flag_ok (s:U8.t) (st:YP.ymodem_client_state) : prop =
  (s == 0uy /\ st.YP.ycs_status == FT.FT_InProgress /\ st.YP.ycs_filename == None) \/
  (s == 1uy /\ st.YP.ycs_status == FT.FT_InProgress /\ Some? st.YP.ycs_filename) \/
  (s == 2uy /\ st.YP.ycs_status == FT.FT_Completed  /\ Some? st.YP.ycs_filename) \/
  (s == 3uy /\ st.YP.ycs_status == FT.FT_Aborted    /\ Some? st.YP.ycs_filename)

noextract
let client_trace =
  list (SM.transition YP.ymodem_client_state ymodem_message YP.ymodem_client_local unit)

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
let yc_step_body
  (log0 log1:ymodem_client_log)
  (ev:SM.event ymodem_message YP.ymodem_client_local)
  (out:SM.step_output ymodem_message unit)
  : prop =
  YP.ymodem_client_step log0.ycl_state ev log1.ycl_state out /\
  Seq.equal log1.ycl_received
    (Seq.append log0.ycl_received
       (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.ycl_sent
    (Seq.append log0.ycl_sent
       (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs))

noextract
let yc_step_rel (log0 log1:ymodem_client_log) : prop =
  exists ev out. yc_step_body log0 log1 ev out

(* Introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_yc_step_rel_intro
  (log0 log1:ymodem_client_log)
  (ev:SM.event ymodem_message YP.ymodem_client_local)
  (out:SM.step_output ymodem_message unit)
  : Lemma (requires yc_step_body log0 log1 ev out) (ensures yc_step_rel log0 log1)
=
  ()

noextract
let yc_state_ahead_preorder : Pre.preorder ymodem_client_log =
  RTC.closure yc_step_rel

(* ── state_ahead: a single step advances the state machine ────────────────── *)

let lemma_yc_step_state_ahead (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_step_rel log0 log1)
      (ensures CPI.state_ahead YP.ymodem_client_wfsm log0.ycl_state log1.ycl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event ymodem_message YP.ymodem_client_local)
      (fun ev -> exists out. yc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output ymodem_message unit)
      (fun out -> yc_step_body log0 log1 ev out) in
  let tr : SM.transition YP.ymodem_client_state ymodem_message YP.ymodem_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.ycl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine log0.ycl_state [tr] log1.ycl_state);
  assert (exists trace.
    SM.trace_reaches
      YP.ymodem_client_wfsm.WFSM.wfsm_state_machine log0.ycl_state trace log1.ycl_state)

let lemma_yc_closure_state_ahead (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead YP.ymodem_client_wfsm log0.ycl_state log1.ycl_state)
=
  RTC.induct
    yc_step_rel
    (fun x y -> CPI.state_ahead YP.ymodem_client_wfsm x.ycl_state y.ycl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        YP.ymodem_client_wfsm.WFSM.wfsm_state_machine x.ycl_state)
    (fun x y -> lemma_yc_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        YP.ymodem_client_wfsm.WFSM.wfsm_state_machine x.ycl_state y.ycl_state z.ycl_state)
    log0
    log1
    ()

(* ── histories_ahead: a single step extends both byte histories ───────────── *)

let lemma_yc_step_histories_ahead (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.ycl_received log1.ycl_received /\
        TCP.bytes_extends log0.ycl_sent log1.ycl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event ymodem_message YP.ymodem_client_local)
      (fun ev -> exists out. yc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output ymodem_message unit)
      (fun out -> yc_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.ycl_received log1.ycl_received
    (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.ycl_sent log1.ycl_sent
    (WF.serialize_all ymodem_wire_format out.SM.so_wire_outputs)

let lemma_yc_closure_histories_ahead (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.ycl_received log1.ycl_received /\
        TCP.bytes_extends log0.ycl_sent log1.ycl_sent)
=
  RTC.induct
    yc_step_rel
    (fun x y ->
      TCP.bytes_extends x.ycl_received y.ycl_received /\
      TCP.bytes_extends x.ycl_sent y.ycl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.ycl_received;
      CPI.lemma_bytes_extends_refl x.ycl_sent)
    (fun x y -> lemma_yc_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.ycl_received y.ycl_received z.ycl_received;
      CPI.lemma_bytes_extends_trans x.ycl_sent y.ycl_sent z.ycl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let client_trace_witness
  (received sent:TCP.bytes)
  (log:ymodem_client_log)
  (trace:client_trace)
  : prop =
  SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_client_initial
    trace
    log.ycl_state /\
  Seq.equal
    received
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.ycl_received /\
  Seq.equal sent log.ycl_sent

noextract
let client_trace_ok
  (received sent:TCP.bytes)
  (log:ymodem_client_log)
  : prop =
  exists trace. client_trace_witness received sent log trace

(* client_trace_ok refines the byte history into a valid state-machine trace. *)
let lemma_client_trace_ok_valid
  (received sent:TCP.bytes)
  (log:ymodem_client_log)
  : Lemma
      (requires client_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          YP.ymodem_client_wfsm
          received
          log.ycl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost client_trace (client_trace_witness received sent log) in
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
      YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
      YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.ycl_state /\
    WF.parses_as
      ymodem_wire_format
      received
      (WFSM.trace_input_messages trace')
      Seq.empty /\
    Seq.equal
      sent
      (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace')))

(* The freshly-created (un-started) receiver at the initial state: reached by the
   empty trace, so both byte histories are empty. *)
let lemma_initial_trace_ok ()
  : Lemma
      (client_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty YP.ymodem_client_initial))
=
  let trace : client_trace = [] in
  assert (SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_client_initial
    trace
    YP.ymodem_client_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace));
  assert (client_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty YP.ymodem_client_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step

   A generic single-transition extension: the byte histories grow by the
   serialized input messages of `ev` and the serialized wire outputs of the step.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_client_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:YP.ymodem_client_state)
  (ev:SM.event ymodem_message YP.ymodem_client_local)
  (st1:YP.ymodem_client_state)
  (out:SM.step_output ymodem_message unit)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        YP.ymodem_client_step st0 ev st1 out)
      (ensures
        client_trace_ok
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
    ID.indefinite_description_ghost client_trace (client_trace_witness received0 sent0 log0) in
  let tr : SM.transition YP.ymodem_client_state ymodem_message YP.ymodem_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches YP.ymodem_client_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_client_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  (* input-message serialization grows by serialize_all (event_input_messages ev) *)
  lemma_trace_input_messages_append trace0 [tr];
  lemma_serialize_all_append
    ymodem_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace0));
  (* WFSM.trace_input_messages [tr] == event_input_messages ev *)
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
  assert (client_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   process_result values, next-state helpers, output lists
   ─────────────────────────────────────────────────────────────────────────── *)

[@inline_let]
noextract
let ymodem_client_process_result
  (status:CPI.process_status) (consumed produced:SZ.t) : CPI.process_result =
  {
    CPI.process_status = status;
    CPI.process_consumed_len = consumed;
    CPI.process_produced_len = produced;
    CPI.process_app_len = 0sz;
  }

(* A received SOH data packet: consumed the 133-byte frame, emitted a 1-byte ACK. *)
[@inline_let]
noextract
let soh_result : CPI.process_result = ymodem_client_process_result CPI.StepOk 133sz 1sz

(* A received EOT: consumed the 1-byte control frame, emitted a 1-byte ACK. *)
[@inline_let]
noextract
let eot_result : CPI.process_result = ymodem_client_process_result CPI.StepOk 1sz 1sz

(* A received CAN: consumed the 1-byte control frame, emitted nothing. *)
[@inline_let]
noextract
let can_result : CPI.process_result = ymodem_client_process_result CPI.StepOk 1sz 0sz

(* A refused wire/local event: a sound no-op. *)
[@inline_let]
noextract
let illegal_result : CPI.process_result = ymodem_client_process_result CPI.IllegalTransition 0sz 0sz

(* The Client_start local step: consumes/produces nothing. *)
[@inline_let]
noextract
let start_result : CPI.process_result = ymodem_client_process_result CPI.StepOk 0sz 0sz

noextract
let ack_wire_outputs : list ymodem_message = [Body_ack ()]
noextract
let no_wire_outputs : list ymodem_message = []
noextract
let no_local_outputs : list unit = []

noextract
let ack_output : SM.step_output ymodem_message unit =
  { SM.so_wire_outputs = ack_wire_outputs; SM.so_local_outputs = no_local_outputs }
noextract
let empty_output : SM.step_output ymodem_message unit =
  { SM.so_wire_outputs = no_wire_outputs; SM.so_local_outputs = no_local_outputs }

(* The state reached after receiving one SOH data block. *)
noextract
let soh_next_state (st0:YP.ymodem_client_state) (body:ymodem_soh_body)
  : YP.ymodem_client_state =
  { st0 with YP.ycs_received = L.append st0.YP.ycs_received [YP.block_payload body] }

(* The state reached after the EOT: only the status flips to FT_Completed. *)
noextract
let eot_next_state (st0:YP.ymodem_client_state) : YP.ymodem_client_state =
  { st0 with YP.ycs_status = FT.FT_Completed }

(* The state reached after a CAN: only the status flips to FT_Aborted. *)
noextract
let can_next_state (st0:YP.ymodem_client_state) : YP.ymodem_client_state =
  { st0 with YP.ycs_status = FT.FT_Aborted }

(* The started state reached by Client_start. *)
noextract
let start_next_state (filename:TCP.bytes) (len:nat) : YP.ymodem_client_state =
  {
    YP.ycs_filename = Some filename;
    YP.ycs_len      = len;
    YP.ycs_received = [];
    YP.ycs_status   = FT.FT_InProgress;
  }

(* ── ACK output-byte helpers ──────────────────────────────────────────────── *)

(* The serialized wire output of an ACK step is the single byte 0x06. *)
let lemma_ack_produced ()
  : Lemma (WF.serialize_all ymodem_wire_format ack_wire_outputs == Seq.create 1 6uy)
=
  lemma_serialize_all_control (Body_ack ())

(* Writing 0x06 at index 0 of a nonempty output buffer discharges `output_written`
   for the serialized ACK. *)
let lemma_ack_output_written (out_bytes:TCP.bytes)
  : Lemma
      (requires Seq.length out_bytes >= 1 /\ Seq.index out_bytes 0 == 6uy)
      (ensures
        CPI.output_written out_bytes 1sz
          (WF.serialize_all ymodem_wire_format ack_wire_outputs))
=
  lemma_ack_produced ();
  Seq.lemma_index_create 1 6uy 0;
  Seq.lemma_eq_intro (CPI.output_prefix out_bytes 1sz) (Seq.create 1 6uy)

(* The serialized wire output of a no-output step is empty; `output_written`
   holds for produced-length 0 against any buffer. *)
let lemma_empty_output_written (out_bytes:TCP.bytes)
  : Lemma
      (ensures
        CPI.output_written out_bytes 0sz
          (WF.serialize_all ymodem_wire_format no_wire_outputs))
=
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  Seq.lemma_eq_intro (CPI.output_prefix out_bytes 0sz) Seq.empty

(* ───────────────────────────────────────────────────────────────────────────
   Message identification from an observed (length, lead-byte)

   The Pulse `process_network` observes the input as one complete framed message
   — a 133-byte SOH frame or a 1-byte control frame — WITHOUT assuming it is well
   formed.  These pure lemmas recover the concrete message identity from a
   *parse* (the SOH case, via the verified reader) or directly from the observed
   length and lead byte (the control cases), so the caller never needs an erased
   `msg` witness and unrecognized frames are handled soundly.
   ─────────────────────────────────────────────────────────────────────────── *)

(* A serialized SOH data block is exactly 133 bytes long. *)
let lemma_soh_serialize_length (body:ymodem_soh_body)
  : Lemma (Seq.length (ymodem_serialize (Body_soh body)) == 133)
=
  ymodem_message_bytesize_eq (Body_soh body)

(* If the whole input is a serialized message and it parses as a SOH block, then
   that message *is* the SOH block (parse∘serialize is injective). *)
let lemma_input_is_serialize_soh
  (input:TCP.bytes) (body:ymodem_soh_body) (rest:TCP.bytes)
  : Lemma
      (requires
        ymodem_parse input == Some (Body_soh body, rest) /\
        Seq.length input == 133)
      (ensures input == ymodem_serialize (Body_soh body) /\ rest == Seq.empty)
=
  lemma_ymodem_parse_implies_serialize input (Body_soh body) rest;
  lemma_soh_serialize_length body;
  Seq.lemma_len_append (ymodem_serialize (Body_soh body)) rest;
  Seq.lemma_eq_elim rest Seq.empty;
  Seq.append_empty_r (ymodem_serialize (Body_soh body));
  Seq.lemma_eq_elim input (ymodem_serialize (Body_soh body))

(* If the whole input is a serialized message of length one whose single byte is
   the EOT control byte 0x04, then that message is `Body_eot ()`. *)
let lemma_input_is_serialize_eot (input:TCP.bytes)
  : Lemma
      (requires
        Seq.length input == 1 /\ Seq.index input 0 == 4uy)
      (ensures input == ymodem_serialize (Body_eot ()))
=
  lemma_serialize_control (Body_eot ());
  Seq.lemma_index_create 1 4uy 0;
  Seq.lemma_eq_elim input (Seq.create 1 4uy)

(* If the whole input is a serialized message of length one whose single byte is
   the CAN control byte 0x18, then that message is `Body_can ()`. *)
let lemma_input_is_serialize_can (input:TCP.bytes)
  : Lemma
      (requires
        Seq.length input == 1 /\ Seq.index input 0 == 24uy)
      (ensures input == ymodem_serialize (Body_can ()))
=
  lemma_serialize_control (Body_can ());
  Seq.lemma_index_create 1 24uy 0;
  Seq.lemma_eq_elim input (Seq.create 1 24uy)

(* Serialized-length facts for the control frames actually consumed. *)
let lemma_eot_serialize_length ()
  : Lemma (Seq.length (ymodem_serialize (Body_eot ())) == 1)
=
  lemma_serialize_control (Body_eot ())

let lemma_can_serialize_length ()
  : Lemma (Seq.length (ymodem_serialize (Body_can ())) == 1)
=
  lemma_serialize_control (Body_can ())

(* ───────────────────────────────────────────────────────────────────────────
   Step-witnesses: the four enabled spec transitions
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_soh_step (st0:YP.ymodem_client_state) (body:ymodem_soh_body)
  : Lemma
      (requires Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures
        YP.ymodem_client_step st0 (SM.WireEvent (Body_soh body))
          (soh_next_state st0 body) ack_output)
=
  ()

let lemma_eot_step (st0:YP.ymodem_client_state)
  : Lemma
      (requires Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures
        YP.ymodem_client_step st0 (SM.WireEvent (Body_eot ()))
          (eot_next_state st0) ack_output)
=
  ()

let lemma_can_step (st0:YP.ymodem_client_state)
  : Lemma
      (requires Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures
        YP.ymodem_client_step st0 (SM.WireEvent (Body_can ()))
          (can_next_state st0) empty_output)
=
  ()

let lemma_start_step (st0:YP.ymodem_client_state) (filename:TCP.bytes) (len:nat)
  : Lemma
      (requires st0.YP.ycs_filename == None)
      (ensures
        YP.ymodem_client_step st0 (SM.LocalEvent (YP.Client_start filename len))
          (start_next_state filename len) empty_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas: re-establish `client_trace_ok` and expose `yc_step_rel`
   (the monotone step used to advance the ghost reference) for each transition.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_yc_soh_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state) (body:ymodem_soh_body)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (ymodem_serialize (Body_soh body)) in
        let sent1 = Seq.append sent0 (Seq.create 1 6uy) in
        let st1 = soh_next_state st0 body in
        client_trace_ok received1 sent1 (mk_log received1 sent1 st1) /\
        yc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)))
=
  let st1 = soh_next_state st0 body in
  lemma_soh_step st0 body;
  lemma_ym_serialize_all_singleton (Body_soh body);
  lemma_ack_produced ();
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.WireEvent (Body_soh body)) st1 ack_output;
  let received1 = Seq.append received0 (ymodem_serialize (Body_soh body)) in
  let sent1 = Seq.append sent0 (Seq.create 1 6uy) in
  lemma_yc_step_rel_intro
    (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)
    (SM.WireEvent (Body_soh body)) ack_output

let lemma_yc_eot_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (ymodem_serialize (Body_eot ())) in
        let sent1 = Seq.append sent0 (Seq.create 1 6uy) in
        let st1 = eot_next_state st0 in
        client_trace_ok received1 sent1 (mk_log received1 sent1 st1) /\
        yc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)))
=
  let st1 = eot_next_state st0 in
  lemma_eot_step st0;
  lemma_ym_serialize_all_singleton (Body_eot ());
  lemma_ack_produced ();
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.WireEvent (Body_eot ())) st1 ack_output;
  let received1 = Seq.append received0 (ymodem_serialize (Body_eot ())) in
  let sent1 = Seq.append sent0 (Seq.create 1 6uy) in
  lemma_yc_step_rel_intro
    (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)
    (SM.WireEvent (Body_eot ())) ack_output

let lemma_yc_can_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (ymodem_serialize (Body_can ())) in
        let st1 = can_next_state st0 in
        client_trace_ok received1 sent0 (mk_log received1 sent0 st1) /\
        yc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)))
=
  let st1 = can_next_state st0 in
  lemma_can_step st0;
  lemma_ym_serialize_all_singleton (Body_can ());
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.WireEvent (Body_can ())) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (ymodem_serialize (Body_can ())) in
  lemma_yc_step_rel_intro
    (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Body_can ())) empty_output

let lemma_yc_start_advance
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (filename:TCP.bytes) (len:nat)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.YP.ycs_filename == None)
      (ensures (
        let st1 = start_next_state filename len in
        client_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        yc_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = start_next_state filename len in
  lemma_start_step st0 filename len;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (YP.Client_start filename len)) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_yc_step_rel_intro
    (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (YP.Client_start filename len)) empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Process-correctness packaging (the pure postconditions of the class handlers)
   ─────────────────────────────────────────────────────────────────────────── *)

(* SOH data block received: a genuine StepOk that consumes the 133-byte frame,
   appends the payload, and emits a single ACK byte. *)
let lemma_yc_network_soh_step_ok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (received1 sent1:TCP.bytes) (st1:YP.ymodem_client_state)
  (body:ymodem_soh_body)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == ymodem_serialize (Body_soh body) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress /\
        Seq.length out_bytes >= 1 /\ Seq.index out_bytes 0 == 6uy /\
        st1 == soh_next_state st0 body /\
        Seq.equal received1 (Seq.append received0 input) /\
        Seq.equal sent1 (Seq.append sent0 (Seq.create 1 6uy)))
      (ensures
        CPI.network_process_correct
          YP.ymodem_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          soh_result
          received1 sent1 st1
          input
          ack_wire_outputs no_local_outputs)
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_soh_serialize_length body;
  lemma_ymodem_parse_serialize_exact (Body_soh body);
  Seq.append_empty_r input;
  lemma_soh_step st0 body;
  lemma_ack_produced ();
  lemma_ack_output_written out_bytes;
  assert (CPI.step_output ack_wire_outputs no_local_outputs == ack_output);
  assert_norm (soh_result.CPI.process_status == CPI.StepOk);
  assert_norm (soh_result.CPI.process_consumed_len == 133sz);
  assert_norm (soh_result.CPI.process_produced_len == 1sz);
  introduce exists (msg':ymodem_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      YP.ymodem_client_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v soh_result.CPI.process_consumed_len == Seq.length input /\
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output ack_wire_outputs no_local_outputs) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format ack_wire_outputs) /\
    CPI.output_written out_bytes soh_result.CPI.process_produced_len produced' /\
    Seq.equal received1 (Seq.append received0 input) /\
    Seq.equal sent1 (Seq.append sent0 produced')
  with (Body_soh body) Seq.empty (Seq.create 1 6uy)
  and ();
  match soh_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct
      YP.ymodem_client_wfsm
      input input_len old_out out_bytes out_len
      received0 sent0 st0
      soh_result received1 sent1 st1
      input ack_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%soh_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* EOT received: a genuine StepOk that consumes the 1-byte control frame, flips
   the status to Completed, and emits a single ACK byte. *)
let lemma_yc_network_eot_step_ok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (received1 sent1:TCP.bytes) (st1:YP.ymodem_client_state)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == ymodem_serialize (Body_eot ()) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress /\
        Seq.length out_bytes >= 1 /\ Seq.index out_bytes 0 == 6uy /\
        st1 == eot_next_state st0 /\
        Seq.equal received1 (Seq.append received0 input) /\
        Seq.equal sent1 (Seq.append sent0 (Seq.create 1 6uy)))
      (ensures
        CPI.network_process_correct
          YP.ymodem_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          eot_result
          received1 sent1 st1
          input
          ack_wire_outputs no_local_outputs)
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_eot_serialize_length ();
  lemma_ymodem_parse_serialize_exact (Body_eot ());
  Seq.append_empty_r input;
  lemma_eot_step st0;
  lemma_ack_produced ();
  lemma_ack_output_written out_bytes;
  assert (CPI.step_output ack_wire_outputs no_local_outputs == ack_output);
  assert_norm (eot_result.CPI.process_status == CPI.StepOk);
  assert_norm (eot_result.CPI.process_consumed_len == 1sz);
  assert_norm (eot_result.CPI.process_produced_len == 1sz);
  introduce exists (msg':ymodem_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      YP.ymodem_client_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v eot_result.CPI.process_consumed_len == Seq.length input /\
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output ack_wire_outputs no_local_outputs) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format ack_wire_outputs) /\
    CPI.output_written out_bytes eot_result.CPI.process_produced_len produced' /\
    Seq.equal received1 (Seq.append received0 input) /\
    Seq.equal sent1 (Seq.append sent0 produced')
  with (Body_eot ()) Seq.empty (Seq.create 1 6uy)
  and ();
  match eot_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct
      YP.ymodem_client_wfsm
      input input_len old_out out_bytes out_len
      received0 sent0 st0
      eot_result received1 sent1 st1
      input ack_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%eot_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* CAN received: a genuine StepOk that consumes the 1-byte control frame, flips
   the status to Aborted, and emits NOTHING. *)
let lemma_yc_network_can_step_ok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (received1 sent1:TCP.bytes) (st1:YP.ymodem_client_state)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == ymodem_serialize (Body_can ()) /\
        Some? st0.YP.ycs_filename /\ st0.YP.ycs_status == FT.FT_InProgress /\
        st1 == can_next_state st0 /\
        Seq.equal received1 (Seq.append received0 input) /\
        Seq.equal sent1 sent0)
      (ensures
        CPI.network_process_correct
          YP.ymodem_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          can_result
          received1 sent1 st1
          input
          no_wire_outputs no_local_outputs)
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_can_serialize_length ();
  lemma_ymodem_parse_serialize_exact (Body_can ());
  Seq.append_empty_r input;
  lemma_can_step st0;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_empty_output_written out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.step_output no_wire_outputs no_local_outputs == empty_output);
  assert_norm (can_result.CPI.process_status == CPI.StepOk);
  assert_norm (can_result.CPI.process_consumed_len == 1sz);
  assert_norm (can_result.CPI.process_produced_len == 0sz);
  introduce exists (msg':ymodem_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      YP.ymodem_client_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v can_result.CPI.process_consumed_len == Seq.length input /\
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output no_wire_outputs no_local_outputs) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format no_wire_outputs) /\
    CPI.output_written out_bytes can_result.CPI.process_produced_len produced' /\
    Seq.equal received1 (Seq.append received0 input) /\
    Seq.equal sent1 (Seq.append sent0 produced')
  with (Body_can ()) Seq.empty Seq.empty
  and ();
  match can_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct
      YP.ymodem_client_wfsm
      input input_len old_out out_bytes out_len
      received0 sent0 st0
      can_result received1 sent1 st1
      input no_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%can_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* A refused wire input (a message that parses but is not enabled — ACK/NAK/'C',
   or any input once completed/aborted): a sound IllegalTransition no-op, via the
   third disjunct of `network_error_refines_state_machine`. *)
let lemma_yc_network_noop
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.network_process_correct
          YP.ymodem_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          illegal_result
          received0 sent0 st0
          Seq.empty
          no_wire_outputs no_local_outputs)
=
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_empty_output_written out_bytes;
  Seq.append_empty_r sent0;
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (CPI.network_error_refines_state_machine
    YP.ymodem_client_wfsm (CPI.input_bytes input input_len) st0 st0
    Seq.empty no_wire_outputs no_local_outputs);
  assert_norm (illegal_result.CPI.process_status == CPI.IllegalTransition);
  assert_norm (illegal_result.CPI.process_consumed_len == 0sz);
  assert_norm (illegal_result.CPI.process_produced_len == 0sz);
  introduce exists (produced':TCP.bytes).
    SZ.v illegal_result.CPI.process_consumed_len == Seq.length (Seq.empty <: TCP.bytes) /\
    CPI.network_error_refines_state_machine
      YP.ymodem_client_wfsm (CPI.input_bytes input input_len) st0 st0
      Seq.empty no_wire_outputs no_local_outputs /\
    Seq.equal produced' (WF.serialize_all ymodem_wire_format no_wire_outputs) /\
    CPI.output_written out_bytes illegal_result.CPI.process_produced_len produced' /\
    Seq.equal received0 (Seq.append received0 (Seq.empty <: TCP.bytes)) /\
    Seq.equal sent0 (Seq.append sent0 produced')
  with Seq.empty
  and ();
  match illegal_result.CPI.process_status with
  | CPI.IllegalTransition ->
    assert (CPI.network_process_correct
      YP.ymodem_client_wfsm
      input input_len old_out out_bytes out_len
      received0 sent0 st0
      illegal_result received0 sent0 st0
      Seq.empty no_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%illegal_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* Client_start local event: a genuine StepOk that initialises the receiver
   (sets the filename, keeps the histories) and produces nothing. *)
let lemma_yc_local_start_step_ok
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (st1:YP.ymodem_client_state) (filename:TCP.bytes) (len:nat)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        st0.YP.ycs_filename == None /\
        st1 == start_next_state filename len)
      (ensures
        CPI.local_process_correct
          YP.ymodem_client_wfsm
          (YP.Client_start filename len) old_out out_bytes out_len
          received0 sent0 st0
          start_result
          received0 sent0 st1
          no_wire_outputs no_local_outputs)
=
  lemma_start_step st0 filename len;
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_empty_output_written out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.step_output no_wire_outputs no_local_outputs == empty_output);
  assert_norm (start_result.CPI.process_status == CPI.StepOk);
  assert_norm (start_result.CPI.process_consumed_len == 0sz);
  assert_norm (start_result.CPI.process_produced_len == 0sz);
  introduce exists (produced':TCP.bytes).
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.LocalEvent (YP.Client_start filename len)) st1
      (CPI.step_output no_wire_outputs no_local_outputs) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format no_wire_outputs) /\
    CPI.output_written out_bytes start_result.CPI.process_produced_len produced' /\
    Seq.equal received0 received0 /\
    Seq.equal sent0 (Seq.append sent0 produced')
  with Seq.empty
  and ();
  match start_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.local_process_correct
      YP.ymodem_client_wfsm
      (YP.Client_start filename len) old_out out_bytes out_len
      received0 sent0 st0
      start_result received0 sent0 st1
      no_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.local_process_correct;
           `%start_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* A refused local event (Client_start once the filename is known): a sound
   IllegalTransition no-op, via the "no change" disjunct of
   `local_error_refines_state_machine`. *)
let lemma_yc_local_illegal
  (ev:YP.ymodem_client_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct
          YP.ymodem_client_wfsm
          ev old_out out_bytes out_len
          received0 sent0 st0
          illegal_result
          received0 sent0 st0
          no_wire_outputs no_local_outputs)
=
  assert (WF.serialize_all ymodem_wire_format no_wire_outputs == Seq.empty);
  lemma_empty_output_written out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine
    YP.ymodem_client_wfsm st0 st0 no_wire_outputs no_local_outputs);
  assert_norm (illegal_result.CPI.process_status == CPI.IllegalTransition);
  assert_norm (illegal_result.CPI.process_consumed_len == 0sz);
  assert_norm (illegal_result.CPI.process_produced_len == 0sz);
  introduce exists (produced':TCP.bytes).
    CPI.local_error_refines_state_machine
      YP.ymodem_client_wfsm st0 st0 no_wire_outputs no_local_outputs /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format no_wire_outputs) /\
    CPI.output_written out_bytes illegal_result.CPI.process_produced_len produced' /\
    Seq.equal received0 received0 /\
    Seq.equal sent0 (Seq.append sent0 produced')
  with Seq.empty
  and ();
  match illegal_result.CPI.process_status with
  | CPI.IllegalTransition ->
    assert (CPI.local_process_correct
      YP.ymodem_client_wfsm
      ev old_out out_bytes out_len
      received0 sent0 st0
      illegal_result received0 sent0 st0
      no_wire_outputs no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.local_process_correct;
           `%illegal_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* ───────────────────────────────────────────────────────────────────────────
   Ghost extraction of the parsed SOH body

   The Pulse `process_network` SOH branch gets, from the verified codec leaf, an
   *existential* `exists body rest. ymodem_parse input == Some (Body_soh body, _)`.
   To advance the ghost state it needs a *named* body.  This total ghost function
   extracts it; `lemma_soh_parsed` proves that, under the frame guard, the input
   is exactly the serialization of `Body_soh` of that extracted body.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let ymodem_default_soh_body : ymodem_soh_body =
  { blk = 0uy; blk_complement = 0uy; data = Seq.create 128 0uy; crc = 0us }

noextract
let ymodem_parsed_soh_body (input:TCP.bytes) : GTot ymodem_soh_body =
  match ymodem_parse input with
  | Some (Body_soh body, _) -> body
  | _ -> ymodem_default_soh_body

let lemma_soh_parsed (input:TCP.bytes)
  : Lemma
      (requires
        (exists (body:ymodem_soh_body) (rest:TCP.bytes).
           ymodem_parse input == Some (Body_soh body, rest)) /\
        Seq.length input == 133)
      (ensures input == ymodem_serialize (Body_soh (ymodem_parsed_soh_body input)))
=
  eliminate exists (body:ymodem_soh_body) (rest:TCP.bytes).
    ymodem_parse input == Some (Body_soh body, rest)
  returns input == ymodem_serialize (Body_soh (ymodem_parsed_soh_body input))
  with _pf. lemma_input_is_serialize_soh input body rest
