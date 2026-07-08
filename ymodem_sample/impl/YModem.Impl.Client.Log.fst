module YModem.Impl.Client.Log

(**
  Pure ghost-log / reachable-trace machinery for the YMODEM *client* (receiver)
  `Common.ProtocolImplementation.protocol_implementation` instance.

  This is the receiver analogue of `Calc.Log` + the trace lemmas of
  `Calc.Server.CanonicalProtocol`: it bundles the receiver's wire history
  (`ycl_received`), its (always empty) wire output (`ycl_sent`) and its abstract
  spec state (`ycl_state`) into a `ymodem_client_log`, equips it with the
  reflexive–transitive closure of a single-`WireEvent` step relation as a
  monotonicity preorder, and proves the closure lemmas
  (`state_ahead` / `histories_ahead`) plus the canonical reachable-trace
  invariant (`client_trace_ok`) that refines a byte history into a valid state
  machine trace (`valid_byte_trace`).

  All of this is pure F* (no Pulse); the Pulse instance in
  `YModem.Impl.Client.CanonicalProtocol` allocates a monotonic ghost reference
  over `yc_state_ahead_preorder` and folds `client_trace_ok` into its invariant.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module ID = FStar.IndefiniteDescription
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module LP = LowParse.Spec
module SZ = FStar.SizeT

module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP = Common.TCP
module CPI = Common.ProtocolImplementation
module FT = Common.FileTransfer

module YP = YModem.Protocol

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

(* ───────────────────────────────────────────────────────────────────────────
   The receiver ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_log = {
  ycl_received : TCP.bytes;                 // all data-packet bytes received
  ycl_sent     : TCP.bytes;                 // wire output (always Seq.empty)
  ycl_state    : YP.ymodem_client_state;    // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
let mk_log (received sent:TCP.bytes) (st:YP.ymodem_client_state) : ymodem_client_log =
  { ycl_received = received; ycl_sent = sent; ycl_state = st }

(* A junk packet, used only to make the parsed-packet projection total. *)
let default_ymodem_packet : ymodem_packet =
  {
    soh            = 0uy;
    blk            = 0uy;
    blk_complement = 0uy;
    data           = Seq.create 128 0uy;
    crc            = 0us;
  }

(* Total projection of the packet a data-frame parses to. *)
let ymodem_parsed_packet (input:TCP.bytes) : GTot ymodem_packet =
  match ymodem_parse input with
  | Some (pkt, _) -> pkt
  | None -> default_ymodem_packet

(* The receiver emits no wire output, so every WireEvent carries the empty
   step output. *)
let yc_empty_output : SM.step_output ymodem_packet unit =
  { SM.so_wire_outputs = []; SM.so_local_outputs = [] }

let client_trace =
  list (SM.transition YP.ymodem_client_state ymodem_packet YP.ymodem_client_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   Round-trip: a 133-byte data packet that parses to `pkt` equals its
   serialization.  This is what lets the growing `received` history stay the
   canonical serialization of the received packet list.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_ymodem_input_is_serialize
  (input:TCP.bytes) (pkt:ymodem_packet) (rest:TCP.bytes)
  : Lemma
      (requires Seq.length input == 133 /\ ymodem_parse input == Some (pkt, rest))
      (ensures Seq.equal input (ymodem_serialize pkt) /\ Seq.equal rest Seq.empty)
=
  LP.serializer_correct_implies_complete ymodem_packet_parser ymodem_packet_serializer;
  let Some (_v, consumed) = LP.parse ymodem_packet_parser input in
  assert (LP.serialize ymodem_packet_serializer pkt == Seq.slice input 0 consumed);
  ymodem_packet_bytesize_eqn pkt;
  ymodem_packet_data_bytesize_eqn pkt.data;
  assert (Seq.length (LP.serialize ymodem_packet_serializer pkt) == 133);
  Seq.lemma_len_slice input 0 consumed;
  assert (consumed == 133);
  Seq.lemma_eq_intro input (Seq.slice input 0 133);
  Seq.lemma_eq_intro rest Seq.empty

(* Bridge `ymodem_client_recv_block`'s existential postcondition into a concrete
   ghost packet: the parsed packet is `ymodem_parsed_packet input`, it consumes
   the whole 133-byte frame, and the frame bytes are exactly its serialization. *)
let lemma_recv_block_packet (input o':TCP.bytes)
  : Lemma
      (requires
        Seq.length input == 133 /\
        (exists (pkt:ymodem_packet) (rest:TCP.bytes).
           ymodem_parse input == Some (pkt, rest) /\ o' == pkt.data))
      (ensures (
        let pkt = ymodem_parsed_packet input in
        ymodem_parse input == Some (pkt, Seq.empty) /\
        o' == pkt.data /\
        Seq.equal input (ymodem_serialize pkt)))
=
  let pv = ymodem_parse input in
  let pkt = ymodem_parsed_packet input in
  let rest = snd (Some?.v pv) in
  assert (pv == Some (pkt, rest));
  lemma_ymodem_input_is_serialize input pkt rest;
  Seq.lemma_eq_elim rest Seq.empty

(* ───────────────────────────────────────────────────────────────────────────
   serialize_all distributes over list append (specialised to ymodem_wire_format)
   ─────────────────────────────────────────────────────────────────────────── *)

let rec lemma_ym_serialize_all_append
  (msgs0 msgs1:list ymodem_packet)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all ymodem_wire_format (L.append msgs0 msgs1))
          (Seq.append
            (WF.serialize_all ymodem_wire_format msgs0)
            (WF.serialize_all ymodem_wire_format msgs1)))
      (decreases msgs0)
=
  match msgs0 with
  | [] ->
    Seq.append_empty_l (WF.serialize_all ymodem_wire_format msgs1)
  | msg :: rest ->
    lemma_ym_serialize_all_append rest msgs1;
    Seq.append_assoc
      (ymodem_serialize msg)
      (WF.serialize_all ymodem_wire_format rest)
      (WF.serialize_all ymodem_wire_format msgs1)

(* serialize_all of a singleton is just the serialization of that element. *)
let lemma_ym_serialize_all_singleton (msg:ymodem_packet)
  : Lemma (Seq.equal (WF.serialize_all ymodem_wire_format [msg]) (ymodem_serialize msg))
=
  Seq.append_empty_r (ymodem_serialize msg)

(* ───────────────────────────────────────────────────────────────────────────
   trace_input_messages / trace_wire_outputs grow by one transition
   ─────────────────────────────────────────────────────────────────────────── *)

let rec lemma_ym_trace_input_bytes_append_one
  (trace:client_trace)
  (tr:SM.transition YP.ymodem_client_state ymodem_packet YP.ymodem_client_local unit)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages (L.append trace [tr])))
          (Seq.append
            (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace))
            (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages tr.SM.tr_event))))
      (decreases trace)
=
  match trace with
  | [] ->
    lemma_ym_serialize_all_append (WFSM.event_input_messages tr.SM.tr_event) [];
    Seq.lemma_eq_elim
      (WF.serialize_all ymodem_wire_format (L.append (WFSM.event_input_messages tr.SM.tr_event) []))
      (Seq.append
        (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages tr.SM.tr_event))
        (WF.serialize_all ymodem_wire_format []))
  | hd :: rest ->
    lemma_ym_trace_input_bytes_append_one rest tr;
    lemma_ym_serialize_all_append
      (WFSM.event_input_messages hd.SM.tr_event)
      (WFSM.trace_input_messages (L.append rest [tr]));
    lemma_ym_serialize_all_append
      (WFSM.event_input_messages hd.SM.tr_event)
      (WFSM.trace_input_messages rest);
    Seq.append_assoc
      (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages hd.SM.tr_event))
      (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages rest))
      (WF.serialize_all ymodem_wire_format (WFSM.event_input_messages tr.SM.tr_event))

let rec lemma_ym_trace_wire_bytes_append_one
  (trace:client_trace)
  (tr:SM.transition YP.ymodem_client_state ymodem_packet YP.ymodem_client_local unit)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs (L.append trace [tr])))
          (Seq.append
            (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace))
            (WF.serialize_all ymodem_wire_format tr.SM.tr_output.SM.so_wire_outputs)))
      (decreases trace)
=
  match trace with
  | [] ->
    lemma_ym_serialize_all_append tr.SM.tr_output.SM.so_wire_outputs [];
    Seq.lemma_eq_elim
      (WF.serialize_all ymodem_wire_format (L.append tr.SM.tr_output.SM.so_wire_outputs []))
      (Seq.append
        (WF.serialize_all ymodem_wire_format tr.SM.tr_output.SM.so_wire_outputs)
        (WF.serialize_all ymodem_wire_format []))
  | hd :: rest ->
    lemma_ym_trace_wire_bytes_append_one rest tr;
    lemma_ym_serialize_all_append
      hd.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs (L.append rest [tr]));
    lemma_ym_serialize_all_append
      hd.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    Seq.append_assoc
      (WF.serialize_all ymodem_wire_format hd.SM.tr_output.SM.so_wire_outputs)
      (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs rest))
      (WF.serialize_all ymodem_wire_format tr.SM.tr_output.SM.so_wire_outputs)

(* ───────────────────────────────────────────────────────────────────────────
   Single-WireEvent step relation + its RTC-closure preorder
   ─────────────────────────────────────────────────────────────────────────── *)

let yc_wire_step_ok
  (log0:ymodem_client_log)
  (pkt:ymodem_packet)
  (log1:ymodem_client_log)
  : prop =
  YP.ymodem_client_step log0.ycl_state (SM.WireEvent pkt) log1.ycl_state yc_empty_output /\
  Seq.equal log1.ycl_received (Seq.append log0.ycl_received (ymodem_serialize pkt)) /\
  Seq.equal log1.ycl_sent log0.ycl_sent

let yc_step_rel (log0 log1:ymodem_client_log) : prop =
  exists pkt. yc_wire_step_ok log0 pkt log1

let yc_state_ahead_preorder : Pre.preorder ymodem_client_log =
  RTC.closure yc_step_rel

let yc_transition
  (log0:ymodem_client_log)
  (pkt:ymodem_packet)
  (log1:ymodem_client_log)
  : SM.transition YP.ymodem_client_state ymodem_packet YP.ymodem_client_local unit =
  {
    SM.tr_event = SM.WireEvent pkt;
    SM.tr_next_state = log1.ycl_state;
    SM.tr_output = yc_empty_output;
  }

(* ── state_ahead closure ─────────────────────────────────────────────────── *)

let lemma_yc_step_rel_state_ahead
  (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_step_rel log0 log1)
      (ensures CPI.state_ahead YP.ymodem_client_wfsm log0.ycl_state log1.ycl_state)
=
  let pkt =
    ID.indefinite_description_ghost
      ymodem_packet
      (fun pkt -> yc_wire_step_ok log0 pkt log1) in
  let tr = yc_transition log0 pkt log1 in
  assert (SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    log0.ycl_state
    [tr]
    log1.ycl_state);
  assert (exists trace.
    SM.trace_reaches
      YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
      log0.ycl_state
      trace
      log1.ycl_state)

let lemma_yc_closure_state_ahead
  (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead YP.ymodem_client_wfsm log0.ycl_state log1.ycl_state)
=
  RTC.induct
    yc_step_rel
    (fun x y -> CPI.state_ahead YP.ymodem_client_wfsm x.ycl_state y.ycl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
        x.ycl_state)
    (fun x y -> lemma_yc_step_rel_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
        x.ycl_state
        y.ycl_state
        z.ycl_state)
    log0
    log1
    ()

(* ── histories_ahead closure ─────────────────────────────────────────────── *)

let lemma_yc_step_rel_histories_ahead
  (log0 log1:ymodem_client_log)
  : Lemma
      (requires yc_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.ycl_received log1.ycl_received /\
        TCP.bytes_extends log0.ycl_sent log1.ycl_sent)
=
  let pkt =
    ID.indefinite_description_ghost
      ymodem_packet
      (fun pkt -> yc_wire_step_ok log0 pkt log1) in
  CPI.lemma_bytes_extends_append_equal
    log0.ycl_received
    log1.ycl_received
    (ymodem_serialize pkt);
  Seq.lemma_eq_elim log1.ycl_sent log0.ycl_sent;
  CPI.lemma_bytes_extends_refl log0.ycl_sent

let lemma_yc_closure_histories_ahead
  (log0 log1:ymodem_client_log)
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
    (fun x y -> lemma_yc_step_rel_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.ycl_received y.ycl_received z.ycl_received;
      CPI.lemma_bytes_extends_trans x.ycl_sent y.ycl_sent z.ycl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

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

(* The initial (freshly-started) receiver log: reached by a single
   YmodemClientStart local event, so its received/sent histories are empty. *)
let started_log (filename:TCP.bytes) (len:nat) : ymodem_client_log =
  {
    ycl_received = Seq.empty;
    ycl_sent     = Seq.empty;
    ycl_state    = {
      YP.ycs_filename = Some filename;
      YP.ycs_len      = len;
      YP.ycs_received = [];
      YP.ycs_status   = FT.FT_InProgress;
    };
  }

let start_transition (filename:TCP.bytes) (len:nat)
  : SM.transition YP.ymodem_client_state ymodem_packet YP.ymodem_client_local unit =
  {
    SM.tr_event = SM.LocalEvent (YP.YmodemClientStart filename len);
    SM.tr_next_state = (started_log filename len).ycl_state;
    SM.tr_output = yc_empty_output;
  }

let lemma_started_trace_ok (filename:TCP.bytes) (len:nat)
  : Lemma (client_trace_ok Seq.empty Seq.empty (started_log filename len))
=
  let tr = start_transition filename len in
  let trace : client_trace = [tr] in
  assert (SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_client_initial
    trace
    (started_log filename len).ycl_state);
  assert (WFSM.trace_input_messages trace == []);
  assert (SM.trace_wire_outputs trace == []);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace));
  assert (client_trace_witness Seq.empty Seq.empty (started_log filename len) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one WireEvent (receive a data packet)
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_client_trace_ok_network_step
  (received0 sent0:TCP.bytes)
  (log0:ymodem_client_log)
  (pkt:ymodem_packet)
  (log1:ymodem_client_log)
  : Lemma
      (requires
        client_trace_ok received0 sent0 log0 /\
        yc_wire_step_ok log0 pkt log1)
      (ensures
        client_trace_ok
          (Seq.append received0 (ymodem_serialize pkt))
          sent0
          log1)
=
  let trace0 =
    ID.indefinite_description_ghost client_trace (client_trace_witness received0 sent0 log0) in
  let tr = yc_transition log0 pkt log1 in
  assert (SM.trace_reaches
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    log0.ycl_state
    [tr]
    log1.ycl_state);
  SM.lemma_trace_reaches_append
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine
    YP.ymodem_client_initial
    log0.ycl_state
    log1.ycl_state
    trace0
    [tr];
  lemma_ym_trace_input_bytes_append_one trace0 tr;
  lemma_ym_trace_wire_bytes_append_one trace0 tr;
  lemma_ym_serialize_all_singleton pkt;
  (* trace_input_messages grows by [pkt]; serialize_all [pkt] == serialize pkt *)
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages trace0));
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace0));
  (* trace_wire_outputs grows by [] (client emits nothing) *)
  Seq.append_empty_r
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs trace0));
  assert (Seq.equal
    (Seq.append received0 (ymodem_serialize pkt))
    (WF.serialize_all ymodem_wire_format (WFSM.trace_input_messages (L.append trace0 [tr]))));
  assert (Seq.equal
    sent0
    (WF.serialize_all ymodem_wire_format (SM.trace_wire_outputs (L.append trace0 [tr]))));
  (* connect to log1 fields *)
  assert (Seq.equal
    (Seq.append received0 (ymodem_serialize pkt))
    log1.ycl_received);
  assert (Seq.equal sent0 log1.ycl_sent);
  assert (client_trace_witness
    (Seq.append received0 (ymodem_serialize pkt))
    sent0
    log1
    (L.append trace0 [tr]))

(* ───────────────────────────────────────────────────────────────────────────
   process_result values and process_correct packaging lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

[@inline_let]
let ymodem_client_process_result
  (status:CPI.process_status) (consumed produced:SZ.t) : CPI.process_result =
  {
    CPI.process_status = status;
    CPI.process_consumed_len = consumed;
    CPI.process_produced_len = produced;
    CPI.process_app_len = 0sz;
  }

(* A received data packet: consumed the whole 133-byte frame, produced no wire
   output (the receiver is silent). *)
[@inline_let]
let ymodem_client_step_ok_result : CPI.process_result =
  ymodem_client_process_result CPI.StepOk 133sz 0sz

(* A refused local event (start-when-started / EOT): a sound no-op. *)
[@inline_let]
let ymodem_client_illegal_result : CPI.process_result =
  ymodem_client_process_result CPI.IllegalTransition 0sz 0sz

let ymodem_no_wire_outputs : list ymodem_packet = []
let ymodem_no_local_outputs : list unit = []

(* The state reached after receiving one data packet. *)
let wire_next_state (st0:YP.ymodem_client_state) (pkt:ymodem_packet)
  : YP.ymodem_client_state =
  { st0 with YP.ycs_received = L.append st0.YP.ycs_received [YP.block_payload pkt] }

(* From the WireEvent guard, the canonical single-step relation holds. *)
let lemma_wire_step_ok
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (pkt:ymodem_packet)
  (received1 sent1:TCP.bytes) (st1:YP.ymodem_client_state)
  : Lemma
      (requires
        Some? st0.YP.ycs_filename /\
        st0.YP.ycs_status == FT.FT_InProgress /\
        st1 == wire_next_state st0 pkt /\
        Seq.equal received1 (Seq.append received0 (ymodem_serialize pkt)) /\
        Seq.equal sent1 sent0)
      (ensures yc_wire_step_ok (mk_log received0 sent0 st0) pkt (mk_log received1 sent1 st1))
=
  ()

(* Package the StepOk obligations of `network_process_correct` for a received
   data packet: consume the 133-byte frame, emit nothing. *)
let lemma_ym_network_process_correct_step_ok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:YP.ymodem_client_state)
  (received1 sent1:TCP.bytes) (st1:YP.ymodem_client_state)
  (pkt:ymodem_packet)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        Seq.length input == 133 /\ SZ.v input_len == 133 /\
        ymodem_parse input == Some (pkt, Seq.empty) /\
        YP.ymodem_client_step st0 (SM.WireEvent pkt) st1 yc_empty_output /\
        Seq.equal received1 (Seq.append received0 input) /\
        Seq.equal sent1 sent0)
      (ensures
        CPI.network_process_correct
          YP.ymodem_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          ymodem_client_step_ok_result
          received1 sent1 st1
          input
          ymodem_no_wire_outputs
          ymodem_no_local_outputs)
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  Seq.append_empty_r input;
  assert (YP.ymodem_client_wfsm.WFSM.wfsm_wire_format == ymodem_wire_format);
  assert (CPI.consumed_by_parse
    YP.ymodem_client_wfsm.WFSM.wfsm_wire_format (CPI.input_bytes input input_len) pkt input Seq.empty);
  assert (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format ymodem_no_wire_outputs == Seq.empty);
  assert (CPI.output_written out_bytes 0sz Seq.empty);
  Seq.append_empty_r sent0;
  assert (CPI.step_output ymodem_no_wire_outputs ymodem_no_local_outputs == yc_empty_output);
  assert (YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
    st0 (SM.WireEvent pkt) st1
    (CPI.step_output ymodem_no_wire_outputs ymodem_no_local_outputs));
  assert_norm (ymodem_client_step_ok_result.CPI.process_status == CPI.StepOk);
  assert_norm (ymodem_client_step_ok_result.CPI.process_consumed_len == 133sz);
  assert_norm (ymodem_client_step_ok_result.CPI.process_produced_len == 0sz);
  assert (SZ.v 133sz == 133);
  assert (SZ.v ymodem_client_step_ok_result.CPI.process_consumed_len == Seq.length input);
  assert (CPI.output_written out_bytes ymodem_client_step_ok_result.CPI.process_produced_len Seq.empty);
  assert (Seq.equal Seq.empty (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format ymodem_no_wire_outputs));
  assert (Seq.equal sent1 (Seq.append sent0 Seq.empty));
  introduce exists (msg':ymodem_packet) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      YP.ymodem_client_wfsm.WFSM.wfsm_wire_format (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v ymodem_client_step_ok_result.CPI.process_consumed_len == Seq.length input /\
    YP.ymodem_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output ymodem_no_wire_outputs ymodem_no_local_outputs) /\
    Seq.equal produced' (WF.serialize_all YP.ymodem_client_wfsm.WFSM.wfsm_wire_format ymodem_no_wire_outputs) /\
    CPI.output_written out_bytes ymodem_client_step_ok_result.CPI.process_produced_len produced' /\
    Seq.equal received1 (Seq.append received0 input) /\
    Seq.equal sent1 (Seq.append sent0 produced')
  with pkt Seq.empty Seq.empty
  and ();
  match ymodem_client_step_ok_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct
      YP.ymodem_client_wfsm
      input input_len old_out out_bytes out_len
      received0 sent0 st0
      ymodem_client_step_ok_result
      received1 sent1 st1
      input
      ymodem_no_wire_outputs
      ymodem_no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%ymodem_client_step_ok_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

(* Package the IllegalTransition (no-op) obligations of `local_process_correct`:
   the receiver refuses local events (start-when-started / EOT), leaving the
   state and buffers untouched.  Sound because IllegalTransition only asserts a
   state-machine *refinement*, whose "no change" disjunct always holds. *)
let lemma_ym_local_process_correct_illegal
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
          ymodem_client_illegal_result
          received0 sent0 st0
          ymodem_no_wire_outputs
          ymodem_no_local_outputs)
=
  assert (WF.serialize_all ymodem_wire_format ymodem_no_wire_outputs == Seq.empty);
  assert (CPI.output_written out_bytes 0sz Seq.empty);
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine
    YP.ymodem_client_wfsm st0 st0 ymodem_no_wire_outputs ymodem_no_local_outputs);
  assert_norm (ymodem_client_illegal_result.CPI.process_status == CPI.IllegalTransition);
  assert_norm (ymodem_client_illegal_result.CPI.process_consumed_len == 0sz);
  assert_norm (ymodem_client_illegal_result.CPI.process_produced_len == 0sz);
  assert (exists (produced':TCP.bytes).
    CPI.local_error_refines_state_machine
      YP.ymodem_client_wfsm st0 st0 ymodem_no_wire_outputs ymodem_no_local_outputs /\
    Seq.equal produced' (WF.serialize_all ymodem_wire_format ymodem_no_wire_outputs) /\
    CPI.output_written out_bytes ymodem_client_illegal_result.CPI.process_produced_len produced' /\
    Seq.equal received0 received0 /\
    Seq.equal sent0 (Seq.append sent0 produced'));
  match ymodem_client_illegal_result.CPI.process_status with
  | CPI.IllegalTransition ->
    assert (CPI.local_process_correct
      YP.ymodem_client_wfsm
      ev old_out out_bytes out_len
      received0 sent0 st0
      ymodem_client_illegal_result
      received0 sent0 st0
      ymodem_no_wire_outputs
      ymodem_no_local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.local_process_correct;
           `%ymodem_client_illegal_result;
           `%ymodem_client_process_result;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_status;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Common.ProtocolImplementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False
