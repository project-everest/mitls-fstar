module HTTP.Impl.Client.Log

(**
  Pure ghost-log / reachable-trace machinery **refining the executable HTTP
  Content-Length body receiver against the spec state machine**
  `HTTP.Protocol.Length.http_client_wfsm`.

  This is the exact dual of `HTTP.Impl.Server.Log`, and the two are deliberately
  symmetric:

    * the SERVER (response sender) consumes no wire input — every
      `SM.WireEvent` maps to `False` — so its `received` history is always
      empty and its `sent` history is the whole story;

    * the CLIENT (body receiver) produces no wire output — every step has
      `so_wire_outputs == []` — so its `sent` history is always empty and its
      `received` history is the whole story.

  Consequently the client discharges the *output* side of
  `Common.WireFormatStateMachine.valid_byte_trace` outright
  (`lemma_client_trace_no_wire_outputs`) and satisfies the *input* side through
  the datagram disjunct: the received byte history is exactly the serialization
  of the consumed body segments, whose boundaries come from the
  Content-Length-driven read sizes rather than from the bytes themselves.  (A
  body segment is not a strong-prefix parser, so `HTTP.Wire.Length` carries no
  `wire_format_stream_laws` instance and the `parses_as` disjunct is not
  available — exactly the situation the datagram disjunct was added for.)

  Capstones proved here:

    * `lemma_client_received_bytes_are_file` — every byte read off the socket is
      accounted for by a reassembled body block, and vice versa;

    * `lemma_client_completed_len` — on `FT_Completed` the reassembly is at
      least the declared Content-Length;

    * `lemma_server_client_agree` / `lemma_end_to_end_transfer` — THE end-to-end
      theorem: if the verified sender's `sent` history is the verified
      receiver's `received` history, the file the receiver reassembles is
      *exactly* the file the sender was serving.  This is the statement that the
      two independently-verified endpoints actually compose.

  All of this is pure F* (no Pulse).  Verified but NOT extracted.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module ID = FStar.IndefiniteDescription
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module SZ = FStar.SizeT
module U8 = FStar.UInt8

module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module TCP = Common.TCP
module CPI = Common.ProtocolImplementation
module FT = Common.FileTransfer

module HP = HTTP.Protocol.Length
module SLog = HTTP.Impl.Server.Log

open HTTP.Wire.Length

#set-options "--fuel 2 --ifuel 2 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   The receiver ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type http_client_log = {
  hcl_received : TCP.bytes;              // all wire bytes received (body segments)
  hcl_sent     : TCP.bytes;              // wire output bytes (always empty: see below)
  hcl_state    : HP.http_client_state;   // abstract spec state
}

noextract
let mk_log (received sent:TCP.bytes) (st:HP.http_client_state) : http_client_log =
  { hcl_received = received; hcl_sent = sent; hcl_state = st }

(* Agreement between the concrete 1-cell status flag carried by the Pulse handle
   and the abstract state.  The receiver has no abort transition, so only three
   values are reachable. *)
noextract
let hc_status_flag_ok (s:U8.t) (st:HP.http_client_state) : prop =
  (s == 0uy /\ st.HP.hcs_status == FT.FT_InProgress /\ st.HP.hcs_filename == None) \/
  (s == 1uy /\ st.HP.hcs_status == FT.FT_InProgress /\ Some? st.HP.hcs_filename) \/
  (s == 2uy /\ st.HP.hcs_status == FT.FT_Completed)

noextract
let client_trace =
  list (SM.transition HP.http_client_state http_message HP.http_client_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   The body receiver is output-free
   ─────────────────────────────────────────────────────────────────────────── *)

let rec lemma_client_trace_no_wire_outputs
  (st0:HP.http_client_state) (trace:client_trace) (st1:HP.http_client_state)
  : Lemma
      (requires SM.trace_reaches HP.http_client_state_machine st0 trace st1)
      (ensures SM.trace_wire_outputs trace == [])
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    assert (HP.http_client_step st0 tr.SM.tr_event tr.SM.tr_next_state tr.SM.tr_output);
    assert (tr.SM.tr_output.SM.so_wire_outputs == []);
    lemma_client_trace_no_wire_outputs tr.SM.tr_next_state rest st1

(* ───────────────────────────────────────────────────────────────────────────
   Single-step relation + its RTC-closure preorder
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let hc_step_body
  (log0 log1:http_client_log)
  (ev:SM.event http_message HP.http_client_local)
  (out:SM.step_output http_message unit)
  : prop =
  HP.http_client_step log0.hcl_state ev log1.hcl_state out /\
  Seq.equal log1.hcl_received
    (Seq.append log0.hcl_received
       (WF.serialize_all http_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.hcl_sent
    (Seq.append log0.hcl_sent
       (WF.serialize_all http_wire_format out.SM.so_wire_outputs))

noextract
let hc_step_rel (log0 log1:http_client_log) : prop =
  exists ev out. hc_step_body log0 log1 ev out

let lemma_hc_step_rel_intro
  (log0 log1:http_client_log)
  (ev:SM.event http_message HP.http_client_local)
  (out:SM.step_output http_message unit)
  : Lemma (requires hc_step_body log0 log1 ev out) (ensures hc_step_rel log0 log1)
=
  ()

noextract
let hc_state_ahead_preorder : Pre.preorder http_client_log =
  RTC.closure hc_step_rel

let lemma_hc_step_state_ahead (log0 log1:http_client_log)
  : Lemma
      (requires hc_step_rel log0 log1)
      (ensures CPI.state_ahead HP.http_client_wfsm log0.hcl_state log1.hcl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event http_message HP.http_client_local)
      (fun ev -> exists out. hc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output http_message unit)
      (fun out -> hc_step_body log0 log1 ev out) in
  let tr : SM.transition HP.http_client_state http_message HP.http_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.hcl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    HP.http_client_wfsm.WFSM.wfsm_state_machine log0.hcl_state [tr] log1.hcl_state);
  assert (exists trace.
    SM.trace_reaches
      HP.http_client_wfsm.WFSM.wfsm_state_machine log0.hcl_state trace log1.hcl_state)

let lemma_hc_closure_state_ahead (log0 log1:http_client_log)
  : Lemma
      (requires hc_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead HP.http_client_wfsm log0.hcl_state log1.hcl_state)
=
  RTC.induct
    hc_step_rel
    (fun x y -> CPI.state_ahead HP.http_client_wfsm x.hcl_state y.hcl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        HP.http_client_wfsm.WFSM.wfsm_state_machine x.hcl_state)
    (fun x y -> lemma_hc_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        HP.http_client_wfsm.WFSM.wfsm_state_machine x.hcl_state y.hcl_state z.hcl_state)
    log0
    log1
    ()

let lemma_hc_step_histories_ahead (log0 log1:http_client_log)
  : Lemma
      (requires hc_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.hcl_received log1.hcl_received /\
        TCP.bytes_extends log0.hcl_sent log1.hcl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event http_message HP.http_client_local)
      (fun ev -> exists out. hc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output http_message unit)
      (fun out -> hc_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.hcl_received log1.hcl_received
    (WF.serialize_all http_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.hcl_sent log1.hcl_sent
    (WF.serialize_all http_wire_format out.SM.so_wire_outputs)

let lemma_hc_closure_histories_ahead (log0 log1:http_client_log)
  : Lemma
      (requires hc_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.hcl_received log1.hcl_received /\
        TCP.bytes_extends log0.hcl_sent log1.hcl_sent)
=
  RTC.induct
    hc_step_rel
    (fun x y ->
      TCP.bytes_extends x.hcl_received y.hcl_received /\
      TCP.bytes_extends x.hcl_sent y.hcl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.hcl_received;
      CPI.lemma_bytes_extends_refl x.hcl_sent)
    (fun x y -> lemma_hc_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.hcl_received y.hcl_received z.hcl_received;
      CPI.lemma_bytes_extends_trans x.hcl_sent y.hcl_sent z.hcl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let client_trace_witness
  (received sent:TCP.bytes)
  (log:http_client_log)
  (trace:client_trace)
  : prop =
  SM.trace_reaches
    HP.http_client_wfsm.WFSM.wfsm_state_machine
    HP.http_client_initial
    trace
    log.hcl_state /\
  Seq.equal
    received
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.hcl_received /\
  Seq.equal sent log.hcl_sent

noextract
let client_trace_ok
  (received sent:TCP.bytes)
  (log:http_client_log)
  : prop =
  exists trace. client_trace_witness received sent log trace

(* The receiver satisfies `valid_byte_trace` through the DATAGRAM disjunct: the
   received bytes are exactly the serialization of the consumed body segments.
   Message boundaries come from the Content-Length-driven read sizes, not from
   the byte stream, which is why the (unavailable) `parses_as` disjunct is not
   needed. *)
let lemma_client_trace_ok_valid
  (received sent:TCP.bytes)
  (log:http_client_log)
  : Lemma
      (requires client_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          HP.http_client_wfsm
          received
          log.hcl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost client_trace (client_trace_witness received sent log) in
  Seq.lemma_eq_elim
    received
    (Seq.append
      (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace))
      Seq.empty);
  assert (exists trace'.
    SM.trace_reaches
      HP.http_client_wfsm.WFSM.wfsm_state_machine
      HP.http_client_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.hcl_state /\
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

(* Corollary: a receiver satisfying the invariant has written nothing. *)
let lemma_client_trace_ok_sent_empty
  (received sent:TCP.bytes)
  (log:http_client_log)
  : Lemma
      (requires client_trace_ok received sent log)
      (ensures Seq.equal sent Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost client_trace (client_trace_witness received sent log) in
  lemma_client_trace_no_wire_outputs HP.http_client_initial trace log.hcl_state

let lemma_client_initial_trace_ok ()
  : Lemma
      (client_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty HP.http_client_initial))
=
  let trace : client_trace = [] in
  assert (SM.trace_reaches
    HP.http_client_wfsm.WFSM.wfsm_state_machine
    HP.http_client_initial
    trace
    HP.http_client_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all http_wire_format (SM.trace_wire_outputs trace));
  assert (client_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty HP.http_client_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_client_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:HP.http_client_state)
  (ev:SM.event http_message HP.http_client_local)
  (st1:HP.http_client_state)
  (out:SM.step_output http_message unit)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        HP.http_client_step st0 ev st1 out)
      (ensures
        client_trace_ok
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
    ID.indefinite_description_ghost client_trace (client_trace_witness received0 sent0 log0) in
  let tr : SM.transition HP.http_client_state http_message HP.http_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches HP.http_client_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    HP.http_client_wfsm.WFSM.wfsm_state_machine
    HP.http_client_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  SLog.lemma_trace_input_messages_append trace0 [tr];
  SLog.lemma_serialize_all_append
    http_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace0));
  L.append_l_nil (WFSM.event_input_messages ev);
  SLog.lemma_trace_wire_outputs_append trace0 [tr];
  SLog.lemma_serialize_all_append
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
  assert (client_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   Next-state helpers and step witnesses
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let client_empty_output : SM.step_output http_message unit =
  { SM.so_wire_outputs = []; SM.so_local_outputs = [] }

(* Client_start binds the target and the declared Content-Length. *)
noextract
let client_start_next_state (filename:TCP.bytes) (len:nat) : HP.http_client_state =
  { HP.hcs_filename = Some filename; HP.hcs_len = len;
    HP.hcs_received = []; HP.hcs_status = FT.FT_InProgress }

(* Receiving a body segment appends it and completes once the declared
   Content-Length has been delivered. *)
noextract
let recv_next_state (st0:HP.http_client_state) (p:body_payload) : HP.http_client_state =
  let rcvd = L.append st0.HP.hcs_received [(p <: TCP.bytes)] in
  { st0 with
    HP.hcs_received = rcvd;
    HP.hcs_status =
      (if Seq.length (FT.ft_concat rcvd) >= st0.HP.hcs_len
       then FT.FT_Completed
       else FT.FT_InProgress) }

let lemma_client_start_step
  (st0:HP.http_client_state) (filename:TCP.bytes) (len:nat)
  : Lemma
      (requires st0.HP.hcs_filename == None)
      (ensures
        HP.http_client_step st0 (SM.LocalEvent (HP.Client_start filename len))
          (client_start_next_state filename len) client_empty_output)
=
  ()

let lemma_recv_step (st0:HP.http_client_state) (p:body_payload)
  : Lemma
      (requires
        Some? st0.HP.hcs_filename /\
        st0.HP.hcs_status == FT.FT_InProgress)
      (ensures
        HP.http_client_step st0 (SM.WireEvent (Msg_body p))
          (recv_next_state st0 p) client_empty_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_client_start_advance
  (received0 sent0:TCP.bytes) (st0:HP.http_client_state)
  (filename:TCP.bytes) (len:nat)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.HP.hcs_filename == None)
      (ensures (
        let st1 = client_start_next_state filename len in
        client_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        hc_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = client_start_next_state filename len in
  lemma_client_start_step st0 filename len;
  assert (WF.serialize_all http_wire_format ([] <: list http_message) == Seq.empty);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (HP.Client_start filename len)) st1 client_empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_hc_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (HP.Client_start filename len)) client_empty_output

let lemma_recv_advance
  (received0 sent0:TCP.bytes) (st0:HP.http_client_state) (p:body_payload)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.HP.hcs_filename /\
        st0.HP.hcs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 p in
        let st1 = recv_next_state st0 p in
        client_trace_ok received1 sent0 (mk_log received1 sent0 st1) /\
        hc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)))
=
  let st1 = recv_next_state st0 p in
  lemma_recv_step st0 p;
  SLog.lemma_serialize_all_body p;
  Seq.lemma_eq_elim
    (WF.serialize_all http_wire_format (WFSM.event_input_messages (SM.WireEvent #http_message #HP.http_client_local (Msg_body p))))
    (p <: TCP.bytes);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.WireEvent (Msg_body p)) st1 client_empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 p in
  lemma_hc_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Msg_body p)) client_empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Capstone: the bytes off the wire ARE the reassembled file
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let client_state_inv (st:HP.http_client_state) : prop =
  (st.HP.hcs_filename == None ==> st.HP.hcs_received == []) /\
  (st.HP.hcs_status == FT.FT_Completed ==>
     Seq.length (FT.ft_concat st.HP.hcs_received) >= st.HP.hcs_len)

let lemma_client_state_inv_initial ()
  : Lemma (client_state_inv HP.http_client_initial)
=
  ()

let rec lemma_trace_received_blocks
  (st0:HP.http_client_state) (trace:client_trace) (st1:HP.http_client_state)
  : Lemma
      (requires
        SM.trace_reaches HP.http_client_state_machine st0 trace st1 /\
        client_state_inv st0)
      (ensures
        client_state_inv st1 /\
        Seq.equal
          (Seq.append
            (FT.ft_concat st0.HP.hcs_received)
            (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace)))
          (FT.ft_concat st1.HP.hcs_received))
      (decreases trace)
=
  match trace with
  | [] ->
    Seq.append_empty_r (FT.ft_concat st0.HP.hcs_received)
  | tr :: rest ->
    let stm = tr.SM.tr_next_state in
    assert (HP.http_client_step st0 tr.SM.tr_event stm tr.SM.tr_output);
    (match tr.SM.tr_event with
     | SM.LocalEvent (HP.Client_start _ _) ->
       assert (st0.HP.hcs_received == []);
       assert (stm.HP.hcs_received == [])
     | SM.WireEvent m ->
       (match m with
        | Msg_body d ->
          SLog.lemma_serialize_all_body d;
          HP.lemma_ft_concat_append st0.HP.hcs_received [(d <: TCP.bytes)];
          Seq.append_empty_r (d <: TCP.bytes)
        | _ -> ()));
    assert (Seq.equal
      (Seq.append
        (FT.ft_concat st0.HP.hcs_received)
        (WF.serialize_all http_wire_format (WFSM.event_input_messages tr.SM.tr_event)))
      (FT.ft_concat stm.HP.hcs_received));
    lemma_trace_received_blocks stm rest st1;
    SLog.lemma_trace_input_messages_append [tr] rest;
    SLog.lemma_serialize_all_append
      http_wire_format
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest);
    L.append_l_nil (WFSM.event_input_messages tr.SM.tr_event);
    Seq.append_assoc
      (FT.ft_concat st0.HP.hcs_received)
      (WF.serialize_all http_wire_format (WFSM.event_input_messages tr.SM.tr_event))
      (WF.serialize_all http_wire_format (WFSM.trace_input_messages rest))

(* CAPSTONE 1.  Every byte the receiver read off the socket is accounted for by a
   reassembled body block, and vice versa. *)
let lemma_client_received_bytes_are_file
  (received sent:TCP.bytes) (st:HP.http_client_state)
  : Lemma
      (requires client_trace_ok received sent (mk_log received sent st))
      (ensures
        client_state_inv st /\
        Seq.equal received (HP.http_client_file st))
=
  let log = mk_log received sent st in
  let trace =
    ID.indefinite_description_ghost client_trace (client_trace_witness received sent log) in
  lemma_client_state_inv_initial ();
  lemma_trace_received_blocks HP.http_client_initial trace st;
  assert (FT.ft_concat HP.http_client_initial.HP.hcs_received == Seq.empty);
  Seq.append_empty_l (WF.serialize_all http_wire_format (WFSM.trace_input_messages trace))

(* CAPSTONE 2.  On completion the receiver has read at least the declared
   Content-Length — the receiver never reports success early. *)
let lemma_client_completed_len
  (received sent:TCP.bytes) (st:HP.http_client_state)
  : Lemma
      (requires
        client_trace_ok received sent (mk_log received sent st) /\
        st.HP.hcs_status == FT.FT_Completed)
      (ensures Seq.length received >= st.HP.hcs_len)
=
  lemma_client_received_bytes_are_file received sent st

(* ───────────────────────────────────────────────────────────────────────────
   CAPSTONE 3: the two verified endpoints compose

   The sender and the receiver were verified independently, against two separate
   state machines, with two separate ghost logs.  These theorems close the loop
   over the shared byte history: whatever the verified sender wrote, the verified
   receiver reassembles *exactly*.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_server_client_agree
  (bytes:TCP.bytes)
  (sst:HP.http_server_state)
  (cst:HP.http_client_state)
  : Lemma
      (requires
        SLog.server_trace_ok Seq.empty bytes (SLog.mk_log Seq.empty bytes sst) /\
        client_trace_ok bytes Seq.empty (mk_log bytes Seq.empty cst))
      (ensures
        Seq.equal (HP.http_client_file cst) (FT.ft_concat sst.HP.hss_sent))
=
  SLog.lemma_server_sent_bytes_are_body Seq.empty bytes sst;
  lemma_client_received_bytes_are_file bytes Seq.empty cst

(* THE end-to-end transfer theorem.  If the sender has run to completion and the
   receiver has consumed exactly the bytes the sender produced, then the file the
   receiver reconstitutes IS the file the sender was serving. *)
let lemma_end_to_end_transfer
  (bytes:TCP.bytes)
  (sst:HP.http_server_state)
  (cst:HP.http_client_state)
  : Lemma
      (requires
        SLog.server_trace_ok Seq.empty bytes (SLog.mk_log Seq.empty bytes sst) /\
        client_trace_ok bytes Seq.empty (mk_log bytes Seq.empty cst) /\
        sst.HP.hss_status == FT.FT_Completed)
      (ensures
        Seq.equal (HP.http_client_file cst) (HP.http_full sst) /\
        (match HP.http_content sst with
         | None -> True
         | Some content -> Seq.equal (HP.http_client_file cst) content))
=
  lemma_server_client_agree bytes sst cst;
  lemma_client_received_bytes_are_file bytes Seq.empty cst;
  (* turn the extensional equalities into propositional ones so they compose *)
  Seq.lemma_eq_elim bytes (HP.http_client_file cst);
  SLog.lemma_server_completed_sent_is_file Seq.empty bytes sst
