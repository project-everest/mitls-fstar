module TLS13.ConnectionState.ProtectedWireNormalize

(**
  Normalising a client's RAW protected server flight into the ordinary
  network-event spine.

  The client implementation describes every received protected handshake
  record as a HEAD [CS.ConnProtectedHandshake] step, whether or not the record
  carried several coalesced messages.  For a single-message record such a head
  step SATURATES its fragment, and
  [TLS13.Spec.StateMachine.Replay.lemma_single_message_head_step_*] show that it
  denotes exactly the same transition as the [CS.ConnNetworkEvent] carrying the
  message.

  The pairing proofs are written against the network-event spine.  This module
  transports a replay -- in either the received-decode or the sent-seal
  direction -- from the raw spine to the network spine, one flight at a time.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module L = FStar.List.Tot
module M = TLS13.Messages
module PWHead = TLS13.ConnectionState.ProtectedWireHead
module SMReplay = TLS13.Spec.StateMachine.Replay
module Seq = FStar.Seq

let recv_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake msg;
  })

(* ------------------------------------------------------------------ *)
(* Head normalisation, one event                                      *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_normalize_head_recv
  (m:CS.connection_model)
  (msg:M.handshake_msg)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        PWHead.received_handshake_head_normal_form msg ev /\
        SMReplay.conn_events_received_decode_replay m (ev :: rest) a b f)
      (ensures
        SMReplay.conn_events_received_decode_replay m (recv_ev msg :: rest) a b f)
  =
  match ev with
  | CS.ConnNetworkEvent _ -> ()
  | CS.ConnProtectedHandshake step ->
    SMReplay.lemma_single_message_head_step_replay_normalizes m step rest a b f

let lemma_normalize_head_sent
  (m:CS.connection_model)
  (msg:M.handshake_msg)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        PWHead.received_handshake_head_normal_form msg ev /\
        SMReplay.conn_events_sent_seal_replay m (ev :: rest) a b f)
      (ensures
        SMReplay.conn_events_sent_seal_replay m (recv_ev msg :: rest) a b f)
  =
  match ev with
  | CS.ConnNetworkEvent _ -> ()
  | CS.ConnProtectedHandshake step ->
    SMReplay.lemma_single_message_head_step_seal_replay_normalizes m step rest a b f
#pop-options

(* ------------------------------------------------------------------ *)
(* Congruence under a common head                                     *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let lemma_recv_replay_cons_cong
  (m:CS.connection_model)
  (ev:CS.conn_event)
  (rest1 rest2:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m (ev :: rest1) a b f /\
        (forall (m1:CS.connection_model) (ta tb:B.bytes).
          SMReplay.conn_events_received_decode_replay m1 rest1 ta tb f ==>
          SMReplay.conn_events_received_decode_replay m1 rest2 ta tb f))
      (ensures
        SMReplay.conn_events_received_decode_replay m (ev :: rest2) a b f)
  =
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event m ev /\
    CS.step_model m ev == Some model1 /\
    CS.event_raw_delta_legal m ev delta_sent delta_received /\
    SMReplay.received_event_nonempty_decode_projection m ev delta_received /\
    Seq.equal a (B.append delta_sent tail_sent) /\
    Seq.equal b (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest1 tail_sent tail_received f
  returns SMReplay.conn_events_received_decode_replay m (ev :: rest2) a b f
  with _.
  ( SMReplay.lemma_received_decode_replay_cons
      m ev rest2 a b f
      model1 delta_sent delta_received tail_sent tail_received )

let lemma_sent_replay_cons_cong
  (m:CS.connection_model)
  (ev:CS.conn_event)
  (rest1 rest2:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m (ev :: rest1) a b f /\
        (forall (m1:CS.connection_model) (ta tb:B.bytes).
          SMReplay.conn_events_sent_seal_replay m1 rest1 ta tb f ==>
          SMReplay.conn_events_sent_seal_replay m1 rest2 ta tb f))
      (ensures
        SMReplay.conn_events_sent_seal_replay m (ev :: rest2) a b f)
  =
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event m ev /\
    CS.step_model m ev == Some model1 /\
    CS.event_raw_delta_legal m ev delta_sent delta_received /\
    SMReplay.sent_event_nonempty_seal_projection m ev delta_sent /\
    Seq.equal a (B.append delta_sent tail_sent) /\
    Seq.equal b (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest1 tail_sent tail_received f
  returns SMReplay.conn_events_sent_seal_replay m (ev :: rest2) a b f
  with _.
  ( SMReplay.lemma_sent_seal_replay_cons
      m ev rest2 a b f
      model1 delta_sent delta_received tail_sent tail_received )
#pop-options

(* ------------------------------------------------------------------ *)
(* The server flight: install :: EE :: Cert :: validate :: CV ::      *)
(*                    verify :: SF :: tail                            *)
(* ------------------------------------------------------------------ *)

unfold let raw_flight
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  : list CS.conn_event =
  raw_ee :: raw_cert :: CS.ConnLocalEvent validate ::
  raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail

unfold let normal_flight
  (ee:M.handshake_msg) (cert:M.handshake_msg)
  (cv:M.handshake_msg) (sf:M.handshake_msg)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  : list CS.conn_event =
  recv_ev ee :: recv_ev cert :: CS.ConnLocalEvent validate ::
  recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail

unfold let flight_normal_form
  (ee cert cv sf:M.handshake_msg)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  : prop =
  PWHead.received_handshake_head_normal_form ee raw_ee /\
  PWHead.received_handshake_head_normal_form cert raw_cert /\
  PWHead.received_handshake_head_normal_form cv raw_cv /\
  PWHead.received_handshake_head_normal_form sf raw_sf

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let lemma_normalize_flight_recv
  (m:CS.connection_model)
  (ee cert cv sf:M.handshake_msg)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        flight_normal_form ee cert cv sf raw_ee raw_cert raw_cv raw_sf /\
        SMReplay.conn_events_received_decode_replay m
          (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) a b f)
      (ensures
        SMReplay.conn_events_received_decode_replay m
          (normal_flight ee cert cv sf validate verify tail) a b f)
  =
  (* innermost: SF *)
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3 (raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3 (recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _. lemma_normalize_head_recv m3 sf raw_sf tail ta tb f;
  (* verify :: SF *)
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3
      (CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3
      (CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_recv_replay_cons_cong m3 (CS.ConnLocalEvent verify)
      (raw_sf :: tail) (recv_ev sf :: tail) ta tb f;
  (* CV :: verify :: SF *)
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3
      (raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3
      (recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
  ( lemma_normalize_head_recv m3 cv raw_cv
      (CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f;
    lemma_recv_replay_cons_cong m3 (recv_ev cv)
      (CS.ConnLocalEvent verify :: raw_sf :: tail)
      (CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f );
  (* validate :: ... *)
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3
      (CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_recv_replay_cons_cong m3 (CS.ConnLocalEvent validate)
      (raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
      (recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f;
  (* Cert :: ... *)
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3
      (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3
      (recv_ev cert :: CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
  ( lemma_normalize_head_recv m3 cert raw_cert
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f;
    lemma_recv_replay_cons_cong m3 (recv_ev cert)
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
      (CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f );
  (* EE :: ... *)
  lemma_normalize_head_recv m ee raw_ee
    (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
    a b f;
  lemma_recv_replay_cons_cong m (recv_ev ee)
    (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
    (recv_ev cert :: CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail)
    a b f

let lemma_normalize_flight_sent
  (m:CS.connection_model)
  (ee cert cv sf:M.handshake_msg)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        flight_normal_form ee cert cv sf raw_ee raw_cert raw_cv raw_sf /\
        SMReplay.conn_events_sent_seal_replay m
          (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) a b f)
      (ensures
        SMReplay.conn_events_sent_seal_replay m
          (normal_flight ee cert cv sf validate verify tail) a b f)
  =
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3 (raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3 (recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _. lemma_normalize_head_sent m3 sf raw_sf tail ta tb f;
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3
      (CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3
      (CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_sent_replay_cons_cong m3 (CS.ConnLocalEvent verify)
      (raw_sf :: tail) (recv_ev sf :: tail) ta tb f;
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3
      (raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3
      (recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
  ( lemma_normalize_head_sent m3 cv raw_cv
      (CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f;
    lemma_sent_replay_cons_cong m3 (recv_ev cv)
      (CS.ConnLocalEvent verify :: raw_sf :: tail)
      (CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f );
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3
      (CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_sent_replay_cons_cong m3 (CS.ConnLocalEvent validate)
      (raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
      (recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f;
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3
      (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3
      (recv_ev cert :: CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f
  with introduce _ ==> _
  with _.
  ( lemma_normalize_head_sent m3 cert raw_cert
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail) ta tb f;
    lemma_sent_replay_cons_cong m3 (recv_ev cert)
      (CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
      (CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail) ta tb f );
  lemma_normalize_head_sent m ee raw_ee
    (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
    a b f;
  lemma_sent_replay_cons_cong m (recv_ev ee)
    (raw_cert :: CS.ConnLocalEvent validate :: raw_cv :: CS.ConnLocalEvent verify :: raw_sf :: tail)
    (recv_ev cert :: CS.ConnLocalEvent validate :: recv_ev cv :: CS.ConnLocalEvent verify :: recv_ev sf :: tail)
    a b f
#pop-options

(* ------------------------------------------------------------------ *)
(* With a leading install event                                       *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_normalize_flight_recv_after
  (m:CS.connection_model)
  (install:CS.conn_event)
  (ee cert cv sf:M.handshake_msg)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        flight_normal_form ee cert cv sf raw_ee raw_cert raw_cv raw_sf /\
        SMReplay.conn_events_received_decode_replay m
          (install :: raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) a b f)
      (ensures
        SMReplay.conn_events_received_decode_replay m
          (install :: normal_flight ee cert cv sf validate verify tail) a b f)
  =
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_received_decode_replay m3
      (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) ta tb f ==>
    SMReplay.conn_events_received_decode_replay m3
      (normal_flight ee cert cv sf validate verify tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_normalize_flight_recv m3 ee cert cv sf
      raw_ee raw_cert raw_cv raw_sf validate verify tail ta tb f;
  lemma_recv_replay_cons_cong m install
    (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail)
    (normal_flight ee cert cv sf validate verify tail)
    a b f

let lemma_normalize_flight_sent_after
  (m:CS.connection_model)
  (install:CS.conn_event)
  (ee cert cv sf:M.handshake_msg)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (validate verify:CS.local_event)
  (tail:list CS.conn_event)
  (a b:B.bytes)
  (f:CS.connection_model)
  : Lemma
      (requires
        flight_normal_form ee cert cv sf raw_ee raw_cert raw_cv raw_sf /\
        SMReplay.conn_events_sent_seal_replay m
          (install :: raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) a b f)
      (ensures
        SMReplay.conn_events_sent_seal_replay m
          (install :: normal_flight ee cert cv sf validate verify tail) a b f)
  =
  introduce forall (m3:CS.connection_model) (ta tb:B.bytes).
    SMReplay.conn_events_sent_seal_replay m3
      (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail) ta tb f ==>
    SMReplay.conn_events_sent_seal_replay m3
      (normal_flight ee cert cv sf validate verify tail) ta tb f
  with introduce _ ==> _
  with _.
    lemma_normalize_flight_sent m3 ee cert cv sf
      raw_ee raw_cert raw_cv raw_sf validate verify tail ta tb f;
  lemma_sent_replay_cons_cong m install
    (raw_flight raw_ee raw_cert raw_cv raw_sf validate verify tail)
    (normal_flight ee cert cv sf validate verify tail)
    a b f
#pop-options
