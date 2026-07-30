module HTTP.Protocol.Length

(**
  HTTP/1.1 response download with *Content-Length* delimited body, as
  state-machine type-class instances over the hand-written wire union
  `HTTP.Wire.Length.http_message`.

  Direction modeled: server (response sender) → client (receiver).  The server
  declares the body length in the response head (`Content-Length`) and serves
  the body as a sequence of raw `Msg_body` segments, each up to `http_block_size`
  bytes; the client reassembles the body and completes once the declared number
  of bytes has been delivered.

  ── The file-transfer profile (how HTTP differs from TFTP/YMODEM) ────────────

    * ORDERING IS POSITIONAL, not indexed.  A body segment carries no block
      number on the wire, so `ft_classify (Msg_body d) = FT_Data None d` (FTP
      block mode over TCP).  `ft_law_data_wire`'s index obligation is vacuous.

    * UNBOUNDED, TRANSPORT-RELIABLE WINDOW: `ft_window = None` (TCP provides
      ordering and flow control).

    * NO BODY-LEVEL ACKS: `FT_Ack` is never classified; `ft_law_ack_wire` is
      vacuous; the acked prefix stays 0.

    * NO TIMEOUTS / RETRANSMISSION: `ft_is_timeout` is always false;
      `ft_law_timeout` is vacuous.

    * UNPADDED, DECLARED-LENGTH.  A body segment carries its exact payload; the
      declared Content-Length equals the total body length (unpadded), so
      reassembly equals the body exactly (`reassembly_exact` degenerates to a
      full equality).  Unlike Content-Length framing has NO on-wire terminator:
      completion is out-of-band once the declared byte count is delivered.

    * THE START IS A LOCAL EVENT: request/response heads classify `FT_Other` and
      `ft_law_request_wire` is vacuous.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module FT = Common.FileTransfer
module TCP = Common.TCP

open HTTP.Wire.Length

(* ───────────────────────────────────────────────────────────────────────────
   Block plans and reassembly lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* Maximum body-segment payload.  Any positive cap is legal; 65535 mirrors the
   chunked framing's per-segment cap. *)
let http_block_size : n:nat{n >= 1} = 65535

(* A "plan" is the body pre-framed into segments, each between 1 and
   `http_block_size` bytes and each `body_ok` (so it cannot collide on the wire
   with the "GET "/"HTTP/1.1 " request/response prefixes). *)
let rec plan_wf (l:list TCP.bytes) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: tl -> 1 <= Seq.length x /\ Seq.length x <= http_block_size /\ body_ok x /\ plan_wf tl

(* Concatenating a block list distributes over list append. *)
let rec lemma_ft_concat_append (l1 l2:list TCP.bytes)
  : Lemma
      (ensures
        FT.ft_concat (L.append l1 l2) ==
        Seq.append (FT.ft_concat l1) (FT.ft_concat l2))
      (decreases l1)
=
  match l1 with
  | [] -> Seq.append_empty_l (FT.ft_concat l2)
  | x :: tl ->
    lemma_ft_concat_append tl l2;
    Seq.append_assoc x (FT.ft_concat tl) (FT.ft_concat l2)

(* A concatenation is a prefix of that concatenation followed by more bytes. *)
let lemma_bytes_extends_append (x y:TCP.bytes)
  : Lemma (TCP.bytes_extends x (Seq.append x y))
=
  SP.append_slices x y

(* ───────────────────────────────────────────────────────────────────────────
   Server (sender) state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type http_server_state = {
  hss_filename : option TCP.bytes;    // file requested / being served
  hss_sent     : list TCP.bytes;      // body segment payloads already sent, in order
  hss_pending  : list TCP.bytes;      // body segment payloads not yet sent
  hss_status   : FT.ft_status;
}

let http_server_initial : http_server_state = {
  hss_filename = None;
  hss_sent     = [];
  hss_pending  = [];
  hss_status   = FT.FT_InProgress;
}

noeq
type http_server_local =
  | Server_start    : filename:TCP.bytes -> plan:list TCP.bytes -> http_server_local
  | Server_send     : http_server_local
  | Server_complete : http_server_local
  | Server_abort    : http_server_local

(* The raw reassembly of every body segment (sent and pending): the whole body. *)
let http_full (s:http_server_state) : TCP.bytes =
  FT.ft_concat (L.append s.hss_sent s.hss_pending)

(* The file being served: the whole reassembly (unpadded — no truncation).  The
   declared Content-Length is exactly its length. *)
let http_content (s:http_server_state) : option TCP.bytes =
  match s.hss_filename with
  | None -> None
  | Some _ -> Some (http_full s)

(* Abstract file-transfer view.  Positional/unbounded/unacked: `ftv_acked` is 0.
   `ftv_content_len` records the declared Content-Length (= body length). *)
let http_server_project (s:http_server_state) : FT.ft_view = {
  FT.ftv_filename    = s.hss_filename;
  FT.ftv_content     = http_content s;
  FT.ftv_content_len =
    (match http_content s with None -> None | Some c -> Some (Seq.length c));
  FT.ftv_blocks      = s.hss_sent;
  FT.ftv_acked       = 0;
  FT.ftv_status      = s.hss_status;
}

(* The server emits the next body segment: it moves the head of the pending list
   onto the sent list.  Positional, unbounded window. *)
let http_server_send (s0 s1:http_server_state) (d:body_payload) : prop =
  Some? s0.hss_filename /\
  s0.hss_status == FT.FT_InProgress /\
  (match s0.hss_pending with
   | [] -> False
   | h :: rest ->
     plan_wf s0.hss_pending /\
     (d <: TCP.bytes) == h /\
     s1.hss_filename == s0.hss_filename /\
     s1.hss_sent == L.append s0.hss_sent [h] /\
     s1.hss_pending == rest /\
     s1.hss_status == FT.FT_InProgress)

let http_server_step
  (s0:http_server_state)
  (ev:SM.event http_message http_server_local)
  (s1:http_server_state)
  (out:SM.step_output http_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Server_start filename plan) ->
    s0.hss_filename == None /\
    plan_wf plan /\
    s1.hss_filename == Some filename /\
    s1.hss_sent == [] /\
    s1.hss_pending == plan /\
    s1.hss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_send ->
    (exists (d:body_payload).
       http_server_send s0 s1 d /\ out.SM.so_wire_outputs == [Msg_body d]) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_complete ->
    s0.hss_status == FT.FT_InProgress /\
    Some? s0.hss_filename /\
    s0.hss_pending == [] /\
    s1.hss_filename == s0.hss_filename /\
    s1.hss_sent == s0.hss_sent /\
    s1.hss_pending == s0.hss_pending /\
    s1.hss_status == FT.FT_Completed /\
    (* Content-Length framing has no on-wire terminator: completion is out-of-band *)
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_abort ->
    s0.hss_status == FT.FT_InProgress /\
    s1.hss_filename == s0.hss_filename /\
    s1.hss_sent == s0.hss_sent /\
    s1.hss_pending == s0.hss_pending /\
    s1.hss_status == FT.FT_Aborted /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (* the response sender consumes no body-level wire input *)
    False

noextract
let http_server_state_machine
  : SM.state_machine http_server_state http_message http_server_local unit =
  {
    SM.sm_initial_state = http_server_initial;
    SM.sm_step = http_server_step;
  }

noextract
let http_server_wfsm
  : WFSM.wire_format_state_machine http_server_state http_message http_server_local unit =
  {
    WFSM.wfsm_state_machine = http_server_state_machine;
    WFSM.wfsm_wire_format = http_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   Client (receiver) state machine

   A valid state machine (no file_transfer instance): it reassembles the body
   from the segments and completes once the declared Content-Length has been
   delivered.
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type http_client_state = {
  hcs_filename : option TCP.bytes;   // file the client is receiving
  hcs_len      : nat;                // declared Content-Length (from the head)
  hcs_received : list TCP.bytes;     // body segment payloads received, in order
  hcs_status   : FT.ft_status;
}

let http_client_initial : http_client_state = {
  hcs_filename = None;
  hcs_len      = 0;
  hcs_received = [];
  hcs_status   = FT.FT_InProgress;
}

noeq
type http_client_local =
  | Client_start : filename:TCP.bytes -> len:nat -> http_client_local

(* The exact file the client reconstitutes: the concatenation of the received
   segment payloads (unpadded). *)
let http_client_file (s:http_client_state) : TCP.bytes =
  FT.ft_concat s.hcs_received

let http_client_step
  (s0:http_client_state)
  (ev:SM.event http_message http_client_local)
  (s1:http_client_state)
  (out:SM.step_output http_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Client_start filename len) ->
    s0.hcs_filename == None /\
    s1.hcs_filename == Some filename /\
    s1.hcs_len == len /\
    s1.hcs_received == [] /\
    s1.hcs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (match m with
     | Msg_body d ->
       (* receive a body segment: append it; completion once the declared
          Content-Length has been delivered *)
       Some? s0.hcs_filename /\
       s0.hcs_status == FT.FT_InProgress /\
       s1.hcs_filename == s0.hcs_filename /\
       s1.hcs_len == s0.hcs_len /\
       s1.hcs_received == L.append s0.hcs_received [(d <: TCP.bytes)] /\
       (if Seq.length (FT.ft_concat s1.hcs_received) >= s0.hcs_len
        then s1.hcs_status == FT.FT_Completed
        else s1.hcs_status == FT.FT_InProgress) /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | _ -> False)

noextract
let http_client_state_machine
  : SM.state_machine http_client_state http_message http_client_local unit =
  {
    SM.sm_initial_state = http_client_initial;
    SM.sm_step = http_client_step;
  }

noextract
let http_client_wfsm
  : WFSM.wire_format_state_machine http_client_state http_message http_client_local unit =
  {
    WFSM.wfsm_state_machine = http_client_state_machine;
    WFSM.wfsm_wire_format = http_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   file_transfer instance for the server
   ─────────────────────────────────────────────────────────────────────────── *)

(* A body segment is a positional data block (`FT_Data None`); request/response
   heads are impl glue, classified FT_Other. *)
let http_classify (m:http_message) : FT.ft_packet =
  match m with
  | Msg_body d -> FT.FT_Data None (d <: TCP.bytes)
  | _          -> FT.FT_Other

(* HTTP over TCP has no retransmission timeouts. *)
let http_is_timeout (le:http_server_local) : bool = false

let http_server_law_initial (_:unit)
  : Lemma
      (ensures
        http_server_project http_server_state_machine.SM.sm_initial_state
          == FT.ft_view_empty)
=
  ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

let http_server_law_step
  (st0:http_server_state)
  (ev:SM.event http_message http_server_local)
  (st1:http_server_state)
  (out:SM.step_output http_message unit)
  : Lemma
      (requires http_server_state_machine.SM.sm_step st0 ev st1 out)
      (ensures
        FT.ft_view_step http_block_size None
          (http_server_project st0) (http_server_project st1))
=
  match ev with
  | SM.LocalEvent (Server_start filename plan) ->
    introduce exists fn ct.
      FT.ft_step_request fn ct (http_server_project st0) (http_server_project st1)
    with filename (http_full st1) and ()
  | SM.LocalEvent Server_send ->
    eliminate exists (d:body_payload).
      http_server_send st0 st1 d /\ out.SM.so_wire_outputs == [Msg_body d]
    returns
      FT.ft_view_step http_block_size None
        (http_server_project st0) (http_server_project st1)
    with _.
    (match st0.hss_pending with
     | [] -> ()
     | h :: rest ->
       L.append_assoc st0.hss_sent [h] rest;
       lemma_ft_concat_append (L.append st0.hss_sent [h]) rest;
       lemma_bytes_extends_append
         (FT.ft_concat (L.append st0.hss_sent [h]))
         (FT.ft_concat rest);
       FT.lemma_bytes_extends_prefix_agree
         (FT.ft_concat (L.append st0.hss_sent [h]))
         (http_full st1);
       introduce exists payload.
         FT.ft_step_send_data http_block_size None payload
           (http_server_project st0) (http_server_project st1)
       with (d <: TCP.bytes) and ())
  | SM.LocalEvent Server_complete ->
    L.append_l_nil st0.hss_sent;
    Seq.lemma_eq_elim
      (Seq.slice (http_full st0) 0 (Seq.length (http_full st0)))
      (http_full st0);
    assert (FT.ft_step_complete (http_server_project st0) (http_server_project st1))
  | SM.LocalEvent Server_abort ->
    assert (FT.ft_step_error (http_server_project st0) (http_server_project st1))
  | SM.WireEvent m -> ()

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

let http_server_law_data_wire
  (st0:http_server_state)
  (ev:SM.event http_message http_server_local)
  (st1:http_server_state)
  (out:SM.step_output http_message unit)
  (msg:http_message)
  : Lemma
      (requires
        http_server_state_machine.SM.sm_step st0 ev st1 out /\
        L.memP msg out.SM.so_wire_outputs /\
        FT.FT_Data? (http_classify msg))
      (ensures
        (match http_classify msg with
         | FT.FT_Data index payload ->
           ((match index with
             | Some i -> i == L.length (http_server_project st0).FT.ftv_blocks + 1
             | None -> True) /\
            (http_server_project st1).FT.ftv_blocks ==
              L.append (http_server_project st0).FT.ftv_blocks [payload])
           \/
           ((http_server_project st1).FT.ftv_blocks == (http_server_project st0).FT.ftv_blocks /\
            (match index with
             | Some i -> FT.ft_block_at (http_server_project st0).FT.ftv_blocks i == Some payload
             | None -> L.memP payload (http_server_project st0).FT.ftv_blocks))
         | _ -> True))
=
  match ev with
  | SM.LocalEvent Server_send ->
    eliminate exists (d:body_payload).
      http_server_send st0 st1 d /\ out.SM.so_wire_outputs == [Msg_body d]
    returns
      (match http_classify msg with
       | FT.FT_Data index payload ->
         ((match index with
           | Some i -> i == L.length (http_server_project st0).FT.ftv_blocks + 1
           | None -> True) /\
          (http_server_project st1).FT.ftv_blocks ==
            L.append (http_server_project st0).FT.ftv_blocks [payload])
         \/
         ((http_server_project st1).FT.ftv_blocks == (http_server_project st0).FT.ftv_blocks /\
          (match index with
           | Some i -> FT.ft_block_at (http_server_project st0).FT.ftv_blocks i == Some payload
           | None -> L.memP payload (http_server_project st0).FT.ftv_blocks))
       | _ -> True)
    with _. ()
  | _ ->
    (* Server_start / Server_complete / Server_abort emit no data wire output. *)
    ()

#pop-options

let http_server_law_ack_wire
  (st0:http_server_state)
  (st1:http_server_state)
  (out:SM.step_output http_message unit)
  (msg:http_message)
  : Lemma
      (requires
        http_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_Ack? (http_classify msg))
      (ensures
        (match http_classify msg with
         | FT.FT_Ack (Some index) ->
           (http_server_project st0).FT.ftv_acked < index /\
           index <= L.length (http_server_project st0).FT.ftv_blocks /\
           (http_server_project st1).FT.ftv_acked == index
         | FT.FT_Ack None ->
           (http_server_project st0).FT.ftv_acked < L.length (http_server_project st0).FT.ftv_blocks /\
           (http_server_project st1).FT.ftv_acked == (http_server_project st0).FT.ftv_acked + 1
         | _ -> True))
=
  ()

let http_server_law_request_wire
  (st0:http_server_state)
  (st1:http_server_state)
  (out:SM.step_output http_message unit)
  (msg:http_message)
  : Lemma
      (requires
        http_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_ReadRequest? (http_classify msg))
      (ensures
        (match http_classify msg with
         | FT.FT_ReadRequest filename ->
           (http_server_project st1).FT.ftv_filename == Some filename /\
           (http_server_project st1).FT.ftv_blocks == [] /\
           (http_server_project st1).FT.ftv_acked == 0
         | _ -> True))
=
  ()

let http_server_law_timeout
  (st0:http_server_state)
  (le:http_server_local)
  (st1:http_server_state)
  (out:SM.step_output http_message unit)
  (msg:http_message)
  : Lemma
      (requires
        http_server_state_machine.SM.sm_step st0 (SM.LocalEvent le) st1 out /\
        http_is_timeout le)
      (ensures
        http_server_project st1 == http_server_project st0 /\
        (L.memP msg out.SM.so_wire_outputs /\ FT.FT_Data? (http_classify msg) ==>
          (match http_classify msg with
           | FT.FT_Data index payload ->
             (match index with
              | Some i -> FT.ft_block_at (http_server_project st0).FT.ftv_blocks i == Some payload
              | None -> True)
           | _ -> True)))
=
  ()

noextract
let http_server_file_transfer
  : FT.file_transfer http_server_state http_message http_server_local unit
      http_server_wfsm =
  {
    FT.ft_block_size = http_block_size;
    FT.ft_window = None;
    FT.ft_classify = http_classify;
    FT.ft_is_timeout = http_is_timeout;
    FT.ft_project = http_server_project;
    FT.ft_law_initial = http_server_law_initial;
    FT.ft_law_step = http_server_law_step;
    FT.ft_law_data_wire = http_server_law_data_wire;
    FT.ft_law_ack_wire = http_server_law_ack_wire;
    FT.ft_law_request_wire = http_server_law_request_wire;
    FT.ft_law_timeout = http_server_law_timeout;
  }

(* Capstone: the generic reconstitution theorem for the Content-Length HTTP
   server.  In any reachable state serving a file, the raw reassembly agrees with
   the body on their common prefix, and on completion reconstitutes the exact
   body (a full equality, since HTTP Content-Length framing is unpadded). *)
let lemma_http_server_reconstitution (st:http_server_state)
  : Lemma
      (requires SM.valid_state http_server_state_machine st)
      (ensures
        (match (http_server_project st).FT.ftv_content with
         | None -> True
         | Some content ->
           FT.bytes_prefix_agree
             (FT.ft_concat (http_server_project st).FT.ftv_blocks) content /\
           ((http_server_project st).FT.ftv_status == FT.FT_Completed ==>
             FT.reassembly_exact (http_server_project st).FT.ftv_blocks content)))
=
  FT.lemma_ft_reconstitution http_server_file_transfer st
