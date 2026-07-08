module YModem.Protocol

(**
  YMODEM (128-byte profile) as state-machine type-class instances, in the
  download (sender -> receiver) direction.

  This module provides:

    * the YMODEM *server* (sender) state machine (Common.StateMachine.state_machine
      + Common.WireFormatStateMachine.wire_format_state_machine), which serves a
      file as a sequence of fixed 128-byte data packets;
    * the YMODEM *client* (receiver) state machine, which reassembles the file
      from the data packets and truncates the padded final block to the declared
      length;
    * an instance of the Common.FileTransfer.file_transfer class for the server,
      exercising the *truncating* exact-file guarantee: the data blocks on the
      wire are padded to 128 bytes, and the declared length (carried, in YMODEM,
      by the header block 0) recovers the exact file by truncation.

  Modeling choices (see also ymodem.qd.rfc):

    * The data-connection wire message is `ymodem_packet`
      (`YModem.Wire.Generated.Ymodem_packet`), with per-message wire format the
      instance `YModem.Wire.ymodem_wire_format`.  `block_payload` projects the
      fixed 128-byte data field.

    * The header block 0 (which declares the file name and length) and the
      end-of-file marker (YMODEM's EOT, 0x04) are, like the FTP block-mode
      control channel, modeled as *local events* — a start event carrying the
      file name, declared length and pre-framed blocks, and an explicit EOT
      completion event.  The data blocks themselves are the wire outputs.

    * Data blocks are padded to exactly 128 bytes, so the raw reassembly
      overshoots the file; the declared length truncates the padding away.  This
      is what distinguishes YMODEM from FTP block mode, and what the truncating
      exact-file guarantee of Common.FileTransfer was added to capture.

    * YMODEM carries a block number on the wire, but it wraps mod 256, so
      ordering is modeled positionally (FT_Data None), as in FTP block mode.

    * There is no application-level ack or timeout in this download model (the
      classic YMODEM ACK/NAK handshake rides underneath); the transfer uses an
      unbounded window (ft_window = None) and those laws are vacuous.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module U8 = FStar.UInt8
module SM = Common.StateMachine
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module FT = Common.FileTransfer
module TCP = Common.TCP

open YModem.Wire.Generated.Ymodem_packet
open YModem.Wire

(* ───────────────────────────────────────────────────────────────────────────
   Packet payloads, block plans, reassembly lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* The 128-byte data field of a YMODEM packet. *)
let block_payload (pkt:ymodem_packet) : TCP.bytes = (pkt.data <: TCP.bytes)

(* YMODEM 128-byte block size. *)
let ymodem_block_size : n:nat{n >= 1} = 128

(* A "plan" is the file, pre-framed into 128-byte data blocks (the final one
   padded up to 128), matching the fixed `ymodem_packet` data field. *)
let rec plan_wf (l:list TCP.bytes) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: tl -> Seq.length x == 128 /\ plan_wf tl

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

(* Two prefixes of the same byte sequence agree on their common prefix. *)
let lemma_two_prefixes_agree (x:TCP.bytes) (m n:nat)
  : Lemma (requires m <= Seq.length x /\ n <= Seq.length x)
          (ensures FT.bytes_prefix_agree (Seq.slice x 0 m) (Seq.slice x 0 n))
=
  let k = if m <= n then m else n in
  Seq.slice_slice x 0 m 0 k;
  Seq.slice_slice x 0 n 0 k;
  Seq.slice_length (Seq.slice x 0 m);
  Seq.slice_length (Seq.slice x 0 n)

(* ───────────────────────────────────────────────────────────────────────────
   Server (sender) state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_server_state = {
  yss_filename : option TCP.bytes;   // file requested / being served
  yss_len      : nat;                // declared content length (from block 0)
  yss_sent     : list TCP.bytes;     // 128-byte data blocks already sent, in order
  yss_pending  : list TCP.bytes;     // 128-byte data blocks not yet sent
  yss_status   : FT.ft_status;
}

let ymodem_server_initial : ymodem_server_state = {
  yss_filename = None;
  yss_len      = 0;
  yss_sent     = [];
  yss_pending  = [];
  yss_status   = FT.FT_InProgress;
}

(* Local events driving the server: the header (block 0) declaring name, length
   and the pre-framed padded blocks; a per-block send; the EOT completion; abort. *)
noeq
type ymodem_server_local =
  | YmodemStart     : filename:TCP.bytes -> len:nat -> plan:list TCP.bytes -> ymodem_server_local
  | YmodemSendBlock : ymodem_server_local
  | YmodemEot       : ymodem_server_local
  | YmodemAbort     : ymodem_server_local

(* The raw reassembly of every data block (sent and pending): the padded file. *)
let ymodem_full (s:ymodem_server_state) : TCP.bytes =
  FT.ft_concat (L.append s.yss_sent s.yss_pending)

(* The declared length, clamped to the padded size so the view is always
   well-defined (an identity for well-formed transfers, where len <= padded). *)
let ymodem_clen (s:ymodem_server_state) : nat =
  let t = Seq.length (ymodem_full s) in
  if s.yss_len <= t then s.yss_len else t

(* The file being served: the declared-length prefix of the padded reassembly. *)
let ymodem_content (s:ymodem_server_state) : option TCP.bytes =
  match s.yss_filename with
  | None -> None
  | Some _ -> Some (Seq.slice (ymodem_full s) 0 (ymodem_clen s))

(* Abstract file-transfer view of a server state. *)
let ymodem_server_project (s:ymodem_server_state) : FT.ft_view = {
  FT.ftv_filename    = s.yss_filename;
  FT.ftv_content     = ymodem_content s;
  FT.ftv_content_len =
    (match ymodem_content s with None -> None | Some c -> Some (Seq.length c));
  FT.ftv_blocks      = s.yss_sent;
  FT.ftv_acked       = 0;
  FT.ftv_status      = s.yss_status;
}

(* The server emits the next 128-byte data packet: it moves the head of the
   pending list onto the sent list.  Sending never completes (see YmodemEot). *)
let ymodem_server_send (s0 s1:ymodem_server_state) (pkt:ymodem_packet) : prop =
  Some? s0.yss_filename /\
  s0.yss_status == FT.FT_InProgress /\
  (match s0.yss_pending with
   | [] -> False
   | h :: rest ->
     plan_wf s0.yss_pending /\
     block_payload pkt == h /\
     s1.yss_filename == s0.yss_filename /\
     s1.yss_len == s0.yss_len /\
     s1.yss_sent == L.append s0.yss_sent [h] /\
     s1.yss_pending == rest /\
     s1.yss_status == FT.FT_InProgress)

let ymodem_server_step
  (s0:ymodem_server_state)
  (ev:SM.event ymodem_packet ymodem_server_local)
  (s1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (YmodemStart filename len plan) ->
    s0.yss_filename == None /\
    plan_wf plan /\
    s1.yss_filename == Some filename /\
    s1.yss_len == len /\
    s1.yss_sent == [] /\
    s1.yss_pending == plan /\
    s1.yss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent YmodemSendBlock ->
    (exists pkt. ymodem_server_send s0 s1 pkt /\ out.SM.so_wire_outputs == [pkt]) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent YmodemEot ->
    Some? s0.yss_filename /\
    s0.yss_status == FT.FT_InProgress /\
    s0.yss_pending == [] /\
    s1.yss_filename == s0.yss_filename /\
    s1.yss_len == s0.yss_len /\
    s1.yss_sent == s0.yss_sent /\
    s1.yss_pending == [] /\
    s1.yss_status == FT.FT_Completed /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent YmodemAbort ->
    s1.yss_filename == s0.yss_filename /\
    s1.yss_len == s0.yss_len /\
    s1.yss_sent == s0.yss_sent /\
    s1.yss_pending == s0.yss_pending /\
    s1.yss_status == FT.FT_Aborted /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent _ ->
    False

noextract
let ymodem_server_state_machine
  : SM.state_machine ymodem_server_state ymodem_packet ymodem_server_local unit =
  {
    SM.sm_initial_state = ymodem_server_initial;
    SM.sm_step = ymodem_server_step;
  }

noextract
let ymodem_server_wfsm
  : WFSM.wire_format_state_machine ymodem_server_state ymodem_packet ymodem_server_local unit =
  {
    WFSM.wfsm_state_machine = ymodem_server_state_machine;
    WFSM.wfsm_wire_format = ymodem_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   Client (receiver) state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_state = {
  ycs_filename : option TCP.bytes;   // file the client is receiving
  ycs_len      : nat;                // declared length (learned from block 0)
  ycs_received : list TCP.bytes;     // 128-byte data payloads received, in order
  ycs_status   : FT.ft_status;
}

let ymodem_client_initial : ymodem_client_state = {
  ycs_filename = None;
  ycs_len      = 0;
  ycs_received = [];
  ycs_status   = FT.FT_InProgress;
}

noeq
type ymodem_client_local =
  | YmodemClientStart : filename:TCP.bytes -> len:nat -> ymodem_client_local
  | YmodemClientEot   : ymodem_client_local

(* The exact file the client reconstitutes on completion: the declared-length
   prefix of the reassembly, truncating the padded final block away. *)
let ymodem_client_file (s:ymodem_client_state) : TCP.bytes =
  let r = FT.ft_concat s.ycs_received in
  let l = if s.ycs_len <= Seq.length r then s.ycs_len else Seq.length r in
  Seq.slice r 0 l

let ymodem_client_step
  (s0:ymodem_client_state)
  (ev:SM.event ymodem_packet ymodem_client_local)
  (s1:ymodem_client_state)
  (out:SM.step_output ymodem_packet unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (YmodemClientStart filename len) ->
    s0.ycs_filename == None /\
    s1.ycs_filename == Some filename /\
    s1.ycs_len == len /\
    s1.ycs_received == [] /\
    s1.ycs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent pkt ->
    Some? s0.ycs_filename /\
    s0.ycs_status == FT.FT_InProgress /\
    s1.ycs_filename == s0.ycs_filename /\
    s1.ycs_len == s0.ycs_len /\
    s1.ycs_received == L.append s0.ycs_received [block_payload pkt] /\
    s1.ycs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent YmodemClientEot ->
    Some? s0.ycs_filename /\
    s0.ycs_status == FT.FT_InProgress /\
    s1.ycs_filename == s0.ycs_filename /\
    s1.ycs_len == s0.ycs_len /\
    s1.ycs_received == s0.ycs_received /\
    s1.ycs_status == FT.FT_Completed /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []

noextract
let ymodem_client_state_machine
  : SM.state_machine ymodem_client_state ymodem_packet ymodem_client_local unit =
  {
    SM.sm_initial_state = ymodem_client_initial;
    SM.sm_step = ymodem_client_step;
  }

noextract
let ymodem_client_wfsm
  : WFSM.wire_format_state_machine ymodem_client_state ymodem_packet ymodem_client_local unit =
  {
    WFSM.wfsm_state_machine = ymodem_client_state_machine;
    WFSM.wfsm_wire_format = ymodem_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   file_transfer instance for the server
   ─────────────────────────────────────────────────────────────────────────── *)

(* YMODEM data blocks carry a wrapping block number, so ordering is modeled
   positionally (FT_Data None), as in FTP block mode. *)
let ymodem_classify (pkt:ymodem_packet) : FT.ft_packet =
  FT.FT_Data None (block_payload pkt)

let ymodem_is_timeout (_:ymodem_server_local) : bool = false

let ymodem_server_law_initial (_:unit)
  : Lemma
      (ensures
        ymodem_server_project ymodem_server_state_machine.SM.sm_initial_state
          == FT.ft_view_empty)
=
  ()

#push-options "--fuel 2 --ifuel 2"

let ymodem_server_law_step
  (st0:ymodem_server_state)
  (ev:SM.event ymodem_packet ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  : Lemma
      (requires ymodem_server_state_machine.SM.sm_step st0 ev st1 out)
      (ensures
        FT.ft_view_step ymodem_block_size None
          (ymodem_server_project st0) (ymodem_server_project st1))
=
  match ev with
  | SM.LocalEvent (YmodemStart filename len plan) ->
    introduce exists fn ct.
      FT.ft_step_request fn ct (ymodem_server_project st0) (ymodem_server_project st1)
    with filename (Seq.slice (ymodem_full st1) 0 (ymodem_clen st1)) and ()
  | SM.LocalEvent YmodemSendBlock ->
    eliminate exists pkt. ymodem_server_send st0 st1 pkt /\ out.SM.so_wire_outputs == [pkt]
    returns
      FT.ft_view_step ymodem_block_size None
        (ymodem_server_project st0) (ymodem_server_project st1)
    with _.
    (match st0.yss_pending with
     | [] -> ()
     | h :: rest ->
       L.append_assoc st0.yss_sent [h] rest;
       lemma_ft_concat_append (L.append st0.yss_sent [h]) rest;
       lemma_bytes_extends_append
         (FT.ft_concat (L.append st0.yss_sent [h]))
         (FT.ft_concat rest);
       // ft_concat st1.sent is a prefix of the (unchanged) padded reassembly,
       // and the content is another prefix of it, so they agree.
       lemma_two_prefixes_agree
         (ymodem_full st1)
         (Seq.length (FT.ft_concat (L.append st0.yss_sent [h])))
         (ymodem_clen st1);
       introduce exists payload.
         FT.ft_step_send_data ymodem_block_size None payload
           (ymodem_server_project st0) (ymodem_server_project st1)
       with h and ())
  | SM.LocalEvent YmodemEot ->
    L.append_l_nil st0.yss_sent;
    Seq.slice_length (Seq.slice (ymodem_full st0) 0 (ymodem_clen st0));
    assert (FT.ft_step_complete (ymodem_server_project st0) (ymodem_server_project st1))
  | SM.LocalEvent YmodemAbort ->
    L.append_l_nil st0.yss_sent;
    assert (FT.ft_step_error (ymodem_server_project st0) (ymodem_server_project st1))
  | SM.WireEvent _ ->
    ()

#pop-options

let ymodem_server_law_data_wire
  (st0:ymodem_server_state)
  (ev:SM.event ymodem_packet ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  (msg:ymodem_packet)
  : Lemma
      (requires
        ymodem_server_state_machine.SM.sm_step st0 ev st1 out /\
        L.memP msg out.SM.so_wire_outputs /\
        FT.FT_Data? (ymodem_classify msg))
      (ensures
        (match ymodem_classify msg with
         | FT.FT_Data index payload ->
           (match index with
            | Some i -> i == L.length (ymodem_server_project st0).FT.ftv_blocks + 1
            | None -> True) /\
           (ymodem_server_project st1).FT.ftv_blocks ==
             L.append (ymodem_server_project st0).FT.ftv_blocks [payload]
         | _ -> True))
=
  match ev with
  | SM.LocalEvent YmodemSendBlock ->
    eliminate exists pkt. ymodem_server_send st0 st1 pkt /\ out.SM.so_wire_outputs == [pkt]
    returns
      (match ymodem_classify msg with
       | FT.FT_Data index payload ->
         (match index with
          | Some i -> i == L.length (ymodem_server_project st0).FT.ftv_blocks + 1
          | None -> True) /\
         (ymodem_server_project st1).FT.ftv_blocks ==
           L.append (ymodem_server_project st0).FT.ftv_blocks [payload]
       | _ -> True)
    with _. ()
  | _ -> ()

let ymodem_server_law_ack_wire
  (st0:ymodem_server_state)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  (msg:ymodem_packet)
  : Lemma
      (requires
        ymodem_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_Ack? (ymodem_classify msg))
      (ensures
        (match ymodem_classify msg with
         | FT.FT_Ack (Some index) ->
           (ymodem_server_project st0).FT.ftv_acked < index /\
           index <= L.length (ymodem_server_project st0).FT.ftv_blocks /\
           (ymodem_server_project st1).FT.ftv_acked == index
         | FT.FT_Ack None ->
           (ymodem_server_project st0).FT.ftv_acked < L.length (ymodem_server_project st0).FT.ftv_blocks /\
           (ymodem_server_project st1).FT.ftv_acked == (ymodem_server_project st0).FT.ftv_acked + 1
         | _ -> True))
=
  ()

let ymodem_server_law_request_wire
  (st0:ymodem_server_state)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  (msg:ymodem_packet)
  : Lemma
      (requires
        ymodem_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_ReadRequest? (ymodem_classify msg))
      (ensures
        (match ymodem_classify msg with
         | FT.FT_ReadRequest filename ->
           (ymodem_server_project st1).FT.ftv_filename == Some filename /\
           (ymodem_server_project st1).FT.ftv_blocks == [] /\
           (ymodem_server_project st1).FT.ftv_acked == 0
         | _ -> True))
=
  ()

let ymodem_server_law_timeout
  (st0:ymodem_server_state)
  (le:ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_packet unit)
  (msg:ymodem_packet)
  : Lemma
      (requires
        ymodem_server_state_machine.SM.sm_step st0 (SM.LocalEvent le) st1 out /\
        ymodem_is_timeout le)
      (ensures
        ymodem_server_project st1 == ymodem_server_project st0 /\
        (L.memP msg out.SM.so_wire_outputs /\ FT.FT_Data? (ymodem_classify msg) ==>
          (match ymodem_classify msg with
           | FT.FT_Data index payload ->
             (match index with
              | Some i -> FT.ft_block_at (ymodem_server_project st0).FT.ftv_blocks i == Some payload
              | None -> True)
           | _ -> True)))
=
  ()

noextract
let ymodem_server_file_transfer
  : FT.file_transfer ymodem_server_state ymodem_packet ymodem_server_local unit
      ymodem_server_wfsm =
  {
    FT.ft_block_size = ymodem_block_size;
    FT.ft_window = None;
    FT.ft_classify = ymodem_classify;
    FT.ft_is_timeout = ymodem_is_timeout;
    FT.ft_project = ymodem_server_project;
    FT.ft_law_initial = ymodem_server_law_initial;
    FT.ft_law_step = ymodem_server_law_step;
    FT.ft_law_data_wire = ymodem_server_law_data_wire;
    FT.ft_law_ack_wire = ymodem_server_law_ack_wire;
    FT.ft_law_request_wire = ymodem_server_law_request_wire;
    FT.ft_law_timeout = ymodem_server_law_timeout;
  }

(* Capstone: the generic reconstitution theorem for the YMODEM server.  In any
   reachable state serving a file, the raw (padded) reassembly agrees with the
   file on their common prefix, and on completion reconstitutes the exact file by
   truncating the padded final block to the declared length. *)
let lemma_ymodem_server_reconstitution (st:ymodem_server_state)
  : Lemma
      (requires SM.valid_state ymodem_server_state_machine st)
      (ensures
        (match (ymodem_server_project st).FT.ftv_content with
         | None -> True
         | Some content ->
           FT.bytes_prefix_agree
             (FT.ft_concat (ymodem_server_project st).FT.ftv_blocks) content /\
           ((ymodem_server_project st).FT.ftv_status == FT.FT_Completed ==>
             FT.reassembly_exact (ymodem_server_project st).FT.ftv_blocks content)))
=
  FT.lemma_ft_reconstitution ymodem_server_file_transfer st
