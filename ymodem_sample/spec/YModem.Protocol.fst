module YModem.Protocol

(**
  YMODEM (128-byte profile) as state-machine type-class instances, modeled as a
  *stop-and-wait ARQ* (Automatic Repeat reQuest) reliable-delivery protocol over
  the leading-byte-discriminated wire union `ymodem_message`
  (`YModem.Wire.Generated.Ymodem_message`), with per-message wire format the
  instance `YModem.Wire.ymodem_wire_format`.

  This module provides:

    * the YMODEM *server* (sender) state machine, which serves a file as a
      sequence of fixed 128-byte SOH data packets, advancing one block at a time
      as the receiver ACKs, retransmitting the outstanding block on a NAK or a
      timeout, and closing the transfer with an EOT handshake;
    * the YMODEM *client* (receiver) state machine, which ACKs each SOH data
      packet, ACKs the final EOT, and reassembles the file;
    * an instance of the Common.FileTransfer.file_transfer class for the server,
      with a *stop-and-wait* window (`ft_window = Some 1`), exercising the
      truncating exact-file guarantee together with ACK-driven advancement and
      NAK/timeout retransmission.

  ── Modeling choices (see also ymodem.qd.rfc) ───────────────────────────────

    * Reliable delivery is stop-and-wait: the sender keeps at most one block in
      flight (`ft_window = Some 1`).  A `Body_ack` from the receiver advances the
      acknowledged prefix by one (a *positional* ack, `FT_Ack None`); a
      `Body_nak` or a `Server_timeout` retransmits the single outstanding block
      (`FT_Data None` again) without changing the abstract view — the delivered
      prefix, the acked count and the file are all unchanged.

    * The end of the transfer is an EOT handshake: once every data block has been
      sent and acked (`yss_pending == []`, `yss_acked == length yss_sent`), the
      sender emits `Body_eot` (phase `SP_Data -> SP_Eot`) and, on the receiver's
      final ack (an out-of-band `Server_complete` local event), moves to
      `FT_Completed`.  While in `SP_Eot`, a `Body_nak` or `Server_timeout`
      re-emits the `Body_eot`.

    * The header block 0 (which declares the file name/length) and the initial
      'C' CRC-mode solicitation are *not* modeled in the state machine: they are
      impl-level glue.  Modeling them would break the stateless classifier — a
      wrapped block-number-0 would be misread as a header, and a header ACK has
      no outstanding data block.  So every `Body_soh` in the modeled stream is a
      *data* block, classified `FT_Data None`.

    * YMODEM carries a block number on the wire, but it wraps mod 256, so
      ordering is modeled positionally (`FT_Data None`), as in FTP block mode.
      The `blk`/`blk_complement`/`crc` fields of the SOH body are therefore left
      unconstrained by the spec-level step relation (only the 128-byte data
      payload matters to the file-transfer abstraction); the Milestone-B impl
      fills them in (blk = index mod 256, complement = 255 - blk, crc = CRC16).

    * Data blocks are padded to exactly 128 bytes, so the raw reassembly
      overshoots the file; the declared length (carried, in YMODEM, by header
      block 0) truncates the padding away.  This is the truncating exact-file
      guarantee of Common.FileTransfer.
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

open YModem.Wire.Generated.Ymodem_message
open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire

(* ───────────────────────────────────────────────────────────────────────────
   Packet payloads, block plans, reassembly lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* The 128-byte data field of a YMODEM SOH packet. *)
let block_payload (body:ymodem_soh_body) : TCP.bytes = (body.data <: Seq.seq U8.t)

(* YMODEM 128-byte block size. *)
let ymodem_block_size : n:nat{n >= 1} = 128

(* A "plan" is the file, pre-framed into 128-byte data blocks (the final one
   padded up to 128), matching the fixed `ymodem_soh_body` data field. *)
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

(* The sender's phase: still sending/acking data blocks, or in the EOT
   handshake (all blocks sent+acked, EOT emitted, awaiting completion). *)
type ymodem_server_phase =
  | SP_Data
  | SP_Eot

noeq
type ymodem_server_state = {
  yss_filename : option TCP.bytes;    // file requested / being served
  yss_len      : nat;                 // declared content length (from block 0)
  yss_sent     : list TCP.bytes;      // 128-byte data blocks already sent, in order
  yss_pending  : list TCP.bytes;      // 128-byte data blocks not yet sent
  yss_acked    : nat;                 // number of leading blocks the receiver acked
  yss_phase    : ymodem_server_phase; // data phase or EOT handshake
  yss_status   : FT.ft_status;
}

let ymodem_server_initial : ymodem_server_state = {
  yss_filename = None;
  yss_len      = 0;
  yss_sent     = [];
  yss_pending  = [];
  yss_acked    = 0;
  yss_phase    = SP_Data;
  yss_status   = FT.FT_InProgress;
}

(* Local events driving the server:
     * Server_start   — the header (block 0): file name, declared length and the
       pre-framed padded blocks;
     * Server_send    — emit the next data block (stop-and-wait: only when the
       previous one is acked);
     * Server_eot     — all blocks sent+acked: emit EOT (enter the handshake);
     * Server_complete— the receiver acked the EOT: the transfer is complete;
     * Server_timeout — retransmission timeout: re-emit the outstanding block
       (data phase) or the EOT (EOT phase);
     * Server_abort   — cancel the transfer. *)
noeq
type ymodem_server_local =
  | Server_start    : filename:TCP.bytes -> len:nat -> plan:list TCP.bytes -> ymodem_server_local
  | Server_send     : ymodem_server_local
  | Server_eot      : ymodem_server_local
  | Server_complete : ymodem_server_local
  | Server_timeout  : ymodem_server_local
  | Server_abort    : ymodem_server_local

(* The raw reassembly of every data block (sent and pending): the padded file.
   This is invariant under Server_send (moving the head of pending onto sent
   leaves the concatenation unchanged). *)
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

(* Abstract file-transfer view of a server state.  The phase is bookkeeping that
   the projection deliberately ignores (the EOT handshake stutters the view). *)
let ymodem_server_project (s:ymodem_server_state) : FT.ft_view = {
  FT.ftv_filename    = s.yss_filename;
  FT.ftv_content     = ymodem_content s;
  FT.ftv_content_len =
    (match ymodem_content s with None -> None | Some c -> Some (Seq.length c));
  FT.ftv_blocks      = s.yss_sent;
  FT.ftv_acked       = s.yss_acked;
  FT.ftv_status      = s.yss_status;
}

(* The projection ignores the phase: states that agree on every non-phase field
   have the same abstract view (used to prove the EOT handshake stutters). *)
let lemma_project_ignores_phase (s0 s1:ymodem_server_state)
  : Lemma
      (requires
        s0.yss_filename == s1.yss_filename /\
        s0.yss_len == s1.yss_len /\
        s0.yss_sent == s1.yss_sent /\
        s0.yss_pending == s1.yss_pending /\
        s0.yss_acked == s1.yss_acked /\
        s0.yss_status == s1.yss_status)
      (ensures ymodem_server_project s0 == ymodem_server_project s1)
=
  ()

(* The server emits the next 128-byte SOH data packet: it moves the head of the
   pending list onto the sent list.  Stop-and-wait: the previous block must be
   acked (in flight == 0, i.e. length sent == acked).  Sending never completes
   (see Server_eot / Server_complete). *)
let ymodem_server_send (s0 s1:ymodem_server_state) (body:ymodem_soh_body) : prop =
  Some? s0.yss_filename /\
  s0.yss_phase == SP_Data /\
  s0.yss_status == FT.FT_InProgress /\
  L.length s0.yss_sent == s0.yss_acked /\
  (match s0.yss_pending with
   | [] -> False
   | h :: rest ->
     plan_wf s0.yss_pending /\
     block_payload body == h /\
     s1.yss_filename == s0.yss_filename /\
     s1.yss_len == s0.yss_len /\
     s1.yss_sent == L.append s0.yss_sent [h] /\
     s1.yss_pending == rest /\
     s1.yss_acked == s0.yss_acked /\
     s1.yss_phase == SP_Data /\
     s1.yss_status == FT.FT_InProgress)

(* The server retransmits the single outstanding (first unacked) data block.
   `yss_acked` (0-based) indexes it in `yss_sent`.  The abstract view is
   unchanged (the caller pins `s1 == s0`). *)
let ymodem_retransmit_data (s0:ymodem_server_state) (out:SM.step_output ymodem_message unit) : prop =
  s0.yss_acked < L.length s0.yss_sent /\
  (exists body.
     block_payload body == L.index s0.yss_sent s0.yss_acked /\
     out.SM.so_wire_outputs == [Body_soh body])

let ymodem_server_step
  (s0:ymodem_server_state)
  (ev:SM.event ymodem_message ymodem_server_local)
  (s1:ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Server_start filename len plan) ->
    s0.yss_filename == None /\
    plan_wf plan /\
    s1.yss_filename == Some filename /\
    s1.yss_len == len /\
    s1.yss_sent == [] /\
    s1.yss_pending == plan /\
    s1.yss_acked == 0 /\
    s1.yss_phase == SP_Data /\
    s1.yss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_send ->
    (exists body. ymodem_server_send s0 s1 body /\ out.SM.so_wire_outputs == [Body_soh body]) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_eot ->
    s0.yss_phase == SP_Data /\
    s0.yss_status == FT.FT_InProgress /\
    Some? s0.yss_filename /\
    s0.yss_pending == [] /\
    s0.yss_acked == L.length s0.yss_sent /\
    s1.yss_filename == s0.yss_filename /\
    s1.yss_len == s0.yss_len /\
    s1.yss_sent == s0.yss_sent /\
    s1.yss_pending == s0.yss_pending /\
    s1.yss_acked == s0.yss_acked /\
    s1.yss_phase == SP_Eot /\
    s1.yss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [Body_eot ()] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_complete ->
    s0.yss_phase == SP_Eot /\
    s0.yss_status == FT.FT_InProgress /\
    Some? s0.yss_filename /\
    s0.yss_pending == [] /\
    s0.yss_acked == L.length s0.yss_sent /\
    s1.yss_filename == s0.yss_filename /\
    s1.yss_len == s0.yss_len /\
    s1.yss_sent == s0.yss_sent /\
    s1.yss_pending == s0.yss_pending /\
    s1.yss_acked == s0.yss_acked /\
    s1.yss_phase == s0.yss_phase /\
    s1.yss_status == FT.FT_Completed /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_timeout ->
    s0.yss_status == FT.FT_InProgress /\
    (match s0.yss_phase with
     | SP_Data -> ymodem_retransmit_data s0 out /\ s1 == s0
     | SP_Eot -> out.SM.so_wire_outputs == [Body_eot ()] /\ s1 == s0) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_abort ->
    s0.yss_status == FT.FT_InProgress /\
    s1.yss_filename == s0.yss_filename /\
    s1.yss_len == s0.yss_len /\
    s1.yss_sent == s0.yss_sent /\
    s1.yss_pending == s0.yss_pending /\
    s1.yss_acked == s0.yss_acked /\
    s1.yss_phase == s0.yss_phase /\
    s1.yss_status == FT.FT_Aborted /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (match m with
     | Body_ack _ ->
       (* positional data ack: advance the acked prefix by one *)
       s0.yss_phase == SP_Data /\
       s0.yss_status == FT.FT_InProgress /\
       s0.yss_acked < L.length s0.yss_sent /\
       s1.yss_filename == s0.yss_filename /\
       s1.yss_len == s0.yss_len /\
       s1.yss_sent == s0.yss_sent /\
       s1.yss_pending == s0.yss_pending /\
       s1.yss_acked == s0.yss_acked + 1 /\
       s1.yss_phase == s0.yss_phase /\
       s1.yss_status == FT.FT_InProgress /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | Body_nak _ ->
       (* NAK: retransmit the outstanding data block, or re-emit the EOT *)
       s0.yss_status == FT.FT_InProgress /\
       (match s0.yss_phase with
        | SP_Data -> ymodem_retransmit_data s0 out /\ s1 == s0
        | SP_Eot -> out.SM.so_wire_outputs == [Body_eot ()] /\ s1 == s0) /\
       out.SM.so_local_outputs == []
     | Body_can _ ->
       (* CAN: cancel the transfer *)
       s0.yss_status == FT.FT_InProgress /\
       s1.yss_filename == s0.yss_filename /\
       s1.yss_len == s0.yss_len /\
       s1.yss_sent == s0.yss_sent /\
       s1.yss_pending == s0.yss_pending /\
       s1.yss_acked == s0.yss_acked /\
       s1.yss_phase == s0.yss_phase /\
       s1.yss_status == FT.FT_Aborted /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | _ -> False)

noextract
let ymodem_server_state_machine
  : SM.state_machine ymodem_server_state ymodem_message ymodem_server_local unit =
  {
    SM.sm_initial_state = ymodem_server_initial;
    SM.sm_step = ymodem_server_step;
  }

noextract
let ymodem_server_wfsm
  : WFSM.wire_format_state_machine ymodem_server_state ymodem_message ymodem_server_local unit =
  {
    WFSM.wfsm_state_machine = ymodem_server_state_machine;
    WFSM.wfsm_wire_format = ymodem_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   Client (receiver) state machine

   A valid state machine (no file_transfer instance): it ACKs each SOH data
   packet, ACKs the final EOT and reassembles the file, and aborts on CAN.
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
  | Client_start : filename:TCP.bytes -> len:nat -> ymodem_client_local

(* The exact file the client reconstitutes: the declared-length prefix of the
   reassembly, truncating the padded final block away. *)
let ymodem_client_file (s:ymodem_client_state) : TCP.bytes =
  let r = FT.ft_concat s.ycs_received in
  let l = if s.ycs_len <= Seq.length r then s.ycs_len else Seq.length r in
  Seq.slice r 0 l

let ymodem_client_step
  (s0:ymodem_client_state)
  (ev:SM.event ymodem_message ymodem_client_local)
  (s1:ymodem_client_state)
  (out:SM.step_output ymodem_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Client_start filename len) ->
    s0.ycs_filename == None /\
    s1.ycs_filename == Some filename /\
    s1.ycs_len == len /\
    s1.ycs_received == [] /\
    s1.ycs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (match m with
     | Body_soh body ->
       (* receive a data block: append it and ACK *)
       Some? s0.ycs_filename /\
       s0.ycs_status == FT.FT_InProgress /\
       s1.ycs_filename == s0.ycs_filename /\
       s1.ycs_len == s0.ycs_len /\
       s1.ycs_received == L.append s0.ycs_received [block_payload body] /\
       s1.ycs_status == FT.FT_InProgress /\
       out.SM.so_wire_outputs == [Body_ack ()] /\
       out.SM.so_local_outputs == []
     | Body_eot _ ->
       (* receive EOT: ACK and complete *)
       Some? s0.ycs_filename /\
       s0.ycs_status == FT.FT_InProgress /\
       s1.ycs_filename == s0.ycs_filename /\
       s1.ycs_len == s0.ycs_len /\
       s1.ycs_received == s0.ycs_received /\
       s1.ycs_status == FT.FT_Completed /\
       out.SM.so_wire_outputs == [Body_ack ()] /\
       out.SM.so_local_outputs == []
     | Body_can _ ->
       (* receive CAN: abort *)
       Some? s0.ycs_filename /\
       s0.ycs_status == FT.FT_InProgress /\
       s1.ycs_filename == s0.ycs_filename /\
       s1.ycs_len == s0.ycs_len /\
       s1.ycs_received == s0.ycs_received /\
       s1.ycs_status == FT.FT_Aborted /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | _ -> False)

noextract
let ymodem_client_state_machine
  : SM.state_machine ymodem_client_state ymodem_message ymodem_client_local unit =
  {
    SM.sm_initial_state = ymodem_client_initial;
    SM.sm_step = ymodem_client_step;
  }

noextract
let ymodem_client_wfsm
  : WFSM.wire_format_state_machine ymodem_client_state ymodem_message ymodem_client_local unit =
  {
    WFSM.wfsm_state_machine = ymodem_client_state_machine;
    WFSM.wfsm_wire_format = ymodem_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   file_transfer instance for the server
   ─────────────────────────────────────────────────────────────────────────── *)

(* SOH = positional data block; ACK = positional ack; everything else is Other.
   YMODEM data blocks carry a wrapping block number, so ordering is positional
   (FT_Data None), as in FTP block mode; the ACK byte carries no index (FT_Ack
   None), so it confirms the next outstanding block. *)
let ymodem_classify (m:ymodem_message) : FT.ft_packet =
  match m with
  | Body_soh body -> FT.FT_Data None (block_payload body)
  | Body_ack _    -> FT.FT_Ack None
  | _             -> FT.FT_Other

(* The only retransmission timeout is Server_timeout. *)
let ymodem_is_timeout (le:ymodem_server_local) : bool =
  match le with
  | Server_timeout -> true
  | _ -> false

let ymodem_server_law_initial (_:unit)
  : Lemma
      (ensures
        ymodem_server_project ymodem_server_state_machine.SM.sm_initial_state
          == FT.ft_view_empty)
=
  ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

let ymodem_server_law_step
  (st0:ymodem_server_state)
  (ev:SM.event ymodem_message ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  : Lemma
      (requires ymodem_server_state_machine.SM.sm_step st0 ev st1 out)
      (ensures
        FT.ft_view_step ymodem_block_size (Some 1)
          (ymodem_server_project st0) (ymodem_server_project st1))
=
  match ev with
  | SM.LocalEvent (Server_start filename len plan) ->
    introduce exists fn ct.
      FT.ft_step_request fn ct (ymodem_server_project st0) (ymodem_server_project st1)
    with filename (Seq.slice (ymodem_full st1) 0 (ymodem_clen st1)) and ()
  | SM.LocalEvent Server_send ->
    eliminate exists body. ymodem_server_send st0 st1 body /\ out.SM.so_wire_outputs == [Body_soh body]
    with
    (match st0.yss_pending with
     | [] -> ()
     | h :: rest ->
       L.append_assoc st0.yss_sent [h] rest;
       lemma_ft_concat_append (L.append st0.yss_sent [h]) rest;
       lemma_bytes_extends_append
         (FT.ft_concat (L.append st0.yss_sent [h]))
         (FT.ft_concat rest);
       lemma_two_prefixes_agree
         (ymodem_full st1)
         (Seq.length (FT.ft_concat (L.append st0.yss_sent [h])))
         (ymodem_clen st1);
       introduce exists payload.
         FT.ft_step_send_data ymodem_block_size (Some 1) payload
           (ymodem_server_project st0) (ymodem_server_project st1)
       with h and ())
  | SM.LocalEvent Server_eot ->
    lemma_project_ignores_phase st0 st1
  | SM.LocalEvent Server_complete ->
    L.append_l_nil st0.yss_sent;
    Seq.slice_length (Seq.slice (ymodem_full st0) 0 (ymodem_clen st0));
    assert (FT.ft_step_complete (ymodem_server_project st0) (ymodem_server_project st1))
  | SM.LocalEvent Server_timeout ->
    (match st0.yss_phase with
     | SP_Data -> ()
     | SP_Eot -> ())
  | SM.LocalEvent Server_abort ->
    assert (FT.ft_step_error (ymodem_server_project st0) (ymodem_server_project st1))
  | SM.WireEvent m ->
    (match m with
     | Body_ack _ ->
       introduce exists index.
         FT.ft_step_recv_ack index (ymodem_server_project st0) (ymodem_server_project st1)
       with (st0.yss_acked + 1) and ()
     | Body_nak _ ->
       (match st0.yss_phase with
        | SP_Data -> ()
        | SP_Eot -> ())
     | Body_can _ ->
       assert (FT.ft_step_error (ymodem_server_project st0) (ymodem_server_project st1))
     | _ -> ())

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

let ymodem_server_law_data_wire
  (st0:ymodem_server_state)
  (ev:SM.event ymodem_message ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  (msg:ymodem_message)
  : Lemma
      (requires
        ymodem_server_state_machine.SM.sm_step st0 ev st1 out /\
        L.memP msg out.SM.so_wire_outputs /\
        FT.FT_Data? (ymodem_classify msg))
      (ensures
        (match ymodem_classify msg with
         | FT.FT_Data index payload ->
           ((match index with
             | Some i -> i == L.length (ymodem_server_project st0).FT.ftv_blocks + 1
             | None -> True) /\
            (ymodem_server_project st1).FT.ftv_blocks ==
              L.append (ymodem_server_project st0).FT.ftv_blocks [payload])
           \/
           ((ymodem_server_project st1).FT.ftv_blocks == (ymodem_server_project st0).FT.ftv_blocks /\
            (match index with
             | Some i -> FT.ft_block_at (ymodem_server_project st0).FT.ftv_blocks i == Some payload
             | None -> L.memP payload (ymodem_server_project st0).FT.ftv_blocks))
         | _ -> True))
=
  match ev with
  | SM.LocalEvent Server_send ->
    eliminate exists body. ymodem_server_send st0 st1 body /\ out.SM.so_wire_outputs == [Body_soh body]
    with ()
  | SM.LocalEvent Server_timeout ->
    (match st0.yss_phase with
     | SP_Data ->
       L.lemma_index_memP st0.yss_sent st0.yss_acked
     | SP_Eot -> ())
  | SM.WireEvent (Body_nak _) ->
    (match st0.yss_phase with
     | SP_Data ->
       L.lemma_index_memP st0.yss_sent st0.yss_acked
     | SP_Eot -> ())
  | _ -> ()

#pop-options

let ymodem_server_law_ack_wire
  (st0:ymodem_server_state)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  (msg:ymodem_message)
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
  (out:SM.step_output ymodem_message unit)
  (msg:ymodem_message)
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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

let ymodem_server_law_timeout
  (st0:ymodem_server_state)
  (le:ymodem_server_local)
  (st1:ymodem_server_state)
  (out:SM.step_output ymodem_message unit)
  (msg:ymodem_message)
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
  match le with
  | Server_timeout ->
    (match st0.yss_phase with
     | SP_Data -> ()
     | SP_Eot -> ())
  | _ -> ()

#pop-options

noextract
let ymodem_server_file_transfer
  : FT.file_transfer ymodem_server_state ymodem_message ymodem_server_local unit
      ymodem_server_wfsm =
  {
    FT.ft_block_size = ymodem_block_size;
    FT.ft_window = Some 1;
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
