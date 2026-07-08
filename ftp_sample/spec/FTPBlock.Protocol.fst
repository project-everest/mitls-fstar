module FTPBlock.Protocol

(**
  FTP "block mode" (MODE B, RFC 959 Section 3.4.2) as state-machine type-class
  instances, in the download (server -> client, `RETR`) direction.

  This module provides:

    * the FTP block-mode *server* state machine (Common.StateMachine.state_machine
      + Common.WireFormatStateMachine.wire_format_state_machine), which serves a
      file to a client as a sequence of data blocks;
    * the FTP block-mode *client* state machine, which issues a read request and
      reassembles the file from the data blocks it receives;
    * an instance of the Common.FileTransfer.file_transfer class for the server,
      establishing that the server delivers the requested file as an ordered
      sequence of blocks that reconstitute it.

  Modeling choices (see also ftp_block.qd.rfc):

    * The wire message on the data connection is `ftp_block`
      (`FTPBlock.Wire.Generated.Ftp_block`), and its per-message wire format is
      the instance `FTPBlock.Wire.ftp_block_wire_format`.

    * The FTP *control* connection (the `RETR` command, `226` completion, error
      replies) is out-of-band CRLF text, not modeled as data-connection wire
      messages.  It is represented by *local events*: the server's transfer is
      started by a `FtpStartRetr` local event carrying the requested file (as a
      well-formed sequence of blocks), and the client issues `FtpClientRetr`.

    * FTP block mode has no application-level acknowledgment or timeout: TCP
      provides ordering, flow control, and reliability.  Accordingly the transfer
      uses an *unbounded* window (`ft_window = None`) and the ack/timeout laws of
      the file_transfer class are vacuous.

    * Data blocks carry no on-wire block number; ordering is *positional* (TCP
      stream order).  Hence data blocks classify as `FT_Data None payload`
      (positional), and end-of-file is signaled by the descriptor's EOF bit,
      which by construction coincides with the transfer's final (short) block.
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

open FTPBlock.Wire.Generated.Ftp_block
open FTPBlock.Wire

(* ───────────────────────────────────────────────────────────────────────────
   Transfer parameter and block descriptor helpers
   ─────────────────────────────────────────────────────────────────────────── *)

(* The data-block chunk size.  A block strictly shorter than this ends the
   transfer; it is bounded by the 16-bit on-wire byte count (2^16 - 1). *)
let ftp_block_size : n:nat{n >= 1} = 512

(* FTP descriptor bit field (RFC 959 3.4.2): bit 6 (value 64) is EOF. *)
let ftp_eof_descriptor  : U8.t = 64uy
let ftp_data_descriptor : U8.t = 0uy

(* Whether a descriptor byte has the EOF bit set. *)
let descriptor_is_eof (d:U8.t) : bool = (U8.v d / 64) % 2 = 1

(* The payload bytes of a block (the vlbytes data field is a `bytes` refined to
   length <= 65535, so it coerces directly to TCP.bytes). *)
let block_payload (b:ftp_block) : TCP.bytes = (b.data <: TCP.bytes)

(* ───────────────────────────────────────────────────────────────────────────
   Well-formed block plans and reassembly lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* A "plan" is the file, pre-framed into data blocks: each block fits in an
   `ftp_block` data field (<= block size), so it can be emitted on the wire.
   Completion is signalled explicitly (FTP's 226), not by a short final block. *)
let rec plan_wf (bs:pos) (l:list TCP.bytes) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: tl ->
    Seq.length x <= bs /\
    plan_wf bs tl

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
   Server state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ftp_server_state = {
  fss_filename : option TCP.bytes;   // file requested by the client (control conn)
  fss_sent     : list TCP.bytes;     // data payloads already sent, in order
  fss_pending  : list TCP.bytes;     // data payloads not yet sent (rest of file)
  fss_status   : FT.ft_status;
}

let ftp_server_initial : ftp_server_state = {
  fss_filename = None;
  fss_sent     = [];
  fss_pending  = [];
  fss_status   = FT.FT_InProgress;
}

(* Local (control-connection) events driving the server. *)
noeq
type ftp_server_local =
  | FtpStartRetr : filename:TCP.bytes -> plan:list TCP.bytes -> ftp_server_local
  | FtpSendBlock : ftp_server_local
  | FtpComplete  : ftp_server_local
  | FtpAbort     : ftp_server_local

(* The full file the server is serving, once a request has started: the
   concatenation of the blocks already sent and those still pending. *)
let ftp_server_content (s:ftp_server_state) : option TCP.bytes =
  match s.fss_filename with
  | None -> None
  | Some _ -> Some (FT.ft_concat (L.append s.fss_sent s.fss_pending))

(* Declared content length: the server knows the file it is serving, so once a
   request has started it declares the file's length (used, in general, for the
   truncating exact-file guarantee; here an identity since FTP block mode is
   unpadded). *)
let ftp_server_content_len (s:ftp_server_state) : option nat =
  match ftp_server_content s with
  | None -> None
  | Some c -> Some (Seq.length c)

(* Abstract file-transfer view of a server state. *)
let ftp_server_project (s:ftp_server_state) : FT.ft_view = {
  FT.ftv_filename    = s.fss_filename;
  FT.ftv_content     = ftp_server_content s;
  FT.ftv_content_len = ftp_server_content_len s;
  FT.ftv_blocks      = s.fss_sent;
  FT.ftv_acked       = 0;
  FT.ftv_status      = s.fss_status;
}

(* The server emits the next data block: it moves the head of the pending list
   onto the sent list, tagging it with the EOF descriptor bit iff it is the last
   pending block.  Sending never completes the transfer (see FtpComplete). *)
let ftp_server_send (s0 s1:ftp_server_state) (blk:ftp_block) : prop =
  Some? s0.fss_filename /\
  s0.fss_status == FT.FT_InProgress /\
  (match s0.fss_pending with
   | [] -> False
   | h :: rest ->
     plan_wf ftp_block_size s0.fss_pending /\
     block_payload blk == h /\
     s1.fss_filename == s0.fss_filename /\
     s1.fss_sent == L.append s0.fss_sent [h] /\
     s1.fss_pending == rest /\
     s1.fss_status == FT.FT_InProgress /\
     blk.descriptor == (if Nil? rest
                        then ftp_eof_descriptor else ftp_data_descriptor))

let ftp_server_step
  (s0:ftp_server_state)
  (ev:SM.event ftp_block ftp_server_local)
  (s1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (FtpStartRetr filename plan) ->
    s0.fss_filename == None /\
    plan_wf ftp_block_size plan /\
    s1.fss_filename == Some filename /\
    s1.fss_sent == [] /\
    s1.fss_pending == plan /\
    s1.fss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent FtpSendBlock ->
    (exists blk. ftp_server_send s0 s1 blk /\ out.SM.so_wire_outputs == [blk]) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent FtpComplete ->
    Some? s0.fss_filename /\
    s0.fss_status == FT.FT_InProgress /\
    s0.fss_pending == [] /\
    s1.fss_filename == s0.fss_filename /\
    s1.fss_sent == s0.fss_sent /\
    s1.fss_pending == [] /\
    s1.fss_status == FT.FT_Completed /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent FtpAbort ->
    s1.fss_filename == s0.fss_filename /\
    s1.fss_sent == s0.fss_sent /\
    s1.fss_pending == s0.fss_pending /\
    s1.fss_status == FT.FT_Aborted /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent _ ->
    False

noextract
let ftp_server_state_machine
  : SM.state_machine ftp_server_state ftp_block ftp_server_local unit =
  {
    SM.sm_initial_state = ftp_server_initial;
    SM.sm_step = ftp_server_step;
  }

noextract
let ftp_server_wfsm
  : WFSM.wire_format_state_machine ftp_server_state ftp_block ftp_server_local unit =
  {
    WFSM.wfsm_state_machine = ftp_server_state_machine;
    WFSM.wfsm_wire_format = ftp_block_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   Client state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ftp_client_state = {
  fcs_filename : option TCP.bytes;   // file the client requested
  fcs_received : list TCP.bytes;     // data payloads received so far, in order
  fcs_status   : FT.ft_status;
}

let ftp_client_initial : ftp_client_state = {
  fcs_filename = None;
  fcs_received = [];
  fcs_status   = FT.FT_InProgress;
}

noeq
type ftp_client_local =
  | FtpClientRetr : filename:TCP.bytes -> ftp_client_local

let ftp_client_step
  (s0:ftp_client_state)
  (ev:SM.event ftp_block ftp_client_local)
  (s1:ftp_client_state)
  (out:SM.step_output ftp_block unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (FtpClientRetr filename) ->
    s0.fcs_filename == None /\
    s1.fcs_filename == Some filename /\
    s1.fcs_received == [] /\
    s1.fcs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent blk ->
    Some? s0.fcs_filename /\
    s0.fcs_status == FT.FT_InProgress /\
    s1.fcs_filename == s0.fcs_filename /\
    s1.fcs_received == L.append s0.fcs_received [block_payload blk] /\
    s1.fcs_status == (if descriptor_is_eof blk.descriptor
                      then FT.FT_Completed else FT.FT_InProgress) /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent _ ->
    False

noextract
let ftp_client_state_machine
  : SM.state_machine ftp_client_state ftp_block ftp_client_local unit =
  {
    SM.sm_initial_state = ftp_client_initial;
    SM.sm_step = ftp_client_step;
  }

noextract
let ftp_client_wfsm
  : WFSM.wire_format_state_machine ftp_client_state ftp_block ftp_client_local unit =
  {
    WFSM.wfsm_state_machine = ftp_client_state_machine;
    WFSM.wfsm_wire_format = ftp_block_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   file_transfer instance for the server
   ─────────────────────────────────────────────────────────────────────────── *)

(* Classify a data-connection block: FTP block mode carries no on-wire index, so
   data is ordered positionally (`FT_Data None`). *)
let ftp_classify (blk:ftp_block) : FT.ft_packet =
  FT.FT_Data None (block_payload blk)

let ftp_is_timeout (_:ftp_server_local) : bool = false

let ftp_server_law_initial (_:unit)
  : Lemma
      (ensures
        ftp_server_project ftp_server_state_machine.SM.sm_initial_state == FT.ft_view_empty)
=
  ()

#push-options "--fuel 2 --ifuel 2"

let ftp_server_law_step
  (st0:ftp_server_state)
  (ev:SM.event ftp_block ftp_server_local)
  (st1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  : Lemma
      (requires ftp_server_state_machine.SM.sm_step st0 ev st1 out)
      (ensures
        FT.ft_view_step ftp_block_size None
          (ftp_server_project st0) (ftp_server_project st1))
=
  match ev with
  | SM.LocalEvent (FtpStartRetr filename plan) ->
    introduce exists fn ct.
      FT.ft_step_request fn ct (ftp_server_project st0) (ftp_server_project st1)
    with filename (FT.ft_concat plan) and ()
  | SM.LocalEvent FtpSendBlock ->
    eliminate exists blk. ftp_server_send st0 st1 blk /\ out.SM.so_wire_outputs == [blk]
    returns
      FT.ft_view_step ftp_block_size None
        (ftp_server_project st0) (ftp_server_project st1)
    with _.
    (match st0.fss_pending with
     | [] -> ()
     | h :: rest ->
       lemma_ft_concat_append st0.fss_sent [h];
       lemma_ft_concat_append st0.fss_sent (h :: rest);
       Seq.append_empty_r h;
       Seq.append_assoc (FT.ft_concat st0.fss_sent) h (FT.ft_concat rest);
       L.append_assoc st0.fss_sent [h] rest;
       lemma_bytes_extends_append
         (FT.ft_concat (L.append st0.fss_sent [h]))
         (FT.ft_concat rest);
       (match ftp_server_content st0 with
        | Some content ->
          FT.lemma_bytes_extends_prefix_agree
            (FT.ft_concat (L.append st0.fss_sent [h])) content);
       assert (FT.ft_step_send_data ftp_block_size None h
                 (ftp_server_project st0) (ftp_server_project st1));
       introduce exists payload.
         FT.ft_step_send_data ftp_block_size None payload
           (ftp_server_project st0) (ftp_server_project st1)
       with h and ())
  | SM.LocalEvent FtpComplete ->
    L.append_l_nil st0.fss_sent;
    (match ftp_server_content st0 with
     | Some content ->
       Seq.slice_length content;
       assert (FT.reassembly_exact st0.fss_sent content));
    assert (FT.ft_step_complete (ftp_server_project st0) (ftp_server_project st1))
  | SM.LocalEvent FtpAbort ->
    assert (FT.ft_step_error (ftp_server_project st0) (ftp_server_project st1))
  | SM.WireEvent _ ->
    ()

#pop-options

let ftp_server_law_data_wire
  (st0:ftp_server_state)
  (ev:SM.event ftp_block ftp_server_local)
  (st1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  (msg:ftp_block)
  : Lemma
      (requires
        ftp_server_state_machine.SM.sm_step st0 ev st1 out /\
        L.memP msg out.SM.so_wire_outputs /\
        FT.FT_Data? (ftp_classify msg))
      (ensures
        (match ftp_classify msg with
         | FT.FT_Data index payload ->
           (match index with
            | Some i -> i == L.length (ftp_server_project st0).FT.ftv_blocks + 1
            | None -> True) /\
           (ftp_server_project st1).FT.ftv_blocks ==
             L.append (ftp_server_project st0).FT.ftv_blocks [payload]
         | _ -> True))
=
  match ev with
  | SM.LocalEvent FtpSendBlock ->
    eliminate exists blk. ftp_server_send st0 st1 blk /\ out.SM.so_wire_outputs == [blk]
    returns
      (match ftp_classify msg with
       | FT.FT_Data index payload ->
         (match index with
          | Some i -> i == L.length (ftp_server_project st0).FT.ftv_blocks + 1
          | None -> True) /\
         (ftp_server_project st1).FT.ftv_blocks ==
           L.append (ftp_server_project st0).FT.ftv_blocks [payload]
       | _ -> True)
    with _. ()
  | _ -> ()

let ftp_server_law_ack_wire
  (st0:ftp_server_state)
  (st1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  (msg:ftp_block)
  : Lemma
      (requires
        ftp_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_Ack? (ftp_classify msg))
      (ensures
        (match ftp_classify msg with
         | FT.FT_Ack index ->
           (ftp_server_project st0).FT.ftv_acked < index /\
           index <= L.length (ftp_server_project st0).FT.ftv_blocks /\
           (ftp_server_project st1).FT.ftv_acked == index
         | _ -> True))
=
  ()

let ftp_server_law_request_wire
  (st0:ftp_server_state)
  (st1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  (msg:ftp_block)
  : Lemma
      (requires
        ftp_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_ReadRequest? (ftp_classify msg))
      (ensures
        (match ftp_classify msg with
         | FT.FT_ReadRequest filename ->
           (ftp_server_project st1).FT.ftv_filename == Some filename /\
           (ftp_server_project st1).FT.ftv_blocks == [] /\
           (ftp_server_project st1).FT.ftv_acked == 0
         | _ -> True))
=
  ()

let ftp_server_law_timeout
  (st0:ftp_server_state)
  (le:ftp_server_local)
  (st1:ftp_server_state)
  (out:SM.step_output ftp_block unit)
  (msg:ftp_block)
  : Lemma
      (requires
        ftp_server_state_machine.SM.sm_step st0 (SM.LocalEvent le) st1 out /\
        ftp_is_timeout le)
      (ensures
        ftp_server_project st1 == ftp_server_project st0 /\
        (L.memP msg out.SM.so_wire_outputs /\ FT.FT_Data? (ftp_classify msg) ==>
          (match ftp_classify msg with
           | FT.FT_Data index payload ->
             (match index with
              | Some i -> FT.ft_block_at (ftp_server_project st0).FT.ftv_blocks i == Some payload
              | None -> True)
           | _ -> True)))
=
  ()

noextract
let ftp_server_file_transfer
  : FT.file_transfer ftp_server_state ftp_block ftp_server_local unit ftp_server_wfsm =
  {
    FT.ft_block_size = ftp_block_size;
    FT.ft_window = None;
    FT.ft_classify = ftp_classify;
    FT.ft_is_timeout = ftp_is_timeout;
    FT.ft_project = ftp_server_project;
    FT.ft_law_initial = ftp_server_law_initial;
    FT.ft_law_step = ftp_server_law_step;
    FT.ft_law_data_wire = ftp_server_law_data_wire;
    FT.ft_law_ack_wire = ftp_server_law_ack_wire;
    FT.ft_law_request_wire = ftp_server_law_request_wire;
    FT.ft_law_timeout = ftp_server_law_timeout;
  }

(* Capstone: instantiating the generic reconstitution theorem for the FTP server.
   In any reachable server state that is serving a file, the raw reassembly of the
   data blocks it has sent — in order — agrees with that file on their common
   prefix, and reconstitutes the exact file (by truncation to the declared length,
   an identity here since FTP block mode is unpadded) once the transfer has
   completed via the explicit FtpComplete (226) step. *)
let lemma_ftp_server_reconstitution (st:ftp_server_state)
  : Lemma
      (requires SM.valid_state ftp_server_state_machine st)
      (ensures
        (match (ftp_server_project st).FT.ftv_content with
         | None -> True
         | Some content ->
           FT.bytes_prefix_agree
             (FT.ft_concat (ftp_server_project st).FT.ftv_blocks) content /\
           ((ftp_server_project st).FT.ftv_status == FT.FT_Completed ==>
             FT.reassembly_exact (ftp_server_project st).FT.ftv_blocks content)))
=
  FT.lemma_ft_reconstitution ftp_server_file_transfer st
