module Common.FileTransfer

(**
  A type class specifying verified *file-transfer* protocols on top of the
  wire-level state-machine refinement framework of `Common.WireFormatStateMachine`.

  ── Motivation / protocol family ────────────────────────────────────────────
  IETF TFTP (RFC 1350) has a very simple, very common structure:

    * the client sends a *read request* (RRQ) naming a file;
    * the server replies with a stream of *data* packets, each carrying a
      monotonically increasing *block number* and up to `block_size` payload
      bytes;
    * the client *acknowledges* each block (by block number);
    * a data packet whose payload is shorter than `block_size` marks the end of
      the transfer;
    * lost packets are recovered by *timeout-driven retransmission* of the last
      unacknowledged packet.

  Many other file-transfer protocols share exactly this shape — a block-oriented
  reliable transfer over an unreliable datagram/serial link, using a per-block
  *ordering mechanism* (block index or byte offset), positive acknowledgments,
  timeout retransmission, and a short final block:

    * TFTP (RFC 1350) and its windowsize option (RFC 7440);
    * XMODEM / YMODEM / ZMODEM (serial links, numbered 128/1K blocks + ACK/NAK);
    * Kermit (sequence-numbered packets, ACK/NAK, windowing);
    * Saratoga (UDP, byte-offset DATA descriptors + STATUS acks);
    * FSP, the File Service Protocol (UDP, offset-based request/response).

  This module abstracts that common structure once, as a type class parametric in
  a `wire_format_state_machine` (the "state-machine protocol specification"), so a
  concrete protocol such as TFTP can later be shown to be a *file transfer* by
  providing an instance.  We deliberately model the read/download direction
  (server → client); the write/upload direction is symmetric.

  ── What the class guarantees ───────────────────────────────────────────────
  The central property is that the server sends the client the data packets with
  an ORDERING MECHANISM (the block index) that lets the client RECONSTITUTE the
  requested file: the concatenation of the delivered block payloads, taken in
  block-index order, is always a prefix of the requested file, and equals the
  whole file once the transfer completes.  This is proved once, generically, as
  `lemma_ft_reconstitution`, so an instance only needs to exhibit the projection
  and discharge the (per-step) laws.

  This module follows the state-machine refinement methodology described in
  https://fstar-lang.org/tutorial/book/agentic/agentic_state_machines.html and
  reuses the abstractions of `common/Common.StateMachine.fst`,
  `common/Common.WireFormat.fst`, and `common/Common.WireFormatStateMachine.fst`.
**)

module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot
module Seq = FStar.Seq
module SM = Common.StateMachine
module TCP = Common.TCP
module U8 = FStar.UInt8
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

(* ───────────────────────────────────────────────────────────────────────────
   The file-transfer *view* of a single wire message.

   `ft_classify` (a field of the class below) maps a concrete `wire_message` to
   one of these roles, exposing the fields a file-transfer protocol cares about:
   the requested filename, a data block's index+payload, or an ack's index.  The
   index is the ordering mechanism used to reassemble the file.
   ─────────────────────────────────────────────────────────────────────────── *)
noeq
type ft_packet =
  | FT_ReadRequest : filename:TCP.bytes -> ft_packet
  | FT_Data        : index:nat -> payload:TCP.bytes -> ft_packet
  | FT_Ack         : index:nat -> ft_packet
  | FT_Error       : ft_packet
  | FT_Other       : ft_packet

(* Progress of a transfer. *)
type ft_status =
  | FT_InProgress
  | FT_Completed
  | FT_Aborted

(* ───────────────────────────────────────────────────────────────────────────
   The abstract file-transfer view of a protocol *state*.

   This is the ghost bookkeeping that a concrete protocol state must be able to
   project to (via `ft_project`).  It records the file being served and the
   ordered list of data-block payloads delivered so far, from which the client
   reconstitutes the file.
   ─────────────────────────────────────────────────────────────────────────── *)
noeq
type ft_view = {
  ftv_filename : option TCP.bytes;   // file named by the client's read request
  ftv_content  : option TCP.bytes;   // full intended contents of that file
  ftv_blocks   : list TCP.bytes;     // payloads of data blocks sent so far, in
                                     // block order: index i (1-based) is the
                                     // i-th element — the ORDERING MECHANISM
  ftv_acked    : nat;                // number of leading blocks the client acked
  ftv_status   : ft_status;          // progress of the transfer
}

(* The empty view: nothing requested and nothing transferred yet. *)
let ft_view_empty : ft_view = {
  ftv_filename = None;
  ftv_content  = None;
  ftv_blocks   = [];
  ftv_acked    = 0;
  ftv_status   = FT_InProgress;
}

(* ───────────────────────────────────────────────────────────────────────────
   Reassembly: concatenating the block payloads in block order reconstitutes the
   received prefix of the file.
   ─────────────────────────────────────────────────────────────────────────── *)
let rec ft_concat (blocks:list TCP.bytes)
  : Tot TCP.bytes (decreases blocks) =
  match blocks with
  | [] -> Seq.empty
  | b :: bs -> Seq.append b (ft_concat bs)

(* The (1-based) index-th block, if it has been delivered. *)
let ft_block_at (blocks:list TCP.bytes) (index:nat)
  : GTot (option TCP.bytes) =
  if 1 <= index && index <= L.length blocks
  then Some (L.index blocks (index - 1))
  else None

(* The empty sequence is a prefix of any byte sequence. *)
let lemma_ft_bytes_extends_empty (b:TCP.bytes)
  : Lemma (TCP.bytes_extends Seq.empty b)
          [SMTPat (TCP.bytes_extends Seq.empty b)] =
  assert (Seq.length (Seq.slice b 0 0) == 0);
  Seq.lemma_eq_intro (Seq.empty <: Seq.seq U8.t) (Seq.slice b 0 0)

(* Appending one block increments the block count by one. *)
let lemma_ft_append_singleton_length (l:list TCP.bytes) (x:TCP.bytes)
  : Lemma (L.length (L.append l [x]) == L.length l + 1)
          [SMTPat (L.length (L.append l [x]))] =
  L.append_length l [x]

(* ───────────────────────────────────────────────────────────────────────────
   Allowed abstract file-transfer transitions on views.

   Every concrete protocol step (see law `ft_law_step`) must project to one of
   these.  Each is witness-parametric so the preservation proofs are direct.
   ─────────────────────────────────────────────────────────────────────────── *)

(* A read request starts the transfer: it records the requested file (and its
   ghost contents) and (re)starts delivery from block 1. *)
let ft_step_request (filename content:TCP.bytes) (v0 v1:ft_view) : prop =
  v0.ftv_content  == None /\
  v1.ftv_filename == Some filename /\
  v1.ftv_content  == Some content /\
  v1.ftv_blocks   == [] /\
  v1.ftv_acked    == 0 /\
  v1.ftv_status   == FT_InProgress

(* Flow control: at most `window` blocks may be in flight (sent but not yet
   acknowledged).  `None` means an *unbounded* window: the transport itself is
   reliable and provides flow control (e.g. FTP block mode over TCP), so the
   application performs no windowing.  `Some 1` recovers TFTP's stop-and-wait;
   `Some n` with n > 1 models windowed variants (RFC 7440 / ZMODEM / Kermit). *)
let ft_in_flight_ok (window:option pos) (in_flight:int) : prop =
  match window with
  | None -> True
  | Some w -> in_flight < w

(* The server sends the next data block.  This is where ORDERING and REASSEMBLY
   are enforced:
     * the new block is appended after all previous ones (consecutive index);
     * its payload is at most `block_size` bytes, and a strictly shorter payload
       is the final block;
     * flow control allows at most `window` unacknowledged blocks in flight
       (`Some 1` recovers TFTP's stop-and-wait; larger finite windows model RFC
       7440 / ZMODEM / Kermit; `None` is an unbounded, transport-reliable window
       as in FTP block mode over TCP);
     * the running reassembly stays a prefix of the file, and equals the whole
       file exactly when the final (short) block is sent. *)
let ft_step_send_data (block_size:nat) (window:option pos) (payload:TCP.bytes) (v0 v1:ft_view)
  : prop =
  match v0.ftv_content with
  | None -> False
  | Some content ->
    v0.ftv_status == FT_InProgress /\
    ft_in_flight_ok window (L.length v0.ftv_blocks - v0.ftv_acked) /\
    Seq.length payload <= block_size /\
    v1.ftv_filename == v0.ftv_filename /\
    v1.ftv_content  == v0.ftv_content /\
    v1.ftv_blocks   == L.append v0.ftv_blocks [payload] /\
    v1.ftv_acked    == v0.ftv_acked /\
    v1.ftv_status   == (if Seq.length payload < block_size
                        then FT_Completed else FT_InProgress) /\
    TCP.bytes_extends (ft_concat v1.ftv_blocks) content /\
    (Seq.length payload < block_size ==>
       Seq.equal (ft_concat v1.ftv_blocks) content)

(* The client acknowledges blocks: a cumulative positive ack advances the
   acknowledged prefix to `index`, which must name blocks that were actually
   sent and not already fully acknowledged. *)
let ft_step_recv_ack (index:nat) (v0 v1:ft_view) : prop =
  v0.ftv_acked < index /\
  index <= L.length v0.ftv_blocks /\
  v1.ftv_filename == v0.ftv_filename /\
  v1.ftv_content  == v0.ftv_content /\
  v1.ftv_blocks   == v0.ftv_blocks /\
  v1.ftv_acked    == index /\
  v1.ftv_status   == v0.ftv_status

(* An error aborts the transfer without delivering more content. *)
let ft_step_error (v0 v1:ft_view) : prop =
  v1.ftv_filename == v0.ftv_filename /\
  v1.ftv_content  == v0.ftv_content /\
  v1.ftv_blocks   == v0.ftv_blocks /\
  v1.ftv_acked    == v0.ftv_acked /\
  v1.ftv_status   == FT_Aborted

(* A single legal abstract file-transfer step.  The `v1 == v0` stutter case
   subsumes timeout-driven retransmission: retransmitting an already-sent block
   leaves the abstract view (delivered blocks, acked prefix, file) unchanged.
   The wire-level effect of a timeout is pinned separately by `ft_law_timeout`. *)
let ft_view_step (block_size:nat) (window:option pos) (v0 v1:ft_view) : prop =
  v1 == v0 \/
  (exists filename content. ft_step_request filename content v0 v1) \/
  (exists payload. ft_step_send_data block_size window payload v0 v1) \/
  (exists index. ft_step_recv_ack index v0 v1) \/
  ft_step_error v0 v1

(* ───────────────────────────────────────────────────────────────────────────
   The consistency invariant carried by every reachable view, and its
   preservation under `ft_view_step`.  The Some-branch is the reconstitution
   guarantee: the reassembled blocks are a prefix of the file, exact on
   completion.
   ─────────────────────────────────────────────────────────────────────────── *)
let ft_view_consistent (v:ft_view) : prop =
  match v.ftv_content with
  | None ->
    v.ftv_blocks == [] /\
    v.ftv_acked == 0 /\
    (v.ftv_status == FT_InProgress \/ v.ftv_status == FT_Aborted)
  | Some content ->
    Some? v.ftv_filename /\
    v.ftv_acked <= L.length v.ftv_blocks /\
    TCP.bytes_extends (ft_concat v.ftv_blocks) content /\
    (v.ftv_status == FT_Completed ==> Seq.equal (ft_concat v.ftv_blocks) content)

let lemma_ft_view_step_preserves_consistent
  (block_size:nat) (window:option pos) (v0 v1:ft_view)
  : Lemma (requires ft_view_consistent v0 /\ ft_view_step block_size window v0 v1)
          (ensures ft_view_consistent v1) =
  ()

(* ───────────────────────────────────────────────────────────────────────────
   The file-transfer type class.

   It takes as an argument (index) `system`, the wire-level state-machine
   protocol specification the transfer runs on, and describes the file-transfer
   structure of that protocol:

     * data fields `ft_block_size`, `ft_window` fix the transfer parameters;
     * `ft_classify` reads a wire message as a file-transfer packet (this is
       where the on-the-wire ordering mechanism — the block index — lives);
     * `ft_is_timeout` marks which local events are retransmission timeouts;
     * `ft_project` maps a protocol state to its abstract file-transfer view;
     * the `ft_law_*` fields are the proof obligations an instance must discharge.
   ─────────────────────────────────────────────────────────────────────────── *)
noextract
class file_transfer
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  =
{
  (* The maximum data-block payload size, in bytes (512 for stock TFTP).  A block
     with strictly fewer bytes ends the transfer. *)
  ft_block_size: n:nat{n >= 1};

  (* Flow-control window: how many blocks may be in flight unacknowledged.
     `Some 1` is TFTP's classic stop-and-wait; `Some n` models windowed variants;
     `None` is an unbounded, transport-reliable window (e.g. FTP block mode over
     TCP, where TCP provides ordering and flow control). *)
  ft_window: option pos;

  (* File-transfer reading of a wire message. *)
  ft_classify: wire_message -> GTot ft_packet;

  (* Which local events are retransmission timeouts. *)
  ft_is_timeout: local_event -> GTot bool;

  (* Abstract file-transfer view of a protocol state. *)
  ft_project: state -> GTot ft_view;

  (* (L0) The initial protocol state has the empty view. *)
  ft_law_initial:
    unit ->
      Lemma (ensures
        ft_project system.WFSM.wfsm_state_machine.SM.sm_initial_state == ft_view_empty);

  (* (L1) Every protocol step projects to a legal abstract file-transfer step:
     request / ordered send-data / cumulative ack / abort (timeouts stutter the
     view).  This is the single obligation that makes `ft_project` a genuine
     file-transfer invariant. *)
  ft_law_step:
    st0:state ->
    ev:SM.event wire_message local_event ->
    st1:state ->
    out:SM.step_output wire_message local_output ->
      Lemma
        (requires system.WFSM.wfsm_state_machine.SM.sm_step st0 ev st1 out)
        (ensures ft_view_step ft_block_size ft_window (ft_project st0) (ft_project st1));

  (* (L2) A data message emitted on the wire carries its true position: its block
     index is the successor of the number of blocks already delivered, and its
     payload is the block appended to the delivered prefix.  This ties the
     on-the-wire ordering mechanism (block index) to reassembly order. *)
  ft_law_data_wire:
    st0:state ->
    ev:SM.event wire_message local_event ->
    st1:state ->
    out:SM.step_output wire_message local_output ->
    msg:wire_message ->
      Lemma
        (requires
          system.WFSM.wfsm_state_machine.SM.sm_step st0 ev st1 out /\
          L.memP msg out.SM.so_wire_outputs /\
          FT_Data? (ft_classify msg))
        (ensures
          (match ft_classify msg with
           | FT_Data index payload ->
             index == L.length (ft_project st0).ftv_blocks + 1 /\
             (ft_project st1).ftv_blocks == L.append (ft_project st0).ftv_blocks [payload]
           | _ -> True));

  (* (L3) An acknowledgment consumed from the wire advances the acknowledged
     prefix to the block index it names. *)
  ft_law_ack_wire:
    st0:state ->
    st1:state ->
    out:SM.step_output wire_message local_output ->
    msg:wire_message ->
      Lemma
        (requires
          system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
          FT_Ack? (ft_classify msg))
        (ensures
          (match ft_classify msg with
           | FT_Ack index ->
             (ft_project st0).ftv_acked < index /\
             index <= L.length (ft_project st0).ftv_blocks /\
             (ft_project st1).ftv_acked == index
           | _ -> True));

  (* (L4) A read request consumed from the wire starts the transfer under the
     requested filename, delivering from block 1. *)
  ft_law_request_wire:
    st0:state ->
    st1:state ->
    out:SM.step_output wire_message local_output ->
    msg:wire_message ->
      Lemma
        (requires
          system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
          FT_ReadRequest? (ft_classify msg))
        (ensures
          (match ft_classify msg with
           | FT_ReadRequest filename ->
             (ft_project st1).ftv_filename == Some filename /\
             (ft_project st1).ftv_blocks == [] /\
             (ft_project st1).ftv_acked == 0
           | _ -> True));

  (* (L5) A timeout is an idempotent retransmission: it leaves the abstract view
     unchanged, and any data block it re-emits is one already sent (same index,
     same payload).  This models timeout-driven recovery without regressing or
     corrupting the reconstructed file. *)
  ft_law_timeout:
    st0:state ->
    le:local_event ->
    st1:state ->
    out:SM.step_output wire_message local_output ->
    msg:wire_message ->
      Lemma
        (requires
          system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.LocalEvent le) st1 out /\
          ft_is_timeout le)
        (ensures
          ft_project st1 == ft_project st0 /\
          (L.memP msg out.SM.so_wire_outputs /\ FT_Data? (ft_classify msg) ==>
            (match ft_classify msg with
             | FT_Data index payload ->
               ft_block_at (ft_project st0).ftv_blocks index == Some payload
             | _ -> True)));
}

(* ───────────────────────────────────────────────────────────────────────────
   Derived guarantees.

   From L0 and L1 alone, `ft_project` is a genuine invariant: every reachable
   protocol state has a consistent view, hence the client always reassembles a
   prefix of the requested file, and the whole file once the transfer completes.
   These theorems are proved generically here, so an instance gets them for free.
   ─────────────────────────────────────────────────────────────────────────── *)

let rec lemma_ft_trace_preserves_consistent
  (#state #wire_message #local_event #local_output:Type0)
  (#system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ftc:file_transfer state wire_message local_event local_output system)
  (st0:state)
  (trace:list (SM.transition state wire_message local_event local_output))
  (st1:state)
  : Lemma
      (requires
        SM.trace_reaches system.WFSM.wfsm_state_machine st0 trace st1 /\
        ft_view_consistent (ftc.ft_project st0))
      (ensures ft_view_consistent (ftc.ft_project st1))
      (decreases trace) =
  match trace with
  | [] -> ()
  | tr :: rest ->
    ftc.ft_law_step st0 tr.SM.tr_event tr.SM.tr_next_state tr.SM.tr_output;
    lemma_ft_view_step_preserves_consistent
      ftc.ft_block_size ftc.ft_window
      (ftc.ft_project st0) (ftc.ft_project tr.SM.tr_next_state);
    lemma_ft_trace_preserves_consistent ftc tr.SM.tr_next_state rest st1

let lemma_ft_valid_state_consistent
  (#state #wire_message #local_event #local_output:Type0)
  (#system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ftc:file_transfer state wire_message local_event local_output system)
  (st:state)
  : Lemma
      (requires SM.valid_state system.WFSM.wfsm_state_machine st)
      (ensures ft_view_consistent (ftc.ft_project st)) =
  let sm = system.WFSM.wfsm_state_machine in
  ftc.ft_law_initial ();
  assert (ft_view_consistent ft_view_empty);
  assert (SM.state_evolves sm sm.SM.sm_initial_state st);
  let trace =
    ID.indefinite_description_ghost
      (list (SM.transition state wire_message local_event local_output))
      (fun trace -> SM.trace_reaches sm sm.SM.sm_initial_state trace st) in
  lemma_ft_trace_preserves_consistent ftc sm.SM.sm_initial_state trace st

(* The audit-facing theorem: in any reachable state whose transfer has a known
   file, the concatenation of the data blocks the server sent — taken in
   block-index order — is a prefix of the requested file, and equals the whole
   file once the transfer has completed.  I.e. the client can always reconstitute
   (a prefix of) the requested file from the ordered blocks it received. *)
let lemma_ft_reconstitution
  (#state #wire_message #local_event #local_output:Type0)
  (#system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ftc:file_transfer state wire_message local_event local_output system)
  (st:state)
  : Lemma
      (requires SM.valid_state system.WFSM.wfsm_state_machine st)
      (ensures
        (match (ftc.ft_project st).ftv_content with
         | None -> True
         | Some content ->
           TCP.bytes_extends (ft_concat (ftc.ft_project st).ftv_blocks) content /\
           ((ftc.ft_project st).ftv_status == FT_Completed ==>
             Seq.equal (ft_concat (ftc.ft_project st).ftv_blocks) content))) =
  lemma_ft_valid_state_consistent ftc st
