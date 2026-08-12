module YModem.Impl.Server.Endpoint

(**
  YMODEM *server* (sender) driver-facing endpoint: a full 28-field instance of
  `Common.ProtocolEndpoint.protocol_endpoint` over the committed dictionary
  `YModem.Impl.Server.CanonicalProtocol.ymodem_server_protocol_implementation`.

  This is the HARDEST endpoint: it SCHEDULES local send events (Server_start,
  Server_send, Server_eot, Server_complete) and maintains a refinement invariant
  `server_plan_ok` coupling a concrete send-plan cursor to the ghost ARQ state.

  Tier-1 simplification: NO Server_timeout / retransmission.  We assume a
  lossless cooperative peer, so the endpoint schedules only
  Server_start / Server_send / Server_eot / Server_complete locally, and handles
  ACK/NAK/CAN on the network path (a CAN drives Server_abort inside
  `pi_process_network`).  `Server_timeout` and local `Server_abort` are never
  scheduled (dead branches, discharged by `unreachable ()` / vacuous coupling).

  Structural mirror of the just-built client endpoint
  `YModem.Impl.Client.Endpoint.fst`, retyped to the server types, with the extra
  machinery for the coupling:

    * `server_plan_ok cfg st` : the crux coupling, keyed on `st.yss_filename`;
    * a concrete cursor cell (blocks sent so far == `L.length st.yss_sent`) and a
      started flag cell (== 1uy iff `Some? st.yss_filename`), both in
      `pe_frame_ready`, agreeing with `st` via `cells_ok`;
    * `pe_next_action` reads the status cell + started + cursor and schedules;
    * `pe_prepare_local` (Server_send) COPIES block `cursor` out of the padded
      file into the payload buffer and proves `hd pending == block cursor` (the
      coupling), discharging `local_pre_ok Server_send`;
    * `pe_finish_local_action` (Server_send) increments the cursor and re-proves
      the coupling at cursor+1 via `Plan.lemma_send_shift`.

  Verified but NOT extracted (a protocol_endpoint over a protocol_implementation
  dictionary is not Low-star).
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Common.ProtocolImplementation
module PE = Common.ProtocolEndpoint
module SZ = FStar.SizeT
module Seq = FStar.Seq
module TCP = Common.TCP
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module L = FStar.List.Tot
module FT = Common.FileTransfer
module Math = FStar.Math.Lemmas

module YP = YModem.Protocol
module CC = YModem.Impl.Server.CanonicalProtocol
module Log = YModem.Impl.Server.Log
module Plan = YModem.Impl.Server.Plan

open YModem.Wire.Generated.Ymodem_message

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint config (§ pe_config) — the concrete send plan
   ─────────────────────────────────────────────────────────────────────────── *)

(* The padded file (scfg_nblocks * 128 bytes), its byte contents, the block
   count (as a nat and a runtime SizeT), the file name and declared length.
   `scfg_contents` is a plain (non-erased) `TCP.bytes`: the endpoint is
   `noextract`, so we avoid `Ghost.reveal` clutter. *)
noeq
type ymodem_server_config = {
  scfg_file       : Vec.vec U8.t;   // the padded file bytes (scfg_nblocks*128)
  scfg_contents   : TCP.bytes;      // == the pts_to value of scfg_file
  scfg_nblocks    : nat;            // number of 128-byte blocks
  scfg_nblocks_sz : SZ.t;           // == scfg_nblocks, for runtime comparison
  scfg_filename   : TCP.bytes;      // file name
  scfg_len        : nat;            // declared content length
}

let scfg_wf (cfg:ymodem_server_config) : prop =
  Seq.length cfg.scfg_contents == cfg.scfg_nblocks * 128 /\
  SZ.v cfg.scfg_nblocks_sz == cfg.scfg_nblocks /\
  SZ.fits (cfg.scfg_nblocks * 128)

(* The whole plan the sender queues at Server_start. *)
let plan_of (cfg:ymodem_server_config) : list TCP.bytes =
  Plan.blocks_of cfg.scfg_contents 0 cfg.scfg_nblocks

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint frame (§ pe_frame): the persistent concrete state + I/O buffers
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_server_endpoint_frame = {
  sef_cursor  : Vec.vec SZ.t;   // single cell: blocks sent so far (0..nblocks)
  sef_started : Vec.vec U8.t;   // single cell: 1uy iff Server_start has fired
  sef_blk     : array U8.t;     // 128-byte payload scratch (yslf_buf)
  sef_ysnf    : array U8.t;     // 128-byte scratch handed to process_network
  sef_out     : array U8.t;     // 133-byte local/network output buffer
  sef_in      : array U8.t;     // 1-byte control input (ACK/NAK/CAN)
}

(* ───────────────────────────────────────────────────────────────────────────
   THE COUPLING INVARIANT (the crux)
   ─────────────────────────────────────────────────────────────────────────── *)

(* `server_plan_ok cfg st` : the ghost ARQ state agrees with the send plan.
   Keyed on `st.yss_filename`:
     * None  (not started)  ⟹ st is exactly the initial state;
     * Some fn (started) and InProgress ⟹ the file/len match the config, the
       cursor `L.length yss_sent` is in range, and `yss_sent`/`yss_pending` are
       the low/high `blocks_of` split at the cursor; in the EOT phase all blocks
       are sent.
   Marked `unfold` so SMT sees the match transparently. *)
unfold
let server_plan_ok (cfg:ymodem_server_config) (st:YP.ymodem_server_state) : prop =
  match st.YP.yss_filename with
  | None -> st == YP.ymodem_server_initial
  | Some fnm ->
    st.YP.yss_status == FT.FT_InProgress ==>
      (fnm == cfg.scfg_filename /\
       st.YP.yss_len == cfg.scfg_len /\
       L.length st.YP.yss_sent <= cfg.scfg_nblocks /\
       st.YP.yss_sent == Plan.blocks_of cfg.scfg_contents 0 (L.length st.YP.yss_sent) /\
       st.YP.yss_pending == Plan.blocks_of cfg.scfg_contents (L.length st.YP.yss_sent) cfg.scfg_nblocks /\
       (st.YP.yss_phase == YP.SP_Eot ==> L.length st.YP.yss_sent == cfg.scfg_nblocks))

(* `started_of b` : the started flag byte 0uy/1uy read as a bool. *)
unfold
let started_of (b:U8.t) : bool = (b = 1uy)

(* The concrete cursor/started cells agree with the ghost state. *)
unfold
let cells_ok (cfg:ymodem_server_config) (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t)
             (st:YP.ymodem_server_state) : prop =
  Seq.length cv == 1 /\ Seq.length bv == 1 /\
  (Seq.index bv 0 == 0uy \/ Seq.index bv 0 == 1uy) /\
  (started_of (Seq.index bv 0) <==> Some? st.YP.yss_filename) /\
  SZ.v (Seq.index cv 0) == L.length st.YP.yss_sent

(* ───────────────────────────────────────────────────────────────────────────
   Persistent slprops (§ pe_frame_ready, pe_io_ready)
   ─────────────────────────────────────────────────────────────────────────── *)

(* frame_ready [STATE-DEPENDENT]: owns the two cells + the file + the two 128-byte
   scratches, and carries the coupling + cell agreement. *)
let ymodem_server_frame_ready
  (_i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (st:YP.ymodem_server_state)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (blkd:Seq.seq U8.t) (ysnfd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_blk blkd **
    pts_to frame.sef_ysnf ysnfd **
    pure (Seq.length blkd == 128 /\ Seq.length ysnfd == 128 /\
          scfg_wf cfg /\ cells_ok cfg cv bv st /\ server_plan_ok cfg st)

(* io_ready [STATE-INDEPENDENT]: owns the channel + the 133-byte output + the
   1-byte input.  The raw received history is existential. *)
let ymodem_server_io_ready
  (_i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (frame:ymodem_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_server_state)
  : slprop =
  exists* (raw:TCP.bytes) (outd:Seq.seq U8.t) (ind:Seq.seq U8.t).
    TCP.is_channel ch raw sent **
    pts_to frame.sef_out outd **
    pts_to frame.sef_in ind **
    pure (Seq.length outd == 133 /\ Seq.length ind == 1)

(* ───────────────────────────────────────────────────────────────────────────
   Per-event scheduling facts (consumed by prepare_local) and continuation facts
   (consumed by finish_local_action).
   ─────────────────────────────────────────────────────────────────────────── *)

(* `server_local_ready cfg ev st` : the st-facts `pe_next_action` derives from
   the status cell + coupling before scheduling `EndpointLocal ev`.  For the two
   never-scheduled events it is `False` (dead branches). *)
unfold
let server_local_ready (cfg:ymodem_server_config) (ev:YP.ymodem_server_local)
                       (st:YP.ymodem_server_state) : prop =
  match ev with
  | YP.Server_start filename len plan ->
    st == YP.ymodem_server_initial /\
    filename == cfg.scfg_filename /\ len == cfg.scfg_len /\ plan == plan_of cfg
  | YP.Server_send ->
    Some? st.YP.yss_filename /\ st.YP.yss_status == FT.FT_InProgress /\
    st.YP.yss_phase == YP.SP_Data /\
    L.length st.YP.yss_sent == st.YP.yss_acked /\
    L.length st.YP.yss_sent < cfg.scfg_nblocks
  | YP.Server_eot ->
    Some? st.YP.yss_filename /\ st.YP.yss_status == FT.FT_InProgress /\
    st.YP.yss_phase == YP.SP_Data /\
    L.length st.YP.yss_sent == st.YP.yss_acked /\
    L.length st.YP.yss_sent == cfg.scfg_nblocks
  | YP.Server_complete ->
    Some? st.YP.yss_filename /\ st.YP.yss_status == FT.FT_InProgress /\
    st.YP.yss_phase == YP.SP_Eot /\
    L.length st.YP.yss_sent == st.YP.yss_acked
  | YP.Server_abort -> False
  | YP.Server_timeout -> False

(* `server_local_cont cfg ev st0` : exactly what `pe_finish_local_action` needs
   about the PRE-state st0 to re-establish the coupling at st1. *)
unfold
let server_local_cont (cfg:ymodem_server_config) (ev:YP.ymodem_server_local)
                      (st0:YP.ymodem_server_state) : prop =
  match ev with
  | YP.Server_start filename len plan ->
    st0 == YP.ymodem_server_initial /\
    filename == cfg.scfg_filename /\ len == cfg.scfg_len /\ plan == plan_of cfg
  | YP.Server_send ->
    Some? st0.YP.yss_filename /\ st0.YP.yss_status == FT.FT_InProgress /\
    st0.YP.yss_phase == YP.SP_Data /\
    L.length st0.YP.yss_sent < cfg.scfg_nblocks
  | YP.Server_eot ->
    Some? st0.YP.yss_filename /\ L.length st0.YP.yss_sent == cfg.scfg_nblocks
  | YP.Server_complete -> Some? st0.YP.yss_filename
  | YP.Server_abort -> Some? st0.YP.yss_filename
  | YP.Server_timeout -> False

(* ───────────────────────────────────────────────────────────────────────────
   Action frame (§ pe_action_frame) — a LIVE slprop for EACH case
   ─────────────────────────────────────────────────────────────────────────── *)

let ymodem_server_action_frame
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (st:YP.ymodem_server_state)
  (action:PE.endpoint_action
    CC.ymodem_server_network_frame
    YP.ymodem_server_local
    CC.ymodem_server_local_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput nf ->
    ymodem_server_frame_ready i cfg frame st **
    pure (nf.CC.ysnf_buf == frame.sef_ysnf /\ Some? st.YP.yss_filename)
  | PE.EndpointLocal ev lf ->
    ymodem_server_frame_ready i cfg frame st **
    pure (lf.CC.yslf_buf == frame.sef_blk /\ server_local_ready cfg ev st)
  | PE.EndpointDone
  | PE.EndpointFailed ->
    ymodem_server_frame_ready i cfg frame st

(* Network continuation: owns cursor+started+file+sef_blk (NOT sef_ysnf, which
   network_frame_pre owns); carries the coupling(st0), `Some? filename` (the
   server only awaits input after it has started), and the scratch equality. *)
let ymodem_server_network_continuation
  (_i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (st:YP.ymodem_server_state)
  (nf:CC.ymodem_server_network_frame)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (blkd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_blk blkd **
    pure (Seq.length blkd == 128 /\ scfg_wf cfg /\
          cells_ok cfg cv bv st /\ server_plan_ok cfg st /\
          Some? st.YP.yss_filename /\
          nf.CC.ysnf_buf == frame.sef_ysnf)

(* Local continuation: owns cursor+started+file+sef_ysnf (NOT sef_blk, which
   local_frame_pre owns); carries coupling(st0) + server_local_cont. *)
let ymodem_server_local_continuation
  (_i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (st:YP.ymodem_server_state)
  (ev:YP.ymodem_server_local)
  (lf:CC.ymodem_server_local_frame)
  : slprop =
  exists* (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t) (ysnfd:Seq.seq U8.t).
    Vec.pts_to frame.sef_cursor cv **
    Vec.pts_to frame.sef_started bv **
    Vec.pts_to cfg.scfg_file cfg.scfg_contents **
    pts_to frame.sef_ysnf ysnfd **
    pure (Seq.length ysnfd == 128 /\ scfg_wf cfg /\
          cells_ok cfg cv bv st /\ server_plan_ok cfg st /\
          lf.CC.yslf_buf == frame.sef_blk /\
          server_local_cont cfg ev st)

(* ───────────────────────────────────────────────────────────────────────────
   Network I/O carrier (§ pe_network_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_server_endpoint_network_io = {
  yni_input          : array U8.t;
  yni_input_len      : SZ.t;
  yni_output         : array U8.t;
  yni_input_contents : Ghost.erased TCP.bytes;
  yni_old_output     : Ghost.erased TCP.bytes;
  yni_raw_received   : Ghost.erased TCP.bytes;
}

let ymodem_server_network_io_continuation
  (_i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (frame:ymodem_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_server_state)
  (nio:ymodem_server_endpoint_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) sent **
  pure (
    nio.yni_input == frame.sef_in /\
    nio.yni_output == frame.sef_out /\
    nio.yni_input_len == 1sz /\
    Seq.length (Ghost.reveal nio.yni_old_output) == 133 /\
    Seq.length (Ghost.reveal nio.yni_input_contents) == 1)

let ymodem_server_network_input (nio:ymodem_server_endpoint_network_io) : array U8.t =
  nio.yni_input
let ymodem_server_network_input_len (nio:ymodem_server_endpoint_network_io) : SZ.t =
  nio.yni_input_len
let ymodem_server_network_output (nio:ymodem_server_endpoint_network_io) : array U8.t =
  nio.yni_output
let ymodem_server_network_output_len (_nio:ymodem_server_endpoint_network_io) : SZ.t =
  133sz
let ymodem_server_network_input_contents (nio:ymodem_server_endpoint_network_io)
  : Ghost.erased TCP.bytes = nio.yni_input_contents
let ymodem_server_network_old_output (nio:ymodem_server_endpoint_network_io)
  : Ghost.erased TCP.bytes = nio.yni_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_next_action — read status cell + started + cursor and schedule
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_next_action
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_server_state)
requires
  CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  ymodem_server_frame_ready i cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CC.ymodem_server_network_frame
  YP.ymodem_server_local
  CC.ymodem_server_local_frame
ensures
  CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  ymodem_server_action_frame i cfg frame (Ghost.reveal st) action **
  pure (PE.action_not_internal CC.ymodem_server_protocol_implementation action)
{
  unfold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with svs. _;
  let s = Vec.op_Array_Access i.status 0sz;
  fold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  unfold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd ysnfd. _;
  let b = Vec.op_Array_Access frame.sef_started 0sz;
  let c = Vec.op_Array_Access frame.sef_cursor 0sz;
  Plan.blocks_of_length cfg.scfg_contents 0 (L.length (Ghost.reveal st).YP.yss_sent);
  fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st));
  if (b = 0uy) {
    (* not started → Server_start (filename None ⟹ st == initial) *)
    let ev = YP.Server_start cfg.scfg_filename cfg.scfg_len (plan_of cfg);
    let lf : CC.ymodem_server_local_frame = { CC.yslf_buf = frame.sef_blk; CC.yslf_blk = 0uy };
    fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf));
    PE.EndpointLocal ev lf
  } else {
    (* started (b == 1uy ⟹ Some? filename) *)
    if (s = 0uy) {
      if (SZ.lt c cfg.scfg_nblocks_sz) {
        (* more blocks to send *)
        let lf : CC.ymodem_server_local_frame = { CC.yslf_buf = frame.sef_blk; CC.yslf_blk = 0uy };
        fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal YP.Server_send lf));
        PE.EndpointLocal YP.Server_send lf
      } else {
        (* all blocks sent+acked → EOT *)
        let lf : CC.ymodem_server_local_frame = { CC.yslf_buf = frame.sef_blk; CC.yslf_blk = 0uy };
        fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal YP.Server_eot lf));
        PE.EndpointLocal YP.Server_eot lf
      }
    } else if (s = 1uy) {
      (* one block outstanding → await the ACK *)
      let nf : CC.ymodem_server_network_frame = { CC.ysnf_buf = frame.sef_ysnf; CC.ysnf_blk = 0uy };
      fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
      PE.EndpointNeedInput nf
    } else if (s = 2uy) {
      (* EOT acked-phase → Server_complete *)
      let lf : CC.ymodem_server_local_frame = { CC.yslf_buf = frame.sef_blk; CC.yslf_blk = 0uy };
      fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal YP.Server_complete lf));
      PE.EndpointLocal YP.Server_complete lf
    } else if (s = 3uy) {
      fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone);
      PE.EndpointDone
    } else {
      fold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed);
      PE.EndpointFailed
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_cancel_action
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_cancel_action
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (st:Ghost.erased YP.ymodem_server_state)
  (action:PE.endpoint_action
    CC.ymodem_server_network_frame
    YP.ymodem_server_local
    CC.ymodem_server_local_frame)
requires ymodem_server_action_frame i cfg frame (Ghost.reveal st) action
ensures ymodem_server_frame_ready i cfg frame (Ghost.reveal st)
{
  match action {
    PE.EndpointNeedInput nf -> {
      unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf))
    }
    PE.EndpointLocal ev lf -> {
      unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf))
    }
    PE.EndpointDone -> {
      unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone)
    }
    PE.EndpointFailed -> {
      unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed)
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_network — read one 1-byte control frame into sef_in
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_prepare_network
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (ch:TCP.channel)
  (nf:CC.ymodem_server_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_server_state)
requires
  ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf) **
  ymodem_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:ymodem_server_endpoint_network_io
ensures
  ymodem_server_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (ymodem_server_network_input nio)
    (ymodem_server_network_input_len nio)
    (ymodem_server_network_output nio)
    (ymodem_server_network_output_len nio)
    (Ghost.reveal (ymodem_server_network_input_contents nio))
    (Ghost.reveal (ymodem_server_network_old_output nio)) **
  CC.ymodem_server_network_frame_pre
    nf
    (ymodem_server_network_input nio)
    (ymodem_server_network_input_len nio)
    (ymodem_server_network_output nio)
    (ymodem_server_network_output_len nio)
    (Ghost.reveal (ymodem_server_network_input_contents nio))
    (Ghost.reveal (ymodem_server_network_old_output nio)) **
  ymodem_server_network_continuation i cfg frame (Ghost.reveal st) nf **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (ymodem_server_network_input_contents nio))
      (ymodem_server_network_input_len nio)
      (Ghost.reveal (ymodem_server_network_old_output nio))
      (ymodem_server_network_output_len nio))
{
  unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
  unfold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd ysnfd. _;
  unfold (ymodem_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw outd ind. _;
  let nread = TCP.read_full ch frame.sef_in 1sz;
  with ind2 chunk. _;
  let nio : ymodem_server_endpoint_network_io = {
    yni_input = frame.sef_in;
    yni_input_len = 1sz;
    yni_output = frame.sef_out;
    yni_input_contents = Ghost.hide ind2;
    yni_old_output = Ghost.hide outd;
    yni_raw_received = Ghost.hide (Seq.append raw chunk);
  };
  (* io continuation: the channel *)
  rewrite (TCP.is_channel ch (Seq.append raw chunk) (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) (Ghost.reveal sent));
  fold (ymodem_server_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  (* network buffers: sef_in (input) + sef_out (output) *)
  rewrite (pts_to frame.sef_in ind2)
    as (pts_to (ymodem_server_network_input nio) (Ghost.reveal (ymodem_server_network_input_contents nio)));
  rewrite (pts_to frame.sef_out outd)
    as (pts_to (ymodem_server_network_output nio) (Ghost.reveal (ymodem_server_network_old_output nio)));
  fold (PE.network_buffers
    (ymodem_server_network_input nio)
    (ymodem_server_network_input_len nio)
    (ymodem_server_network_output nio)
    (ymodem_server_network_output_len nio)
    (Ghost.reveal (ymodem_server_network_input_contents nio))
    (Ghost.reveal (ymodem_server_network_old_output nio)));
  (* network frame precondition: owns sef_ysnf *)
  assert (pure (nf.CC.ysnf_buf == frame.sef_ysnf));
  rewrite (pts_to frame.sef_ysnf ysnfd)
    as (pts_to nf.CC.ysnf_buf ysnfd);
  fold (CC.ymodem_server_network_frame_pre
    nf
    (ymodem_server_network_input nio)
    (ymodem_server_network_input_len nio)
    (ymodem_server_network_output nio)
    (ymodem_server_network_output_len nio)
    (Ghost.reveal (ymodem_server_network_input_contents nio))
    (Ghost.reveal (ymodem_server_network_old_output nio)));
  (* network continuation: cursor+started+file+sef_blk + coupling *)
  fold (ymodem_server_network_continuation i cfg frame (Ghost.reveal st) nf);
  nio
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_action — re-establish the coupling (unchanged cells)
   ─────────────────────────────────────────────────────────────────────────── *)

(* PURE lemma: the coupling + cell agreement are preserved across every network
   transition (noop / ack / abort).  All three keep filename, sent, pending, len
   and phase; abort only flips status to Aborted (making the InProgress guard
   false ⟹ the Some-branch is vacuous).  Proved by pure case analysis here so
   the Pulse fold does not have to rewrite a match scrutinee. *)
let network_coupling_preserved
  (cfg:ymodem_server_config) (cv:Seq.seq SZ.t) (bv:Seq.seq U8.t)
  (st0 st1:YP.ymodem_server_state)
  : Lemma
    (requires
      cells_ok cfg cv bv st0 /\ server_plan_ok cfg st0 /\
      Some? st0.YP.yss_filename /\
      (st1 == st0 \/ st1 == Log.ack_next_state st0 \/ st1 == Log.abort_next_state st0))
    (ensures cells_ok cfg cv bv st1 /\ server_plan_ok cfg st1)
  = ()

noextract
fn ymodem_server_finish_network_action
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (nf:CC.ymodem_server_network_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased TCP.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_server_state)
  (st1:Ghost.erased YP.ymodem_server_state)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_server_network_continuation i cfg frame (Ghost.reveal st0) nf **
  CC.ymodem_server_network_frame_post
    nf result (Ghost.reveal input_contents) input_len
    (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs)
ensures ymodem_server_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (ymodem_server_network_continuation i cfg frame (Ghost.reveal st0) nf);
  with cv bv blkd. _;
  unfold (CC.ymodem_server_network_frame_post
    nf result (Ghost.reveal input_contents) input_len
    (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs));
  with o'. _;
  assert (pure (nf.CC.ysnf_buf == frame.sef_ysnf));
  rewrite (pts_to nf.CC.ysnf_buf o')
    as (pts_to frame.sef_ysnf o');
  (* st1 in {st0, ack st0, abort st0}: all preserve filename & sent, so the
     coupling + cell agreement carry over (Some? filename ⟹ Some-branch;
     ack keeps acked-only, abort makes InProgress false ⟹ vacuous). *)
  network_coupling_preserved cfg cv bv (Ghost.reveal st0) (Ghost.reveal st1);
  fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_io — write produced bytes, re-establish io_ready
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_finish_network_io
  (i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (frame:ymodem_server_endpoint_frame)
  (nio:ymodem_server_endpoint_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_server_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased YP.ymodem_server_state)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_server_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (ymodem_server_network_input nio) (Ghost.reveal (ymodem_server_network_input_contents nio)) **
  pts_to (ymodem_server_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CC.ymodem_server_protocol_implementation.CPI.pi_system i)
      (Ghost.reveal (ymodem_server_network_input_contents nio))
      (ymodem_server_network_input_len nio)
      (Ghost.reveal (ymodem_server_network_old_output nio))
      (Ghost.reveal out_contents)
      (ymodem_server_network_output_len nio)
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      result
      (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
      (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs))
ensures ymodem_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (ymodem_server_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CC.ymodem_server_protocol_implementation.CPI.pi_system i)
    (Ghost.reveal (ymodem_server_network_input_contents nio))
    (ymodem_server_network_input_len nio)
    (Ghost.reveal (ymodem_server_network_old_output nio))
    (Ghost.reveal out_contents)
    (ymodem_server_network_output_len nio)
    (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
    result
    (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
    (Ghost.reveal consumed) (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (ymodem_server_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal (Ghost.reveal sent1)
    (Seq.append (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (ymodem_server_network_output nio) (Ghost.reveal out_contents))
    as (pts_to frame.sef_out (Ghost.reveal out_contents));
  rewrite (pts_to (ymodem_server_network_input nio) (Ghost.reveal (ymodem_server_network_input_contents nio)))
    as (pts_to frame.sef_in (Ghost.reveal (ymodem_server_network_input_contents nio)));
  fold (ymodem_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   Local I/O carrier (§ pe_local_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_server_endpoint_local_io = {
  ylo_output       : array U8.t;
  ylo_old_output   : Ghost.erased TCP.bytes;
  ylo_raw_received : Ghost.erased TCP.bytes;
}

let ymodem_server_local_io_continuation
  (_i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (frame:ymodem_server_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_server_state)
  (_ev:YP.ymodem_server_local)
  (lio:ymodem_server_endpoint_local_io)
  : slprop =
  exists* (ind:Seq.seq U8.t).
    TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) sent **
    pts_to frame.sef_in ind **
    pure (
      lio.ylo_output == frame.sef_out /\
      Seq.length (Ghost.reveal lio.ylo_old_output) == 133 /\
      Seq.length ind == 1)

let ymodem_server_local_output (lio:ymodem_server_endpoint_local_io) : array U8.t =
  lio.ylo_output
let ymodem_server_local_output_len (_lio:ymodem_server_endpoint_local_io) : SZ.t =
  133sz
let ymodem_server_local_old_output (lio:ymodem_server_endpoint_local_io)
  : Ghost.erased TCP.bytes = lio.ylo_old_output

(* ───────────────────────────────────────────────────────────────────────────
   Block copy helper: dst[0..128) := file[off..off+128)
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn copy_block
  (file:Vec.vec U8.t)
  (dst:array U8.t)
  (off:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#d0:Ghost.erased (Seq.seq U8.t))
requires
  Vec.pts_to file contents ** pts_to dst d0 **
  pure (Seq.length d0 == 128 /\
        SZ.v off + 128 <= Seq.length contents /\
        SZ.fits (SZ.v off + 128))
returns _:unit
ensures exists* (d1:Seq.seq U8.t).
  Vec.pts_to file contents ** pts_to dst d1 **
  pure (Seq.length d1 == 128 /\
        (forall (k:nat). (k < 128 /\ SZ.v off + k < Seq.length contents) ==>
           Seq.index d1 k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
{
  let mut j = 0sz;
  while (SZ.lt (!j) 128sz)
  invariant exists* (vj:SZ.t) (d:Seq.seq U8.t).
    R.pts_to j vj **
    Vec.pts_to file contents **
    pts_to dst d **
    pure (SZ.v vj <= 128 /\ Seq.length d == 128 /\
          SZ.v off + 128 <= Seq.length contents /\
          SZ.fits (SZ.v off + 128) /\
          (forall (k:nat). k < SZ.v vj ==> Seq.index d k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
  decreases (128 - SZ.v (!j))
  {
    let vj = !j;
    FStar.SizeT.fits_lte (SZ.v off + SZ.v vj) (SZ.v off + 128);
    let src = Vec.op_Array_Access file (SZ.add off vj);
    dst.(vj) <- src;
    j := SZ.add vj 1sz;
  };
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_local — build the local frame + output; Server_send copies block
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_prepare_local
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (ch:TCP.channel)
  (ev:YP.ymodem_server_local)
  (lf:CC.ymodem_server_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_server_state)
requires
  ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf) **
  ymodem_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:ymodem_server_endpoint_local_io
ensures
  ymodem_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (ymodem_server_local_output lio)
    (ymodem_server_local_output_len lio)
    (Ghost.reveal (ymodem_server_local_old_output lio)) **
  CC.ymodem_server_local_frame_pre
    ev lf (Ghost.reveal st)
    (ymodem_server_local_output lio)
    (ymodem_server_local_output_len lio)
    (Ghost.reveal (ymodem_server_local_old_output lio)) **
  ymodem_server_local_continuation i cfg frame (Ghost.reveal st) ev lf
{
  unfold (ymodem_server_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev lf));
  unfold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st));
  with cv bv blkd ysnfd. _;
  unfold (ymodem_server_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw outd ind. _;
  let lio : ymodem_server_endpoint_local_io = {
    ylo_output = frame.sef_out;
    ylo_old_output = Ghost.hide outd;
    ylo_raw_received = Ghost.hide raw;
  };
  (* For Server_send, copy block `cursor` into sef_blk and prove it is the head
     of the pending list; other live events leave sef_blk untouched. *)
  match ev {
    YP.Server_send -> {
      let c = Vec.op_Array_Access frame.sef_cursor 0sz;
      let cn = SZ.v c;
      (* cn == L.length sent < nblocks (from cells_ok + server_local_ready) *)
      Math.lemma_mult_le_right 128 (cn + 1) cfg.scfg_nblocks;
      Math.lemma_mult_le_right 128 cn cfg.scfg_nblocks;
      Math.distributivity_add_left cn 1 128;
      FStar.SizeT.fits_lte (cn * 128) (cfg.scfg_nblocks * 128);
      let off = SZ.mul c 128sz;
      FStar.SizeT.fits_lte (SZ.v off + 128) (cfg.scfg_nblocks * 128);
      copy_block cfg.scfg_file frame.sef_blk off;
      with blkd1. _;
      (* blkd1 == block contents cn == hd pending *)
      Plan.block_slice cfg.scfg_contents cn cfg.scfg_nblocks;
      Plan.blocks_of_unfold cfg.scfg_contents cn cfg.scfg_nblocks;
      Plan.blocks_of_plan_wf cfg.scfg_contents cn cfg.scfg_nblocks;
      assert (pure (Seq.equal blkd1 (Plan.block cfg.scfg_contents cn)));
      assert (pure (Seq.equal (L.hd (Ghost.reveal st).YP.yss_pending) blkd1));
      rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
        as (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent));
      fold (ymodem_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
      rewrite (pts_to frame.sef_out outd)
        as (pts_to (ymodem_server_local_output lio) (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (PE.local_output_buffer
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      rewrite (pts_to frame.sef_blk blkd1)
        as (pts_to lf.CC.yslf_buf blkd1);
      fold (CC.ymodem_server_local_frame_pre
        ev lf (Ghost.reveal st)
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (ymodem_server_local_continuation i cfg frame (Ghost.reveal st) ev lf);
      lio
    }
    YP.Server_start filename len plan -> {
      Plan.blocks_of_plan_wf cfg.scfg_contents 0 cfg.scfg_nblocks;
      rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
        as (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent));
      fold (ymodem_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
      rewrite (pts_to frame.sef_out outd)
        as (pts_to (ymodem_server_local_output lio) (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (PE.local_output_buffer
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      rewrite (pts_to frame.sef_blk blkd)
        as (pts_to lf.CC.yslf_buf blkd);
      fold (CC.ymodem_server_local_frame_pre
        ev lf (Ghost.reveal st)
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (ymodem_server_local_continuation i cfg frame (Ghost.reveal st) ev lf);
      lio
    }
    YP.Server_eot -> {
      Plan.blocks_of_empty cfg.scfg_contents cfg.scfg_nblocks cfg.scfg_nblocks;
      rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
        as (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent));
      fold (ymodem_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
      rewrite (pts_to frame.sef_out outd)
        as (pts_to (ymodem_server_local_output lio) (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (PE.local_output_buffer
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      rewrite (pts_to frame.sef_blk blkd)
        as (pts_to lf.CC.yslf_buf blkd);
      fold (CC.ymodem_server_local_frame_pre
        ev lf (Ghost.reveal st)
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (ymodem_server_local_continuation i cfg frame (Ghost.reveal st) ev lf);
      lio
    }
    YP.Server_complete -> {
      Plan.blocks_of_empty cfg.scfg_contents cfg.scfg_nblocks cfg.scfg_nblocks;
      rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
        as (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent));
      fold (ymodem_server_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
      rewrite (pts_to frame.sef_out outd)
        as (pts_to (ymodem_server_local_output lio) (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (PE.local_output_buffer
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      rewrite (pts_to frame.sef_blk blkd)
        as (pts_to lf.CC.yslf_buf blkd);
      fold (CC.ymodem_server_local_frame_pre
        ev lf (Ghost.reveal st)
        (ymodem_server_local_output lio)
        (ymodem_server_local_output_len lio)
        (Ghost.reveal (ymodem_server_local_old_output lio)));
      fold (ymodem_server_local_continuation i cfg frame (Ghost.reveal st) ev lf);
      lio
    }
    YP.Server_abort -> { unreachable () }
    YP.Server_timeout -> { unreachable () }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_action — advance the cursor/started cells, re-prove coupling
   ─────────────────────────────────────────────────────────────────────────── *)

(* PURE lemma: Server_send shifts the plan cursor by one while preserving the
   coupling.  From `st0.sent == blocks_of 0 c0` and `st0.pending == blocks_of c0
   nblocks` (c0 = length sent0 < nblocks), appending the head of pending onto
   sent produces `blocks_of 0 (c0+1)` and the new pending is `blocks_of (c0+1)
   nblocks` — i.e. `server_plan_ok cfg (send_next_state st0)`.  Proved here by a
   pure `lemma_send_shift` + `append_length` so the Pulse fold is mechanical. *)
let send_preserves_plan_ok
  (cfg:ymodem_server_config) (st0 st1:YP.ymodem_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\
      Some? st0.YP.yss_filename /\ st0.YP.yss_status == FT.FT_InProgress /\
      st0.YP.yss_phase == YP.SP_Data /\
      L.length st0.YP.yss_sent < cfg.scfg_nblocks /\
      Cons? st0.YP.yss_pending /\ st1 == Log.send_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\
      st1.YP.yss_filename == st0.YP.yss_filename /\
      L.length st1.YP.yss_sent == L.length st0.YP.yss_sent + 1)
  = Plan.lemma_send_shift cfg.scfg_contents (L.length st0.YP.yss_sent) cfg.scfg_nblocks;
    FStar.List.Tot.Properties.append_length st0.YP.yss_sent [L.hd st0.YP.yss_pending]

(* PURE lemma: Server_start establishes the coupling from the initial state.
   sent=[]=blocks_of 0 0, pending=plan=blocks_of 0 nblocks, filename=Some. *)
let start_preserves_plan_ok
  (cfg:ymodem_server_config) (st1:YP.ymodem_server_state)
  (filename:TCP.bytes) (len:nat) (plan:list TCP.bytes)
  : Lemma
    (requires
      filename == cfg.scfg_filename /\ len == cfg.scfg_len /\ plan == plan_of cfg /\
      st1 == Log.start_next_state filename len plan)
    (ensures
      server_plan_ok cfg st1 /\ Some? st1.YP.yss_filename /\
      L.length st1.YP.yss_sent == 0)
  = Plan.blocks_of_empty cfg.scfg_contents 0 0

(* PURE lemma: Server_eot only flips the phase to SP_Eot; the cursor is at
   nblocks (all blocks sent) so the new phase-guard `SP_Eot ⟹ length==nblocks`
   holds and every other coupling fact transfers unchanged. *)
let eot_preserves_plan_ok
  (cfg:ymodem_server_config) (st0 st1:YP.ymodem_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\ Some? st0.YP.yss_filename /\
      L.length st0.YP.yss_sent == cfg.scfg_nblocks /\
      st1 == Log.eot_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\ st1.YP.yss_filename == st0.YP.yss_filename /\
      L.length st1.YP.yss_sent == L.length st0.YP.yss_sent)
  = ()

(* PURE lemma: Server_complete flips status to Completed; Server_abort flips it
   to Aborted.  Either way the InProgress guard is false ⟹ the Some-branch of
   the coupling is vacuous, and the (filename, sent) fields are untouched. *)
let complete_preserves_plan_ok
  (cfg:ymodem_server_config) (st0 st1:YP.ymodem_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\ Some? st0.YP.yss_filename /\
      st1 == Log.complete_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\ st1.YP.yss_filename == st0.YP.yss_filename /\
      L.length st1.YP.yss_sent == L.length st0.YP.yss_sent)
  = ()

let abort_preserves_plan_ok
  (cfg:ymodem_server_config) (st0 st1:YP.ymodem_server_state)
  : Lemma
    (requires
      server_plan_ok cfg st0 /\ Some? st0.YP.yss_filename /\
      st1 == Log.abort_next_state st0)
    (ensures
      server_plan_ok cfg st1 /\ st1.YP.yss_filename == st0.YP.yss_filename /\
      L.length st1.YP.yss_sent == L.length st0.YP.yss_sent)
  = ()

noextract
fn ymodem_server_finish_local_action
  (i:CC.ymodem_server_impl)
  (cfg:ymodem_server_config)
  (frame:ymodem_server_endpoint_frame)
  (ev:YP.ymodem_server_local)
  (lf:CC.ymodem_server_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_server_state)
  (st1:Ghost.erased YP.ymodem_server_state)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_server_local_continuation i cfg frame (Ghost.reveal st0) ev lf **
  CC.ymodem_server_local_frame_post
    ev lf result (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs)
ensures ymodem_server_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (ymodem_server_local_continuation i cfg frame (Ghost.reveal st0) ev lf);
  with cv bv ysnfd. _;
  unfold (CC.ymodem_server_local_frame_post
    ev lf result (Ghost.reveal old_out) (Ghost.reveal out_contents)
    (Ghost.reveal st0) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs));
  with d. _;
  assert (pure (lf.CC.yslf_buf == frame.sef_blk));
  rewrite (pts_to lf.CC.yslf_buf d)
    as (pts_to frame.sef_blk d);
  match ev {
    YP.Server_send -> {
      let c = Vec.op_Array_Access frame.sef_cursor 0sz;
      FStar.SizeT.fits_lte (SZ.v c + 1) (cfg.scfg_nblocks);
      Vec.op_Array_Assignment frame.sef_cursor 0sz (SZ.add c 1sz);
      (* st1 == send_next_state st0; re-establish the coupling at cursor+1 *)
      send_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    YP.Server_start filename len plan -> {
      Vec.op_Array_Assignment frame.sef_cursor 0sz 0sz;
      Vec.op_Array_Assignment frame.sef_started 0sz 1uy;
      (* st1 == start_next_state: sent=[], pending=plan=blocks_of 0 nblocks *)
      start_preserves_plan_ok cfg (Ghost.reveal st1) filename len plan;
      fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    YP.Server_eot -> {
      (* st1 == eot_next_state st0: only phase → SP_Eot; cells unchanged *)
      eot_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    YP.Server_complete -> {
      (* st1 == complete_next_state st0: status → Completed ⟹ coupling vacuous *)
      complete_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    YP.Server_abort -> {
      (* st1 == abort_next_state st0: status → Aborted ⟹ coupling vacuous *)
      abort_preserves_plan_ok cfg (Ghost.reveal st0) (Ghost.reveal st1);
      fold (ymodem_server_frame_ready i cfg frame (Ghost.reveal st1))
    }
    YP.Server_timeout -> { unreachable () }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_io — write produced bytes, re-establish io_ready
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_server_finish_local_io
  (i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (frame:ymodem_server_endpoint_frame)
  (lio:ymodem_server_endpoint_local_io)
  (ev:YP.ymodem_server_local)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_server_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased YP.ymodem_server_state)
  (out_contents:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_server_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (ymodem_server_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CC.ymodem_server_protocol_implementation.CPI.pi_system i)
      ev
      (Ghost.reveal (ymodem_server_local_old_output lio))
      (Ghost.reveal out_contents)
      (ymodem_server_local_output_len lio)
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
      result
      (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
      (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs))
ensures ymodem_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (ymodem_server_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  with ind. _;
  CPI.lemma_local_process_sent_output_prefix
    (CC.ymodem_server_protocol_implementation.CPI.pi_system i)
    ev
    (Ghost.reveal (ymodem_server_local_old_output lio))
    (Ghost.reveal out_contents)
    (ymodem_server_local_output_len lio)
    (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
    result
    (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
    (Ghost.reveal wire_outputs) (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (ymodem_server_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal (Ghost.reveal sent1)
    (Seq.append (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received)
      (Seq.append (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (ymodem_server_local_output lio) (Ghost.reveal out_contents))
    as (pts_to frame.sef_out (Ghost.reveal out_contents));
  fold (ymodem_server_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   The 28-field endpoint instance
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let ymodem_server_protocol_endpoint
  : PE.protocol_endpoint
      CC.ymodem_server_impl
      YP.ymodem_server_state
      ymodem_message
      YP.ymodem_server_local
      unit
      CC.ymodem_server_protocol_implementation
  =
  {
    PE.pe_config = ymodem_server_config;
    PE.pe_frame = ymodem_server_endpoint_frame;
    PE.pe_frame_ready = ymodem_server_frame_ready;
    PE.pe_io_ready = ymodem_server_io_ready;
    PE.pe_action_frame = ymodem_server_action_frame;
    PE.pe_network_continuation = ymodem_server_network_continuation;
    PE.pe_local_continuation = ymodem_server_local_continuation;
    PE.pe_next_action = ymodem_server_next_action;
    PE.pe_cancel_action = ymodem_server_cancel_action;
    PE.pe_finish_network_action = ymodem_server_finish_network_action;
    PE.pe_finish_local_action = ymodem_server_finish_local_action;
    PE.pe_network_io = ymodem_server_endpoint_network_io;
    PE.pe_network_io_continuation = ymodem_server_network_io_continuation;
    PE.pe_network_input = ymodem_server_network_input;
    PE.pe_network_input_len = ymodem_server_network_input_len;
    PE.pe_network_output = ymodem_server_network_output;
    PE.pe_network_output_len = ymodem_server_network_output_len;
    PE.pe_network_input_contents = ymodem_server_network_input_contents;
    PE.pe_network_old_output = ymodem_server_network_old_output;
    PE.pe_prepare_network = ymodem_server_prepare_network;
    PE.pe_finish_network_io = ymodem_server_finish_network_io;
    PE.pe_local_io = ymodem_server_endpoint_local_io;
    PE.pe_local_io_continuation = ymodem_server_local_io_continuation;
    PE.pe_local_output = ymodem_server_local_output;
    PE.pe_local_output_len = ymodem_server_local_output_len;
    PE.pe_local_old_output = ymodem_server_local_old_output;
    PE.pe_prepare_local = ymodem_server_prepare_local;
    PE.pe_finish_local_io = ymodem_server_finish_local_io;
  }
