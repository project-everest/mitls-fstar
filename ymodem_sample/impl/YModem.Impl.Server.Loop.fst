module YModem.Impl.Server.Loop

(**
  A verified, **Low*-EXTRACTABLE** YMODEM *server* (sender) driver loop.

  Unlike the generic `YModem.Impl.Server.Socket` driver (which runs the
  typeclass-polymorphic `Common.ProtocolDriver.drive_steps` and is therefore
  NOT extractable) and unlike the committed `ymodem_server_process_local` (whose
  event type `YModem.Protocol.ymodem_server_local` carries specification data
  — `Server_start filename:bytes len:nat plan:list _` — and so does NOT extract),
  this module contains a bespoke, first-order Pulse loop whose every runnable
  step is verified AND extracts to clean Low* C.

    * For ACK reception it DIRECTLY reuses the committed verified leaf
      `YModem.Impl.Server.CanonicalProtocol.ymodem_server_process_network`.

    * For the send events it provides Low* action wrappers
      (`ymodem_server_start`, `ymodem_server_send_block`, `ymodem_server_emit_eot`,
      `ymodem_server_complete`) whose *event data is `Ghost.erased`*: each is the
      corresponding `ymodem_server_process_local` branch with the spec-carrying
      event replaced by erased ghosts and the `local_frame`/`frame_post`
      bookkeeping inlined.  The concrete residue of each wrapper is exactly a
      status-cell write plus (for `send_block`/`emit_eot`) the emit leaf; the
      MonotonicGhostRef / ReflexiveTransitiveClosure / Log operations all erase.

  The loop maintains the send-plan coupling `loop_coupling` — the concrete block
  cursor `c` agrees with the ghost ARQ state's `yss_sent`/`yss_pending`
  (`blocks_of` split at `c`) — transplanted from
  `YModem.Impl.Server.Endpoint.server_plan_ok`.  `send_block` discharges its
  precondition `hd pending == block cursor` exactly as
  `Server.Endpoint.prepare_local` does: a 128-byte offset copy of `block c` out
  of the padded file, then `Plan.block_slice` / `Plan.blocks_of_unfold`.  After
  each ACK the coupling is re-established at `c+1` via `Plan.lemma_send_shift`.

  Tier-1 simplification (lossless cooperative peer): no NAK-retransmit /
  Server_timeout; the EOT-ack is not read as a wire event (fire complete
  directly), mirroring the endpoint's SP_Eot handling.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Common.ProtocolImplementation
module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Common.TCP
module U8   = FStar.UInt8
module Vec  = Pulse.Lib.Vec
module MR   = Pulse.Lib.MonotonicGhostRef
module RTC  = FStar.ReflexiveTransitiveClosure
module R    = Pulse.Lib.Reference
module A    = Pulse.Lib.Array
module L    = FStar.List.Tot
module FT   = Common.FileTransfer
module Math = FStar.Math.Lemmas

module YP    = YModem.Protocol
module CC    = YModem.Impl.Server.CanonicalProtocol
module Log   = YModem.Impl.Server.Log
module Plan  = YModem.Impl.Server.Plan
module Codec = YModem.Impl.Codec

open YModem.Wire.Generated.Ymodem_soh_body
open YModem.Wire.Generated.Ymodem_message
open YModem.Wire

#set-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   THE SEND-PLAN COUPLING (transplanted from Server.Endpoint.server_plan_ok,
   augmented with the concrete cursor↔`length yss_sent` cell agreement).

   `loop_coupling contents nblocks filename len st c` says the loop is in the
   "ready-to-send-next-block" state: nothing outstanding (acked == length sent),
   still InProgress in the data phase, and the cursor `c` == the number of sent
   blocks, with `yss_sent`/`yss_pending` the low/high `blocks_of` split at `c`.
   ─────────────────────────────────────────────────────────────────────────── *)
unfold
let loop_coupling
  (contents:TCP.bytes) (nblocks:nat) (filename:TCP.bytes) (len:nat)
  (st:YP.ymodem_server_state) (c:SZ.t) : prop =
  st.YP.yss_filename == Some filename /\
  st.YP.yss_len == len /\
  st.YP.yss_status == FT.FT_InProgress /\
  st.YP.yss_phase == YP.SP_Data /\
  st.YP.yss_acked == L.length st.YP.yss_sent /\
  SZ.v c == L.length st.YP.yss_sent /\
  SZ.v c <= nblocks /\
  st.YP.yss_sent == Plan.blocks_of contents 0 (L.length st.YP.yss_sent) /\
  st.YP.yss_pending == Plan.blocks_of contents (L.length st.YP.yss_sent) nblocks

(* PURE fact: none of the three network post-transitions (identity, ACK-advance,
   CAN-abort) touches `yss_sent`/`yss_pending`/`yss_filename`/`yss_len`/`yss_phase`
   — they only bump `yss_acked` / flip `yss_status`.  So after `process_network`
   the send-plan fields carry over unchanged from the pre-state. *)
let lemma_net_post_preserves (sa st1:YP.ymodem_server_state)
  : Lemma
    (requires
      st1 == sa \/ st1 == Log.ack_next_state sa \/ st1 == Log.abort_next_state sa)
    (ensures
      st1.YP.yss_sent == sa.YP.yss_sent /\
      st1.YP.yss_pending == sa.YP.yss_pending /\
      st1.YP.yss_filename == sa.YP.yss_filename /\
      st1.YP.yss_len == sa.YP.yss_len /\
      st1.YP.yss_phase == sa.YP.yss_phase)
  = ()

(* ───────────────────────────────────────────────────────────────────────────
   1.  ymodem_server_start — Low* wrapper for the Server_start bootstrap.

   Models the `Server_start` branch of `ymodem_server_process_local`, with the
   (filename, len, plan) taken ERASED (they feed only the ghost log).  Concrete
   effect: status cell stays `0uy` (idle) + the ghost log advance.  The
   precondition pins `yss_filename == None`.

   EXTRACTS to roughly `void ymodem_server_start(uint8_t *i){ i[0] = 0; }`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn ymodem_server_start
  (i:CC.ymodem_server_impl)
  (filename:Ghost.erased TCP.bytes)
  (len:Ghost.erased nat)
  (plan:Ghost.erased (list TCP.bytes))
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
requires
  CC.ymodem_server_inv i received sent st **
  pure ((Ghost.reveal st).YP.yss_filename == None /\ YP.plan_wf (Ghost.reveal plan))
ensures
  CC.ymodem_server_inv i received sent
    (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len) (Ghost.reveal plan))
{
  unfold (CC.ymodem_server_inv i received sent st);
  with svs. _;
  Log.lemma_start_step (Ghost.reveal st) (Ghost.reveal filename) (Ghost.reveal len) (Ghost.reveal plan);
  Vec.op_Array_Assignment i.status 0sz 0uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
               (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len) (Ghost.reveal plan)));
  Log.lemma_start_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
    (Ghost.reveal filename) (Ghost.reveal len) (Ghost.reveal plan);
  RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent)
          (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len) (Ghost.reveal plan)));
}

(* ───────────────────────────────────────────────────────────────────────────
   2.  ymodem_server_send_block — Low* wrapper for Server_send.

   Models the `Server_send` branch of `ymodem_server_process_local`.  The caller
   supplies the 128-byte payload `bd == hd pending` (via `local_pre_ok`); this
   wrapper frames + emits the SOH data block into `out` (calling the verified
   `Codec.ymodem_emit_data_block`), sets the status cell `0uy -> 1uy`, and
   advances the ghost log to `send_next_state st`.

   EXTRACTS to: emit-leaf call + `i->status[0] = 1`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn ymodem_server_send_block
  (i:CC.ymodem_server_impl)
  (blkdata:array U8.t)
  (blk:U8.t)
  (out:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
  (#bd:Ghost.erased (Seq.seq U8.t))
  (#oc:Ghost.erased (Seq.seq U8.t))
requires
  CC.ymodem_server_inv i received sent st **
  pts_to blkdata bd **
  pts_to out oc **
  pure (Seq.length (Ghost.reveal bd) == 128 /\ Seq.length (Ghost.reveal oc) == 133 /\
        CC.local_pre_ok YP.Server_send (Ghost.reveal st) (Ghost.reveal bd))
ensures exists* (st1:YP.ymodem_server_state) (nsent:TCP.bytes) (oc':Seq.seq U8.t).
  CC.ymodem_server_inv i received nsent st1 **
  pts_to blkdata bd **
  pts_to out oc' **
  pure (Seq.length oc' == 133 /\
        CC.ys_local_post_ok YP.Server_send (Ghost.reveal st) st1)
{
  Codec.ymodem_emit_data_block blk blkdata out;
  with o'. _;
  let body = CC.extract_soh_body bd o' blk;
  Seq.lemma_eq_elim (L.hd (Ghost.reveal st).YP.yss_pending) (Ghost.reveal bd);
  unfold (CC.ymodem_server_inv i received sent st);
  with svs. _;
  Log.lemma_send_step (Ghost.reveal st) (Ghost.reveal body);
  let st1 = Ghost.hide (Log.send_next_state (Ghost.reveal st));
  let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent) (ymodem_serialize (Body_soh (Ghost.reveal body))));
  Vec.op_Array_Assignment i.status 0sz 1uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent1) (Ghost.reveal st1));
  Log.lemma_send_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) (Ghost.reveal body);
  RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent1) (Ghost.reveal st1));
}

(* ───────────────────────────────────────────────────────────────────────────
   3.  ymodem_server_emit_eot — Low* wrapper for Server_eot.

   Models the `Server_eot` branch.  Writes the 1-byte EOT (0x04) into `out`,
   sets the status cell `0uy -> 2uy` (EOT handshake), advances the ghost log to
   `eot_next_state st`.

   EXTRACTS to: `out[0] = 4` + `i->status[0] = 2`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn ymodem_server_emit_eot
  (i:CC.ymodem_server_impl)
  (out:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
  (#oc:Ghost.erased (Seq.seq U8.t))
requires
  CC.ymodem_server_inv i received sent st **
  pts_to out oc **
  pure (Seq.length (Ghost.reveal oc) == 133 /\
        Some? (Ghost.reveal st).YP.yss_filename /\
        (Ghost.reveal st).YP.yss_status == FT.FT_InProgress /\
        (Ghost.reveal st).YP.yss_phase == YP.SP_Data /\
        (Ghost.reveal st).YP.yss_pending == [] /\
        (Ghost.reveal st).YP.yss_acked == L.length (Ghost.reveal st).YP.yss_sent)
ensures exists* (nsent:TCP.bytes) (oc':Seq.seq U8.t).
  CC.ymodem_server_inv i received nsent (Log.eot_next_state (Ghost.reveal st)) **
  pts_to out oc' **
  pure (Seq.length oc' == 133 /\ Seq.index oc' 0 == 4uy)
{
  unfold (CC.ymodem_server_inv i received sent st);
  with svs. _;
  Log.lemma_eot_step (Ghost.reveal st);
  let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent) (Seq.create 1 4uy));
  out.(0sz) <- 4uy;
  with o'. _;
  Vec.op_Array_Assignment i.status 0sz 2uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent1)
               (Log.eot_next_state (Ghost.reveal st)));
  Log.lemma_eot_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st);
  RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent1)
          (Log.eot_next_state (Ghost.reveal st)));
}

(* ───────────────────────────────────────────────────────────────────────────
   4.  ymodem_server_complete — Low* wrapper for Server_complete.

   Models the `Server_complete` branch.  Emits nothing; sets the status cell
   `2uy -> 3uy` (Completed), advances the ghost log to `complete_next_state st`.

   EXTRACTS to: `i->status[0] = 3`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn ymodem_server_complete
  (i:CC.ymodem_server_impl)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
requires
  CC.ymodem_server_inv i received sent st **
  pure (Some? (Ghost.reveal st).YP.yss_filename /\
        (Ghost.reveal st).YP.yss_status == FT.FT_InProgress /\
        (Ghost.reveal st).YP.yss_phase == YP.SP_Eot /\
        (Ghost.reveal st).YP.yss_pending == [] /\
        (Ghost.reveal st).YP.yss_acked == L.length (Ghost.reveal st).YP.yss_sent)
ensures
  CC.ymodem_server_inv i received sent (Log.complete_next_state (Ghost.reveal st))
{
  unfold (CC.ymodem_server_inv i received sent st);
  with svs. _;
  Log.lemma_complete_step (Ghost.reveal st);
  Vec.op_Array_Assignment i.status 0sz 3uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
               (Log.complete_next_state (Ghost.reveal st)));
  Log.lemma_complete_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st);
  RTC.closure_step Log.ys_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.ymodem_server_inv i (Ghost.reveal received) (Ghost.reveal sent)
          (Log.complete_next_state (Ghost.reveal st)));
}

(* ───────────────────────────────────────────────────────────────────────────
   5.  read_server_status — read the runtime status cell, exposing the flag↔state
   agreement `ys_status_flag_ok`.  Extracts to a vector read `i->status[0]`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn read_server_status
  (i:CC.ymodem_server_impl)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
requires
  CC.ymodem_server_inv i received sent st
returns s:U8.t
ensures
  CC.ymodem_server_inv i received sent st **
  pure (Log.ys_status_flag_ok s (Ghost.reveal st))
{
  unfold (CC.ymodem_server_inv i received sent st);
  with svs. _;
  let s = Vec.op_Array_Access i.status 0sz;
  fold (CC.ymodem_server_inv i received sent st);
  s
}

(* ───────────────────────────────────────────────────────────────────────────
   6.  run_process_network — a first-order wrapper around the committed
   `ymodem_server_process_network` leaf.  Builds the two-field network frame from
   the caller's 128-byte scratch `ysnf`, folds the (relaxed) frame precondition,
   dispatches, and unfolds the frame postcondition to hand the scratch back.
   Exposes `ys_network_post_ok st st1` so the loop can carry the send-plan fields
   across the ACK.  Extracts to a direct `process_network` call.
   ─────────────────────────────────────────────────────────────────────────── *)
fn run_process_network
  (i:CC.ymodem_server_impl)
  (ysnf:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_server_state)
  (#yd #ic #oc:Ghost.erased (Seq.seq U8.t))
requires
  CC.ymodem_server_inv i received sent st **
  pts_to ysnf yd **
  pts_to input ic **
  pts_to out oc **
  pure (Seq.length (Ghost.reveal yd) == 128 /\ SZ.v input_len == Seq.length (Ghost.reveal ic) /\
        SZ.v input_len >= 1 /\ Seq.length (Ghost.reveal oc) == 133)
returns result:CPI.process_result
ensures exists* (st1:YP.ymodem_server_state) (received1 sent1:Ghost.erased TCP.bytes)
                (yd1 oc1:Seq.seq U8.t).
  CC.ymodem_server_inv i received1 sent1 st1 **
  pts_to ysnf yd1 **
  pts_to input ic **
  pts_to out oc1 **
  pure (Seq.length yd1 == 128 /\ Seq.length oc1 == 133 /\
        CC.ys_network_post_ok (Ghost.reveal st) st1)
{
  pts_to_len out;
  let frame : CC.ymodem_server_network_frame = { CC.ysnf_buf = ysnf; CC.ysnf_blk = 0uy };
  rewrite (pts_to ysnf yd) as (pts_to frame.CC.ysnf_buf yd);
  fold (CC.ymodem_server_network_frame_pre frame input input_len out 133sz ic oc);
  let result =
    CC.ymodem_server_process_network i frame input input_len out 133sz
      received sent st ic oc;
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs. _;
  unfold (CC.ymodem_server_network_frame_post
            frame result ic input_len oc out_contents (Ghost.reveal st) st1
            consumed wire_outputs local_outputs);
  with yd1. _;
  rewrite (pts_to frame.CC.ysnf_buf yd1) as (pts_to ysnf yd1);
  pts_to_len out;
  result
}

(* ───────────────────────────────────────────────────────────────────────────
   7.  copy_block_arr — dst[0..128) := src[off..off+128), through a byte loop
   (exactly `Server.Endpoint.copy_block`, retyped from `Vec` to `array`).
   The postcondition exposes the copied bytes so the caller can prove
   `dst == block src (off/128)`.  Extracts to a byte-copy loop.
   ─────────────────────────────────────────────────────────────────────────── *)
fn copy_block_arr
  (src:array U8.t)
  (dst:array U8.t)
  (off:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#d0:Ghost.erased (Seq.seq U8.t))
requires
  pts_to src contents ** pts_to dst d0 **
  pure (Seq.length (Ghost.reveal d0) == 128 /\
        SZ.v off + 128 <= Seq.length (Ghost.reveal contents) /\
        SZ.fits (SZ.v off + 128))
returns _:unit
ensures exists* (d1:Seq.seq U8.t).
  pts_to src contents ** pts_to dst d1 **
  pure (Seq.length d1 == 128 /\
        (forall (k:nat). (k < 128 /\ SZ.v off + k < Seq.length (Ghost.reveal contents)) ==>
           Seq.index d1 k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
{
  let mut j = 0sz;
  while (SZ.lt (!j) 128sz)
  invariant exists* (vj:SZ.t) (d:Seq.seq U8.t).
    R.pts_to j vj **
    pts_to src contents **
    pts_to dst d **
    pure (SZ.v vj <= 128 /\ Seq.length d == 128 /\
          SZ.v off + 128 <= Seq.length (Ghost.reveal contents) /\
          SZ.fits (SZ.v off + 128) /\
          (forall (k:nat). k < SZ.v vj ==>
             Seq.index d k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
  decreases (128 - SZ.v (!j))
  {
    let vj = !j;
    FStar.SizeT.fits_lte (SZ.v off + SZ.v vj) (SZ.v off + 128);
    let sv = src.(SZ.add off vj);
    dst.(vj) <- sv;
    j := SZ.add vj 1sz;
  };
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   8.  ymodem_server_run — the verified Low* sender driver loop.

   Bounded by `fuel`; drives Server_start once, then walks the block cursor `c`,
   sending each 128-byte block (framed as SOH) and awaiting its ACK, then emits
   the EOT + fires Server_complete once all blocks are acked.  Stops early on
   fuel exhaustion, on a missing/unexpected ACK, or on abort.

   The channel history (chr/chs) and the protocol history (pr/ps) are tracked
   with SEPARATE witnesses.  The send-plan coupling `loop_coupling` — held while
   `running` is true — keeps the concrete cursor in lock-step with the ghost
   `yss_sent`/`yss_pending` split, so each `send_block` can discharge
   `hd pending == block cursor`.

   Structural mirror of `YModem.Impl.Client.Loop.ymodem_client_run`, with the
   extra send-plan coupling for the scheduled local send events.
   ─────────────────────────────────────────────────────────────────────────── *)
fn ymodem_server_run
  (i:CC.ymodem_server_impl)
  (ch:TCP.channel)
  (infile:array U8.t)
  (nblocks_sz:SZ.t)
  (blk:array U8.t)
  (out:array U8.t)
  (ctrl:array U8.t)
  (ysnf:array U8.t)
  (fuel:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#nblocks:Ghost.erased nat)
  (#filename:Ghost.erased TCP.bytes)
  (#len:Ghost.erased nat)
requires
  TCP.is_channel ch 'r 's **
  CC.ymodem_server_inv i 'r 's YP.ymodem_server_initial **
  pts_to infile (Ghost.reveal contents) **
  pts_to blk 'blk ** pts_to out 'out ** pts_to ctrl 'ctrl ** pts_to ysnf 'ysnf **
  pure (Seq.length (Ghost.reveal contents) == Ghost.reveal nblocks * 128 /\
        SZ.v nblocks_sz == Ghost.reveal nblocks /\ SZ.fits (Ghost.reveal nblocks * 128) /\
        Seq.length 'blk == 128 /\ Seq.length 'out == 133 /\
        Seq.length 'ctrl == 1 /\ Seq.length 'ysnf == 128)
returns nsent:SZ.t
ensures exists* (chr chs pr ps:TCP.bytes) (st1:YP.ymodem_server_state)
                (bd od cd yd:Seq.seq U8.t).
  TCP.is_channel ch chr chs **
  CC.ymodem_server_inv i pr ps st1 **
  pts_to infile (Ghost.reveal contents) **
  pts_to blk bd ** pts_to out od ** pts_to ctrl cd ** pts_to ysnf yd **
  pure (SZ.v nsent <= Ghost.reveal nblocks)
{
  Plan.blocks_of_plan_wf (Ghost.reveal contents) 0 (Ghost.reveal nblocks);
  let plan = Ghost.hide (Plan.blocks_of (Ghost.reveal contents) 0 (Ghost.reveal nblocks));
  ymodem_server_start i filename len plan;
  Plan.blocks_of_empty (Ghost.reveal contents) 0 0;
  let mut remaining = fuel;
  let mut running = true;
  let mut cursor = 0sz;
  let mut blkno = 1uy;
  while (
    let b = !running;
    let f = !remaining;
    b && not (f = 0sz)
  )
    invariant exists* (st:YP.ymodem_server_state) (cv:SZ.t)
                      (chr chs pr ps:TCP.bytes)
                      (bd od cd yd:Seq.seq U8.t)
                      (rv:bool) (fv:SZ.t) (bn:U8.t).
      TCP.is_channel ch chr chs **
      CC.ymodem_server_inv i pr ps st **
      pts_to infile (Ghost.reveal contents) **
      pts_to blk bd ** pts_to out od ** pts_to ctrl cd ** pts_to ysnf yd **
      R.pts_to cursor cv ** R.pts_to running rv ** R.pts_to remaining fv ** R.pts_to blkno bn **
      pure (Seq.length bd == 128 /\ Seq.length od == 133 /\ Seq.length cd == 1 /\
            Seq.length yd == 128 /\ SZ.v cv <= Ghost.reveal nblocks /\
            (rv == true ==>
              loop_coupling (Ghost.reveal contents) (Ghost.reveal nblocks)
                (Ghost.reveal filename) (Ghost.reveal len) st cv))
  decreases %[(if !running then 1 else 0); SZ.v (!remaining)]
  {
    with st cv. _;
    assert (pure (loop_coupling (Ghost.reveal contents) (Ghost.reveal nblocks)
                    (Ghost.reveal filename) (Ghost.reveal len) st cv));
    let c = !cursor;
    if (SZ.lt c nblocks_sz) {
      (* c < nblocks: send block c, then await its ACK. *)
      Math.lemma_mult_le_right 128 (SZ.v c + 1) (Ghost.reveal nblocks);
      Math.lemma_mult_le_right 128 (SZ.v c) (Ghost.reveal nblocks);
      Math.distributivity_add_left (SZ.v c) 1 128;
      FStar.SizeT.fits_lte (SZ.v c * 128) (Ghost.reveal nblocks * 128);
      let off = SZ.mul c 128sz;
      FStar.SizeT.fits_lte (SZ.v off + 128) (Ghost.reveal nblocks * 128);
      copy_block_arr infile blk off;
      with bd1. _;
      (* bd1 == block contents c == hd pending (the coupling discharge). *)
      Plan.block_slice (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      Plan.blocks_of_unfold (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      Plan.blocks_of_plan_wf (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      assert (pure (Seq.equal bd1 (Plan.block (Ghost.reveal contents) (SZ.v c))));
      assert (pure (Seq.equal (L.hd st.YP.yss_pending) bd1));
      let bn = !blkno;
      blkno := U8.add_mod bn 1uy;
      ymodem_server_send_block i blk bn out;
      with st_a nsent_a oc_a. _;
      (* st_a == send_next_state st; re-derive the shifted plan facts at c+1. *)
      Plan.lemma_send_shift (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      FStar.List.Tot.Properties.append_length st.YP.yss_sent [L.hd st.YP.yss_pending];
      let nw = TCP.write ch out 133sz;
      let nr = TCP.read_full ch ctrl 1sz;
      let res = run_process_network i ysnf ctrl 1sz out;
      with st_b. _;
      lemma_net_post_preserves st_a st_b;
      let s = read_server_status i;
      if (s = 0uy) {
        (* ACK received: acked advanced to cn+1 == length sent; coupling holds at cn+1. *)
        FStar.SizeT.fits_lte (SZ.v c + 1) (Ghost.reveal nblocks);
        cursor := SZ.add c 1sz;
        let f = !remaining;
        if (SZ.gt f 0sz) {
          remaining := SZ.sub f 1sz;
        } else {
          ()
        }
      } else {
        (* No ACK (block still outstanding) or abort: stop. *)
        running := false;
      }
    } else {
      (* c == nblocks: all blocks sent+acked — emit EOT then complete. *)
      Plan.blocks_of_empty (Ghost.reveal contents) (Ghost.reveal nblocks) (Ghost.reveal nblocks);
      ymodem_server_emit_eot i out;
      let nw = TCP.write ch out 1sz;
      ymodem_server_complete i;
      running := false;
    }
  };
  let final_cursor = !cursor;
  final_cursor
}
