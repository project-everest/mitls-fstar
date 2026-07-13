module YModem.Impl.Client.Loop

(**
  A verified, **Low*-EXTRACTABLE** YMODEM *client* (receiver) driver loop.

  Unlike `YModem.Impl.Client.Socket.run_ymodem_client_channel` — which runs the
  GENERIC typeclass-polymorphic driver `Common.ProtocolDriver.drive_steps` and is
  therefore NOT extractable — this module contains a bespoke, first-order Pulse
  loop that DIRECTLY reuses the committed verified leaf
  `YModem.Impl.Client.CanonicalProtocol.ymodem_client_process_network`.  Every
  step of the runnable C loop is verified: the framed read, the
  `process_network` dispatch, the ACK write-back, and the payload reconstruction
  into a caller-provided buffer.

  Structural mirror of `calc_sample/impl/Calc.Server.Socket.fst`'s
  `run_connection_loop`: a `while` loop over fuel with an `exists*` invariant
  binding the erased ghost history (received/sent/state) and the concrete
  channel + scratch buffers, plus concrete `Reference` cells for the fuel
  counter, the running flag and the reconstruction cursor.

  EXTRACTS to clean Low* C via KaRaMeL (the impl handle erases to just the
  status-byte pointer; the ghost MonotonicGhostRef vanishes).
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
module AC   = Pulse.Lib.Array.Core

module YP   = YModem.Protocol
module CC   = YModem.Impl.Client.CanonicalProtocol
module Log  = YModem.Impl.Client.Log

open YModem.Wire.Generated.Ymodem_message
open YModem.Impl.Control

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   1.  ymodem_client_start — a Low* wrapper for the Client_start bootstrap.

   Its concrete effect is PURELY the status flip 0uy -> 1uy; the filename/len
   only feed the GHOST state, so they are taken ERASED.  Modelled on the
   `Client_start` branch of `ymodem_client_process_local`.  Since the
   precondition pins `ycs_filename == None`, `yc_status_flag_ok` forces the
   runtime status cell to `0uy`, so the `else` branch is dead (`unreachable`).

   EXTRACTS to roughly `void ymodem_client_start(uint8_t *i){ if(i[0]==0) i[0]=1; }`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn ymodem_client_start
  (i:CC.ymodem_client_impl)
  (filename:Ghost.erased TCP.bytes)
  (len:Ghost.erased nat)
  (received sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_client_state)
requires
  CC.ymodem_client_inv i received sent st **
  pure ((Ghost.reveal st).YP.ycs_filename == None)
ensures
  CC.ymodem_client_inv i received sent
    (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len))
{
  unfold (CC.ymodem_client_inv i received sent st);
  with svs. _;
  let s = Vec.op_Array_Access i.CC.status 0sz;
  if (s = 0uy) {
    Vec.op_Array_Assignment i.CC.status 0sz 1uy;
    with svs2. _;
    Log.lemma_yc_start_advance received sent st (Ghost.reveal filename) (Ghost.reveal len);
    RTC.closure_step Log.yc_step_rel
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st))
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
        (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len)));
    MR.update i.CC.progress
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
        (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len)));
    fold (CC.ymodem_client_inv i received sent
      (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal len)));
  } else {
    unreachable ()
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2a.  run_process_network — a first-order wrapper around the committed
   `ymodem_client_process_network` leaf.  Builds the single-field network frame
   from the caller's 128-byte scratch `ycnf`, folds the (relaxed) frame
   precondition, dispatches, and unfolds the frame postcondition to hand the
   scratch buffer back.  Extracts to a direct `process_network` call.
   ─────────────────────────────────────────────────────────────────────────── *)

fn run_process_network
  (i:CC.ymodem_client_impl)
  (ycnf:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (ack:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_client_state)
  (#yc #ic #ac:Ghost.erased (Seq.seq U8.t))
requires
  CC.ymodem_client_inv i received sent st **
  pts_to ycnf yc **
  pts_to input ic **
  pts_to ack ac **
  pure (Seq.length yc == 128 /\ SZ.v input_len == Seq.length ic /\
        SZ.v input_len >= 1 /\ Seq.length ac == 1)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes) (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased YP.ymodem_client_state)
                (yc1 ac1:Seq.seq U8.t).
  CC.ymodem_client_inv i received1 sent1 st1 **
  pts_to ycnf yc1 **
  pts_to input ic **
  pts_to ack ac1 **
  pure (Seq.length yc1 == 128 /\ Seq.length ac1 == 1)
{
  let frame : CC.ymodem_client_network_frame = { CC.ycnf_data = ycnf };
  rewrite (pts_to ycnf yc) as (pts_to frame.CC.ycnf_data yc);
  fold (CC.ymodem_client_network_frame_pre frame input input_len ack 1sz ic ac);
  let result =
    CC.ymodem_client_process_network i frame input input_len ack 1sz
      received sent st ic ac;
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs. _;
  unfold (CC.ymodem_client_network_frame_post
            frame result ic input_len ac out_contents st st1
            consumed wire_outputs local_outputs);
  with yc1. _;
  rewrite (pts_to frame.CC.ycnf_data yc1) as (pts_to ycnf yc1);
  result
}

(* ───────────────────────────────────────────────────────────────────────────
   2b.  array_blit — copy `src[0..n)` into `dst[dst_off..dst_off+n)` through a
   concrete sub-array view (`to_mask`/`sub`/`from_mask`/`memcpy_l`/`return_sub`),
   exactly the framing pattern `YModem.Impl.Client.Endpoint.fill_soh_tail` uses.
   Extracts to a `memcpy(dst + dst_off, src, n)`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn array_blit
  (dst:array U8.t) (dst_off:SZ.t) (src:array U8.t) (n:SZ.t)
  (#dc #sc:Ghost.erased (Seq.seq U8.t))
requires
  pts_to dst dc ** pts_to src sc **
  pure (SZ.v dst_off + SZ.v n <= Seq.length dc /\ SZ.v n <= Seq.length sc)
returns _:unit
ensures exists* (dc':Seq.seq U8.t).
  pts_to dst dc' ** pts_to src sc **
  pure (Seq.length dc' == Seq.length dc)
{
  pts_to_len dst;
  pts_to_len src;
  to_mask dst;
  let sub = AC.sub dst dst_off (SZ.v dst_off + SZ.v n);
  from_mask sub;
  pts_to_len sub;
  let _sq = A.memcpy_l n src sub;
  to_mask sub;
  AC.return_sub dst;
  from_mask dst;
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   2c.  maybe_write_ack — send the 1-byte ACK iff `process_network` produced one
   (`process_produced_len == 1`).  The channel's sent-history advances in the
   write branch and is unchanged otherwise; the explicit `exists*` post joins
   both cases.
   ─────────────────────────────────────────────────────────────────────────── *)

fn maybe_write_ack
  (ch:TCP.channel)
  (ack:array U8.t)
  (produced_len:SZ.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#ac:Ghost.erased (Seq.seq U8.t))
requires
  TCP.is_channel ch received sent **
  pts_to ack ac **
  pure (Seq.length ac == 1)
returns _:unit
ensures exists* (sent1:TCP.bytes).
  TCP.is_channel ch received sent1 **
  pts_to ack ac
{
  if (produced_len = 1sz) {
    let n = TCP.write ch ack 1sz;
    ()
  } else {
    ()
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2d.  maybe_copy_payload — after an SOH block, append the 128-byte payload
   (now sitting in `ycnf`) to the running reconstruction `outbuf` at `cursor`,
   advancing the cursor.  If it would overflow `outcap`, stop the loop by
   clearing `running`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn maybe_copy_payload
  (ycnf:array U8.t)
  (outbuf:array U8.t)
  (cursor:R.ref SZ.t)
  (running:R.ref bool)
  (outcap:SZ.t)
  (#yc #ob:Ghost.erased (Seq.seq U8.t))
  (#cv0:Ghost.erased SZ.t)
  (#rn0:Ghost.erased bool)
requires
  pts_to ycnf yc **
  pts_to outbuf ob **
  R.pts_to cursor cv0 **
  R.pts_to running rn0 **
  pure (Seq.length yc == 128 /\ Seq.length ob == SZ.v outcap /\
        SZ.v (Ghost.reveal cv0) <= SZ.v outcap)
returns _:unit
ensures exists* (ob1:Seq.seq U8.t) (cv1:SZ.t) (rn1:bool).
  pts_to ycnf yc **
  pts_to outbuf ob1 **
  R.pts_to cursor cv1 **
  R.pts_to running rn1 **
  pure (Seq.length ob1 == SZ.v outcap /\ SZ.v cv1 <= SZ.v outcap)
{
  let cv = R.read cursor;
  let room = SZ.sub outcap cv;
  if (SZ.gte room 128sz) {
    array_blit outbuf cv ycnf 128sz;
    let ncv = SZ.add cv 128sz;
    R.write cursor ncv;
  } else {
    R.write running false;
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2e.  read_status_update — read the runtime status cell and either stop the
   loop (status `2uy` Completed / `3uy` Aborted) or consume one unit of fuel.
   ─────────────────────────────────────────────────────────────────────────── *)

fn read_status_update
  (i:CC.ymodem_client_impl)
  (running:R.ref bool)
  (remaining:R.ref SZ.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased YP.ymodem_client_state)
  (#rn0:Ghost.erased bool)
  (#f0:Ghost.erased SZ.t)
requires
  CC.ymodem_client_inv i received sent st **
  R.pts_to running rn0 **
  R.pts_to remaining f0
returns _:unit
ensures exists* (rn1:bool) (f1:SZ.t).
  CC.ymodem_client_inv i received sent st **
  R.pts_to running rn1 **
  R.pts_to remaining f1
{
  unfold (CC.ymodem_client_inv i received sent st);
  with svs. _;
  let sv = Vec.op_Array_Access i.CC.status 0sz;
  fold (CC.ymodem_client_inv i received sent st);
  if (sv = 2uy || sv = 3uy) {
    R.write running false;
  } else {
    let f = R.read remaining;
    if (SZ.gt f 0sz) {
      R.write remaining (SZ.sub f 1sz);
    } else {
      ()
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   3.  ymodem_client_run — the verified Low* receiver driver loop.

   Bounded by `fuel`; also stops as soon as the status cell reaches `2uy`
   (Completed) or `3uy` (Aborted), or the reconstruction buffer `outbuf` fills.
   Each iteration performs a framed read, dispatches it through the committed
   `ymodem_client_process_network` leaf, writes back an ACK when one is
   produced, and (for an SOH data block) appends the 128-byte payload to
   `outbuf` at the running cursor.

   The channel history and the protocol (ghost) history are tracked with
   SEPARATE witnesses: an unrecognized/finished frame is consumed from the wire
   (advancing the channel history) yet is a sound protocol no-op (leaving the
   protocol history unchanged), so the two are not kept equal.

   Structural mirror of `calc_sample/impl/Calc.Server.Socket.run_connection_loop`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn ymodem_client_run
  (i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (ctrl:array U8.t) (soh:array U8.t) (tail:array U8.t) (ack:array U8.t) (ycnf:array U8.t)
  (outbuf:array U8.t) (outcap:SZ.t)
  (fuel:SZ.t)
requires
  TCP.is_channel ch 'r 's **
  CC.ymodem_client_inv i 'r 's 'st **
  pts_to ctrl 'c ** pts_to soh 'so ** pts_to tail 't **
  pts_to ack 'a ** pts_to ycnf 'y ** pts_to outbuf 'o **
  pure (Seq.length 'c == 1 /\ Seq.length 'so == 133 /\ Seq.length 't == 132 /\
        Seq.length 'a == 1 /\ Seq.length 'y == 128 /\ Seq.length 'o == SZ.v outcap)
returns nbytes:SZ.t
ensures exists* (chr chs pr ps:TCP.bytes) (st1:YP.ymodem_client_state)
                (c so t a y o:Seq.seq U8.t).
  TCP.is_channel ch chr chs **
  CC.ymodem_client_inv i pr ps st1 **
  pts_to ctrl c ** pts_to soh so ** pts_to tail t **
  pts_to ack a ** pts_to ycnf y ** pts_to outbuf o **
  pure (SZ.v nbytes <= SZ.v outcap)
{
  let mut remaining = fuel;
  let mut running = true;
  let mut cursor = 0sz;
  while (
    let b = !running;
    let rem = !remaining;
    b && not (rem = 0sz)
  )
    invariant live running
    invariant live remaining
    invariant exists* (chr chs pr ps:TCP.bytes) (st:YP.ymodem_client_state)
                      (c so t a y o:Seq.seq U8.t) (cv:SZ.t).
      TCP.is_channel ch chr chs **
      CC.ymodem_client_inv i pr ps st **
      pts_to ctrl c ** pts_to soh so ** pts_to tail t **
      pts_to ack a ** pts_to ycnf y ** pts_to outbuf o **
      R.pts_to cursor cv **
      pure (Seq.length c == 1 /\ Seq.length so == 133 /\ Seq.length t == 132 /\
            Seq.length a == 1 /\ Seq.length y == 128 /\ Seq.length o == SZ.v outcap /\
            SZ.v cv <= SZ.v outcap)
  {
    let nlead = TCP.read_full ch ctrl 1sz;
    let lead = ctrl.(0sz);
    if (lead = 1uy) {
      (* SOH: assemble the 133-byte frame in `soh` and dispatch it. *)
      soh.(0sz) <- 1uy;
      let ntail = TCP.read_full ch tail 132sz;
      array_blit soh 1sz tail 132sz;
      let result = run_process_network i ycnf soh 133sz ack;
      maybe_write_ack ch ack result.CPI.process_produced_len;
      maybe_copy_payload ycnf outbuf cursor running outcap;
      read_status_update i running remaining;
    } else {
      (* Control frame (EOT / CAN / anything else): dispatch the single byte. *)
      let result = run_process_network i ycnf ctrl 1sz ack;
      maybe_write_ack ch ack result.CPI.process_produced_len;
      read_status_update i running remaining;
    }
  };
  let final_cursor = !cursor;
  final_cursor
}
