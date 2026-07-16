module YModem.Impl.Server.Socket

(**
  Thin verified runner that drives the YMODEM *server* (sender) over a
  `Common.TCP` channel using the GENERIC verified loop
  `Common.ProtocolDriver.drive_steps` specialised to the committed instances
  `YModem.Impl.Server.CanonicalProtocol.ymodem_server_protocol_implementation`
  (the state-machine implementation dictionary) and
  `YModem.Impl.Server.Endpoint.ymodem_server_protocol_endpoint` (the scheduling
  + resource dictionary).

  Structural mirror of the committed client runner
  `YModem.Impl.Client.Socket.fst`'s `run_ymodem_client_channel`
  (setup / fold / rewrite-to-instance-projections / drive / unfold / free),
  retyped to the server, with these differences dictated by the server frame:

    * the server endpoint frame carries TWO extra persistent CELLS, a cursor
      (`sef_cursor : Vec.vec SZ.t`, blocks sent so far) and a started flag
      (`sef_started : Vec.vec U8.t`, `1uy` iff `Server_start` has fired); these
      stay as `Vec` handles (NOT bridged to raw arrays), while the four scratch
      buffers (`sef_blk`/`sef_ysnf`/`sef_out`/`sef_in`) ARE bridged with
      `Vec.to_array_pts_to` / `Vec.to_vec_pts_to`, exactly as the client bridges
      its transport buffers;

    * the initial fold of `ymodem_server_frame_ready` must discharge the coupling
      `cells_ok` (cursor cell `0sz`, started cell `0uy`) and `server_plan_ok` at
      `ymodem_server_initial`; since `ymodem_server_initial.yss_filename == None`,
      `server_plan_ok` reduces to `st == ymodem_server_initial` (reflexive) and
      `cells_ok` reduces to `0 == length [] == 0` and `started_of 0uy <==> None`
      (both immediate); and

    * the caller OWNS the padded send file (`cfg.scfg_file`); the server only
      READS it, so the runner threads its `Vec.pts_to` through the drive
      (it lives inside `frame_ready`) and RETURNS it intact to the caller —
      it is never freed.

  Full leak-free teardown otherwise (all six endpoint vecs are freed, the
  channel is closed, and the impl handle is disposed by `free_ymodem_server`,
  which mirrors the client's `free_ymodem_client`).

  Verified but NOT extracted (`drive_steps` and the endpoint dictionary are not
  Low-star).
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Common.ProtocolImplementation
module PD   = Common.ProtocolDriver
module PE   = Common.ProtocolEndpoint
module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Common.TCP
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module Vec  = Pulse.Lib.Vec
module MR   = Pulse.Lib.MonotonicGhostRef
module L    = FStar.List.Tot

module YP   = YModem.Protocol
module SC   = YModem.Impl.Server.CanonicalProtocol
module EP   = YModem.Impl.Server.Endpoint
module Log  = YModem.Impl.Server.Log
module YMsg = YModem.Wire.Generated.Ymodem_message

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Impl-handle disposal (mirror of the client's `free_ymodem_client`)

   `new_ymodem_server` exposes `pure (Vec.is_full_vec i.status)`; the caller
   threads that pure fact here to `Vec.free` the concrete single-cell status
   vector.  The monotonic ghost progress reference is affine and disposed with
   `drop_` (the only resource dropped — everything concrete is freed).
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn free_ymodem_server
  (i:SC.ymodem_server_impl)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#st:erased YP.ymodem_server_state)
requires
  SC.ymodem_server_inv i received sent st **
  pure (Vec.is_full_vec i.status)
ensures emp
{
  unfold (SC.ymodem_server_inv i received sent st);
  with svs. _;
  Vec.free i.SC.status;
  drop_ (MR.pts_to i.SC.progress #1.0R (Log.mk_log received sent st))
}

(* ───────────────────────────────────────────────────────────────────────────
   The runner: drive the sender over an already-connected channel.

   The caller owns the padded file `cfg.scfg_file` (contents `cfg.scfg_contents`,
   well-formed by `scfg_wf`).  The server only READS it, so we return the
   `Vec.pts_to` intact.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_ymodem_server_channel
  (ch:TCP.channel)
  (cfg:EP.ymodem_server_config)
  (fuel:SZ.t)
requires
  TCP.is_channel ch Seq.empty Seq.empty **
  Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents **
  pure (EP.scfg_wf cfg)
ensures
  Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents
{
  (* 1. Fresh sender handle: pi_invariant at the initial state, plus the pure
        `is_full_vec i.status` witness we need to free it later. *)
  let i = SC.new_ymodem_server ();

  (* 2. Allocate the endpoint's persistent state.  The two cells stay as `Vec`
        handles; the four scratch buffers become raw-array points-to (their
        frame fields are `array U8.t`). *)
  let cursor  = Vec.alloc 0sz 1sz;    // cursor cell:  blocks sent so far
  let started = Vec.alloc 0uy 1sz;    // started flag: 1uy iff Server_start fired
  let blk_v   = Vec.alloc 0uy 128sz;  // 128-byte payload scratch (sef_blk)
  let ysnf_v  = Vec.alloc 0uy 128sz;  // 128-byte process_network scratch (sef_ysnf)
  let out_v   = Vec.alloc 0uy 133sz;  // 133-byte output buffer (sef_out)
  let in_v    = Vec.alloc 0uy 1sz;    // 1-byte control input (sef_in)
  Vec.to_array_pts_to blk_v;
  Vec.to_array_pts_to ysnf_v;
  Vec.to_array_pts_to out_v;
  Vec.to_array_pts_to in_v;

  let frame : EP.ymodem_server_endpoint_frame = {
    EP.sef_cursor  = cursor;
    EP.sef_started = started;
    EP.sef_blk     = Vec.vec_to_array blk_v;
    EP.sef_ysnf    = Vec.vec_to_array ysnf_v;
    EP.sef_out     = Vec.vec_to_array out_v;
    EP.sef_in      = Vec.vec_to_array in_v;
  };
  assert (pure (frame.EP.sef_cursor  == cursor));
  assert (pure (frame.EP.sef_started == started));
  assert (pure (frame.EP.sef_blk     == Vec.vec_to_array blk_v));
  assert (pure (frame.EP.sef_ysnf    == Vec.vec_to_array ysnf_v));
  assert (pure (frame.EP.sef_out     == Vec.vec_to_array out_v));
  assert (pure (frame.EP.sef_in      == Vec.vec_to_array in_v));

  rewrite (Vec.pts_to cursor (Seq.create 1 0sz))
      as  (Vec.pts_to frame.EP.sef_cursor (Seq.create 1 0sz));
  rewrite (Vec.pts_to started (Seq.create 1 0uy))
      as  (Vec.pts_to frame.EP.sef_started (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array blk_v) (Seq.create 128 0uy))
      as  (pts_to frame.EP.sef_blk (Seq.create 128 0uy));
  rewrite (pts_to (Vec.vec_to_array ysnf_v) (Seq.create 128 0uy))
      as  (pts_to frame.EP.sef_ysnf (Seq.create 128 0uy));
  rewrite (pts_to (Vec.vec_to_array out_v) (Seq.create 133 0uy))
      as  (pts_to frame.EP.sef_out (Seq.create 133 0uy));
  rewrite (pts_to (Vec.vec_to_array in_v) (Seq.create 1 0uy))
      as  (pts_to frame.EP.sef_in (Seq.create 1 0uy));

  (* 3. Discharge the coupling at the initial state, fold the endpoint's
        persistent resources, then re-present them as the instance's projected
        slprops so unification pins `drive_steps`. *)
  assert (pure (YP.ymodem_server_initial.YP.yss_filename == None));
  assert (pure (L.length YP.ymodem_server_initial.YP.yss_sent == 0));

  fold (EP.ymodem_server_frame_ready i cfg frame YP.ymodem_server_initial);
  fold (EP.ymodem_server_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_server_initial);

  rewrite (SC.ymodem_server_inv i Seq.empty Seq.empty YP.ymodem_server_initial)
      as  (SC.ymodem_server_protocol_implementation.CPI.pi_invariant
            i Seq.empty Seq.empty YP.ymodem_server_initial);
  rewrite (EP.ymodem_server_frame_ready i cfg frame YP.ymodem_server_initial)
      as  (EP.ymodem_server_protocol_endpoint.PE.pe_frame_ready
            i cfg frame YP.ymodem_server_initial);
  rewrite (EP.ymodem_server_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_server_initial)
      as  (EP.ymodem_server_protocol_endpoint.PE.pe_io_ready
            i ch frame Seq.empty Seq.empty YP.ymodem_server_initial);

  (* 4. Run the GENERIC verified driver.  Implicits are given explicitly so the
        polymorphic protocol/endpoint dictionaries resolve unambiguously. *)
  let _res =
    PD.drive_steps
      #SC.ymodem_server_impl
      #YP.ymodem_server_state
      #YMsg.ymodem_message
      #YP.ymodem_server_local
      #unit
      #SC.ymodem_server_protocol_implementation
      #EP.ymodem_server_protocol_endpoint
      i cfg frame ch fuel
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide YP.ymodem_server_initial);
  with received1 sent1 st1. _;

  (* 5. Tear everything down.  Re-present the instance slprops as the endpoint's
        own definitions, unfold to recover the cells/buffers/channel, close and
        free — except the file, which is returned to the caller. *)
  rewrite (EP.ymodem_server_protocol_endpoint.PE.pe_frame_ready
            i cfg frame (Ghost.reveal st1))
      as  (EP.ymodem_server_frame_ready i cfg frame (Ghost.reveal st1));
  rewrite (EP.ymodem_server_protocol_endpoint.PE.pe_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (EP.ymodem_server_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  rewrite (SC.ymodem_server_protocol_implementation.CPI.pi_invariant
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (SC.ymodem_server_inv
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));

  unfold (EP.ymodem_server_frame_ready i cfg frame (Ghost.reveal st1));
  with cv_f bv_f blk_f ysnf_f. _;
  unfold (EP.ymodem_server_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  with raw_f out_f in_f. _;

  TCP.close ch;

  (* Free the four array-backed scratch vecs (bridge each raw-array points-to
     back to its `Vec` and free). *)
  rewrite (pts_to frame.EP.sef_blk blk_f) as (pts_to (Vec.vec_to_array blk_v) blk_f);
  Vec.to_vec_pts_to blk_v;
  Vec.free blk_v;
  rewrite (pts_to frame.EP.sef_ysnf ysnf_f) as (pts_to (Vec.vec_to_array ysnf_v) ysnf_f);
  Vec.to_vec_pts_to ysnf_v;
  Vec.free ysnf_v;
  rewrite (pts_to frame.EP.sef_out out_f) as (pts_to (Vec.vec_to_array out_v) out_f);
  Vec.to_vec_pts_to out_v;
  Vec.free out_v;
  rewrite (pts_to frame.EP.sef_in in_f) as (pts_to (Vec.vec_to_array in_v) in_f);
  Vec.to_vec_pts_to in_v;
  Vec.free in_v;

  (* Free the two persistent cell vecs (kept as `Vec` handles throughout). *)
  rewrite (Vec.pts_to frame.EP.sef_cursor cv_f) as (Vec.pts_to cursor cv_f);
  Vec.free cursor;
  rewrite (Vec.pts_to frame.EP.sef_started bv_f) as (Vec.pts_to started bv_f);
  Vec.free started;

  (* Dispose the impl handle; the file's `Vec.pts_to cfg.scfg_file` remains and
     is returned to the caller (server only READS it). *)
  free_ymodem_server i #received1 #sent1 #st1
}

(* ───────────────────────────────────────────────────────────────────────────
   Connect-style entry: connect, then drive; the host buffer and the send file
   are both returned intact.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_ymodem_server_connect
  (host:array U8.t)
  (host_len:SZ.t)
  (port:U16.t)
  (cfg:EP.ymodem_server_config)
  (fuel:SZ.t)
requires
  pts_to host 'h **
  Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents **
  pure (Seq.length 'h == SZ.v host_len /\ EP.scfg_wf cfg)
ensures
  pts_to host 'h **
  Vec.pts_to cfg.EP.scfg_file cfg.EP.scfg_contents
{
  match TCP.connect_tcp host host_len port {
    Some ch -> {
      (* `connect_tcp` yields the empty history as `Seq.create 0 0uy`; the runner
         wants it as `Seq.empty`.  They are extensionally equal (both length 0). *)
      assert (pure (Seq.equal (Seq.create 0 0uy) (Seq.empty #U8.t)));
      rewrite (TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy))
          as  (TCP.is_channel ch Seq.empty Seq.empty);
      run_ymodem_server_channel ch cfg fuel
    }
    None -> {
      ()
    }
  }
}
