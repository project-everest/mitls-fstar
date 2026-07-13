module YModem.Impl.Client.Socket

(**
  Thin verified runner that drives the YMODEM *client* (receiver) over a
  `Common.TCP` channel using the GENERIC verified loop
  `Common.ProtocolDriver.drive_steps` specialised to the committed instances
  `YModem.Impl.Client.CanonicalProtocol.ymodem_client_protocol_implementation`
  (the state-machine implementation dictionary) and
  `YModem.Impl.Client.Endpoint.ymodem_client_protocol_endpoint` (the scheduling
  + resource dictionary).

  Structural mirror of `Calc.Server.Endpoint.fst`'s `run_channel_endpoint`
  (setup / fold / rewrite-to-instance-projections / drive / unfold / free),
  except:

    * the driver invoked is the GENERIC `Common.ProtocolDriver.drive_steps`
      (a typeclass-polymorphic recursion), NOT a bespoke per-endpoint loop; and

    * the endpoint frame stores raw `array U8.t` buffers (obtained from
      `Pulse.Lib.Vec` handles via `Vec.vec_to_array`), so we bridge each
      `Vec.pts_to` to `pts_to (Vec.vec_to_array _)` with `Vec.to_array_pts_to`
      on setup and back with `Vec.to_vec_pts_to` on teardown, exactly as
      `Calc.Server.CanonicalProtocol.fst` bridges its network-frame arrays.

  Full leak-free teardown is achieved (`ensures emp`): the four endpoint vecs
  and the channel are freed/closed, and the impl handle is disposed by
  `free_ymodem_client` below, which mirrors calc's `free_canonical_server`
  (`Vec.free` the concrete status cell, `drop_` the ghost progress ref).  This
  relies on `new_ymodem_client` exposing `pure (Vec.is_full_vec i.status)` — the
  same enabler calc's `new_canonical_server` provides for its own teardown.

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

module YP   = YModem.Protocol
module CC   = YModem.Impl.Client.CanonicalProtocol
module EP   = YModem.Impl.Client.Endpoint
module Log  = YModem.Impl.Client.Log
module YMsg = YModem.Wire.Generated.Ymodem_message

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Impl-handle disposal (mirror of calc's `free_canonical_server`)

   `new_ymodem_client` exposes `pure (Vec.is_full_vec i.status)`; the caller
   threads that pure fact here to `Vec.free` the concrete single-cell status
   vector.  The monotonic ghost progress reference is affine and disposed with
   `drop_` (the only resource dropped — everything concrete is freed).
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn free_ymodem_client
  (i:CC.ymodem_client_impl)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#st:erased YP.ymodem_client_state)
requires
  CC.ymodem_client_inv i received sent st **
  pure (Vec.is_full_vec i.status)
ensures emp
{
  unfold (CC.ymodem_client_inv i received sent st);
  with svs. _;
  Vec.free i.CC.status;
  drop_ (MR.pts_to i.CC.progress #1.0R (Log.mk_log received sent st))
}

(* ───────────────────────────────────────────────────────────────────────────
   The runner: drive the receiver over an already-connected channel.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_ymodem_client_channel
  (ch:TCP.channel)
  (cfg:EP.ymodem_client_config)
  (fuel:SZ.t)
requires TCP.is_channel ch Seq.empty Seq.empty
ensures emp
{
  (* 1. Fresh receiver handle: pi_invariant at the initial state, plus the pure
        `is_full_vec i.status` witness we need to free it later. *)
  let i = CC.new_ymodem_client ();

  (* 2. Allocate the four persistent transport buffers as heap vecs, then expose
        their contents as raw-array points-to so they can populate the endpoint
        frame (whose fields are `array U8.t`). *)
  let ctrl = Vec.alloc 0uy 1sz;
  let soh  = Vec.alloc 0uy 133sz;
  let ack  = Vec.alloc 0uy 1sz;
  let ycnf = Vec.alloc 0uy 128sz;
  Vec.to_array_pts_to ctrl;
  Vec.to_array_pts_to soh;
  Vec.to_array_pts_to ack;
  Vec.to_array_pts_to ycnf;

  let frame : EP.ymodem_client_endpoint_frame = {
    EP.yef_ctrl = Vec.vec_to_array ctrl;
    EP.yef_soh  = Vec.vec_to_array soh;
    EP.yef_ack  = Vec.vec_to_array ack;
    EP.yef_ycnf = Vec.vec_to_array ycnf;
  };
  assert (pure (frame.EP.yef_ctrl == Vec.vec_to_array ctrl));
  assert (pure (frame.EP.yef_soh  == Vec.vec_to_array soh));
  assert (pure (frame.EP.yef_ack  == Vec.vec_to_array ack));
  assert (pure (frame.EP.yef_ycnf == Vec.vec_to_array ycnf));
  rewrite (pts_to (Vec.vec_to_array ctrl) (Seq.create 1 0uy))
      as  (pts_to frame.EP.yef_ctrl (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array soh) (Seq.create 133 0uy))
      as  (pts_to frame.EP.yef_soh (Seq.create 133 0uy));
  rewrite (pts_to (Vec.vec_to_array ack) (Seq.create 1 0uy))
      as  (pts_to frame.EP.yef_ack (Seq.create 1 0uy));
  rewrite (pts_to (Vec.vec_to_array ycnf) (Seq.create 128 0uy))
      as  (pts_to frame.EP.yef_ycnf (Seq.create 128 0uy));

  (* 3. Fold the endpoint's persistent resources, then re-present them as the
        instance's projected slprops so unification pins `drive_steps`. *)
  fold (EP.ymodem_client_frame_ready i cfg frame YP.ymodem_client_initial);
  fold (EP.ymodem_client_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_client_initial);

  rewrite (CC.ymodem_client_inv i Seq.empty Seq.empty YP.ymodem_client_initial)
      as  (CC.ymodem_client_protocol_implementation.CPI.pi_invariant
            i Seq.empty Seq.empty YP.ymodem_client_initial);
  rewrite (EP.ymodem_client_frame_ready i cfg frame YP.ymodem_client_initial)
      as  (EP.ymodem_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame YP.ymodem_client_initial);
  rewrite (EP.ymodem_client_io_ready i ch frame Seq.empty Seq.empty YP.ymodem_client_initial)
      as  (EP.ymodem_client_protocol_endpoint.PE.pe_io_ready
            i ch frame Seq.empty Seq.empty YP.ymodem_client_initial);

  (* 4. Run the GENERIC verified driver.  Implicits are given explicitly so the
        polymorphic protocol/endpoint dictionaries resolve unambiguously. *)
  let _res =
    PD.drive_steps
      #CC.ymodem_client_impl
      #YP.ymodem_client_state
      #YMsg.ymodem_message
      #YP.ymodem_client_local
      #unit
      #CC.ymodem_client_protocol_implementation
      #EP.ymodem_client_protocol_endpoint
      i cfg frame ch fuel
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide #TCP.bytes Seq.empty)
      (Ghost.hide YP.ymodem_client_initial);
  with received1 sent1 st1. _;

  (* 5. Tear everything down.  Re-present the instance slprops as the endpoint's
        own definitions, unfold to recover the buffers/channel, close and free. *)
  rewrite (EP.ymodem_client_protocol_endpoint.PE.pe_frame_ready
            i cfg frame (Ghost.reveal st1))
      as  (EP.ymodem_client_frame_ready i cfg frame (Ghost.reveal st1));
  rewrite (EP.ymodem_client_protocol_endpoint.PE.pe_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (EP.ymodem_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  rewrite (CC.ymodem_client_protocol_implementation.CPI.pi_invariant
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
      as  (CC.ymodem_client_inv
            i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));

  unfold (EP.ymodem_client_frame_ready i cfg frame (Ghost.reveal st1));
  with d_final. _;
  unfold (EP.ymodem_client_io_ready
            i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
  with raw_final ctrl_final soh_final ack_final. _;

  TCP.close ch;

  rewrite (pts_to frame.EP.yef_ycnf d_final) as (pts_to (Vec.vec_to_array ycnf) d_final);
  Vec.to_vec_pts_to ycnf;
  Vec.free ycnf;
  rewrite (pts_to frame.EP.yef_ctrl ctrl_final) as (pts_to (Vec.vec_to_array ctrl) ctrl_final);
  Vec.to_vec_pts_to ctrl;
  Vec.free ctrl;
  rewrite (pts_to frame.EP.yef_soh soh_final) as (pts_to (Vec.vec_to_array soh) soh_final);
  Vec.to_vec_pts_to soh;
  Vec.free soh;
  rewrite (pts_to frame.EP.yef_ack ack_final) as (pts_to (Vec.vec_to_array ack) ack_final);
  Vec.to_vec_pts_to ack;
  Vec.free ack;

  free_ymodem_client i #received1 #sent1 #st1
}

(* ───────────────────────────────────────────────────────────────────────────
   Connect-style entry: connect, then drive; the host buffer is returned intact.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn run_ymodem_client_connect
  (host:array U8.t)
  (host_len:SZ.t)
  (port:U16.t)
  (cfg:EP.ymodem_client_config)
  (fuel:SZ.t)
requires
  pts_to host 'h **
  pure (Seq.length 'h == SZ.v host_len)
ensures pts_to host 'h
{
  match TCP.connect_tcp host host_len port {
    Some ch -> {
      (* `connect_tcp` yields the empty history as `Seq.create 0 0uy`; the runner
         wants it as `Seq.empty`.  They are extensionally equal (both length 0). *)
      assert (pure (Seq.equal (Seq.create 0 0uy) (Seq.empty #U8.t)));
      rewrite (TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy))
          as  (TCP.is_channel ch Seq.empty Seq.empty);
      run_ymodem_client_channel ch cfg fuel
    }
    None -> {
      ()
    }
  }
}
