module YModem.Impl.Client.Endpoint

(**
  YMODEM *client* (receiver) driver-facing endpoint: a full 28-field instance of
  `Common.ProtocolEndpoint.protocol_endpoint` over the committed dictionary
  `YModem.Impl.Client.CanonicalProtocol.ymodem_client_protocol_implementation`.

  This is the executable scheduling + resource layer that lets the GENERIC
  verified loop `Common.ProtocolDriver.drive_steps` run the receiver.  It reuses
  the driver loop verbatim (it is a typeclass argument), so NO loop is written
  here.

  Structural mirror of the template `Calc.Server.Endpoint.fst`, retyped to the
  YMODEM client types, with three novelties:

    1. `pe_next_action` reads the runtime status cell and SCHEDULES:
         status 0uy (fresh, filename None) -> EndpointLocal (Client_start ...)  (bootstrap)
         status 1uy (receiving)            -> EndpointNeedInput                 (await a packet)
         status 2uy (completed)            -> EndpointDone
         status 3uy (aborted)              -> EndpointFailed
       (calc always returns NeedInput.)

    2. `pe_prepare_network` performs a FRAMED read of one complete YMODEM frame
       of a priori unknown size: it peeks the 1-byte lead, then either keeps the
       1-byte control frame or reads the 132-byte tail to assemble the 133-byte
       SOH frame.  The relaxed frame precondition keeps
       `input_len == Seq.length input_contents`, so the concrete input array is
       EXACTLY the message length (1 for a control frame, 133 for an SOH frame).

    3. The `EndpointLocal` (Client_start bootstrap) case is LIVE, not the
       `pure False` stub calc uses.

  Config note: in real YMODEM the receiver's filename/length come from header
  block 0 (impl glue not modelled in the SM); for this verified slice the config
  supplies them.  We use a CONCRETE `TCP.bytes` filename (NOT `Ghost.erased`,
  which the task literally suggested) because the concrete `EndpointLocal
  (Client_start filename len)` scheduled by `pe_next_action` needs a total
  (non-ghost) filename, and `pi_process_local` matches the event concretely.

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
module MR = Pulse.Lib.MonotonicGhostRef
module AC = Pulse.Lib.Array.Core

module YP = YModem.Protocol
module CC = YModem.Impl.Client.CanonicalProtocol

open YModem.Wire.Generated.Ymodem_message

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint config (§ pe_config)
   ─────────────────────────────────────────────────────────────────────────── *)

(* Concrete filename + length that seed the receiver's `Client_start`. *)
noeq
type ymodem_client_config = {
  ycfg_filename : TCP.bytes;
  ycfg_len      : nat;
}

(* ───────────────────────────────────────────────────────────────────────────
   Endpoint frame (§ pe_frame): the persistent concrete I/O buffers
   ─────────────────────────────────────────────────────────────────────────── *)

(* VARIABLE-length inputs: the relaxed network frame precondition keeps
   `input_len == Seq.length input_contents`, so the input array is EXACTLY the
   message length.  We keep a 1-byte control buffer and a 133-byte SOH buffer;
   `pe_prepare_network` selects one as the input and threads the other. *)
noeq
type ymodem_client_endpoint_frame = {
  yef_ctrl : array U8.t;   // 1-byte buffer: a control frame (EOT/CAN/…) OR the peeked lead
  yef_soh  : array U8.t;   // 133-byte buffer: an assembled SOH data frame
  yef_ack  : array U8.t;   // 1-byte output buffer: the ACK the receiver emits
  yef_ycnf : array U8.t;   // 128-byte scratch handed to process_network (ycnf_data)
}

(* ───────────────────────────────────────────────────────────────────────────
   Persistent slprops (§ pe_frame_ready, pe_io_ready)
   ─────────────────────────────────────────────────────────────────────────── *)

(* frame_ready owns ONLY the 128-byte scratch: the network frame post-condition
   owns `ycnf_data`, so finishing a network action re-establishes frame_ready. *)
let ymodem_client_frame_ready
  (_i:CC.ymodem_client_impl)
  (_cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (_st:YP.ymodem_client_state)
  : slprop =
  exists* (d:Seq.seq U8.t).
    pts_to frame.yef_ycnf d **
    pure (Seq.length d == 128)

(* io_ready owns the channel + the three transport buffers (ctrl/soh/ack).  The
   raw received history is existential (decoupled from the abstract `received`,
   like calc). *)
let ymodem_client_io_ready
  (_i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (frame:ymodem_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_client_state)
  : slprop =
  exists* (raw:TCP.bytes) (ctrl_b:Seq.seq U8.t) (soh_b:Seq.seq U8.t) (ack_b:Seq.seq U8.t).
    TCP.is_channel ch raw sent **
    pts_to frame.yef_ctrl ctrl_b **
    pts_to frame.yef_soh soh_b **
    pts_to frame.yef_ack ack_b **
    pure (
      Seq.length ctrl_b == 1 /\
      Seq.length soh_b == 133 /\
      Seq.length ack_b == 1)

(* ───────────────────────────────────────────────────────────────────────────
   Action frame (§ pe_action_frame) — a LIVE slprop for EACH of the four cases
   ─────────────────────────────────────────────────────────────────────────── *)

let ymodem_client_action_frame
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (st:YP.ymodem_client_state)
  (action:PE.endpoint_action
    CC.ymodem_client_network_frame
    YP.ymodem_client_local
    CC.ymodem_client_local_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput network_frame ->
    ymodem_client_frame_ready i cfg frame st **
    pure (network_frame.CC.ycnf_data == frame.yef_ycnf)
  | PE.EndpointLocal _ _ ->
    ymodem_client_frame_ready i cfg frame st
  | PE.EndpointDone
  | PE.EndpointFailed ->
    ymodem_client_frame_ready i cfg frame st

(* Network continuation carries only the equality linking the network frame's
   scratch to the endpoint frame's scratch (so finish_network_action can rebuild
   frame_ready from the frame post). *)
let ymodem_client_network_continuation
  (_i:CC.ymodem_client_impl)
  (_cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (_st:YP.ymodem_client_state)
  (network_frame:CC.ymodem_client_network_frame)
  : slprop =
  pure (network_frame.CC.ycnf_data == frame.yef_ycnf)

(* Local continuation owns the 128-byte scratch (untouched by the local event)
   so finish_local_action rebuilds frame_ready. *)
let ymodem_client_local_continuation
  (_i:CC.ymodem_client_impl)
  (_cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (_st:YP.ymodem_client_state)
  (_ev:YP.ymodem_client_local)
  (_local_frame:CC.ymodem_client_local_frame)
  : slprop =
  exists* (d:Seq.seq U8.t).
    pts_to frame.yef_ycnf d **
    pure (Seq.length d == 128)

(* ───────────────────────────────────────────────────────────────────────────
   Network I/O carrier (§ pe_network_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

(* The input buffer VARIES (yef_ctrl for a control frame, yef_soh for an SOH
   frame), so we record BOTH the input and the "other" (threaded) buffer, plus a
   concrete `yni_is_soh` discriminator that lets finish_network_io case-split at
   runtime to re-fold io_ready. *)
noeq
type ymodem_client_endpoint_network_io = {
  yni_is_soh         : bool;
  yni_input          : array U8.t;
  yni_input_len      : SZ.t;
  yni_output         : array U8.t;
  yni_input_contents : Ghost.erased TCP.bytes;
  yni_old_output     : Ghost.erased TCP.bytes;
  yni_raw_received   : Ghost.erased TCP.bytes;
  yni_other          : array U8.t;
  yni_other_contents : Ghost.erased TCP.bytes;
}

let ymodem_client_network_io_continuation
  (_i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (frame:ymodem_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_client_state)
  (nio:ymodem_client_endpoint_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) sent **
  pts_to nio.yni_other (Ghost.reveal nio.yni_other_contents) **
  pure (
    nio.yni_output == frame.yef_ack /\
    Seq.length (Ghost.reveal nio.yni_old_output) == 1 /\
    Seq.length (Ghost.reveal nio.yni_input_contents) == SZ.v nio.yni_input_len /\
    (nio.yni_is_soh == true ==>
      (nio.yni_input == frame.yef_soh /\
       nio.yni_other == frame.yef_ctrl /\
       nio.yni_input_len == 133sz /\
       Seq.length (Ghost.reveal nio.yni_other_contents) == 1)) /\
    (nio.yni_is_soh == false ==>
      (nio.yni_input == frame.yef_ctrl /\
       nio.yni_other == frame.yef_soh /\
       nio.yni_input_len == 1sz /\
       Seq.length (Ghost.reveal nio.yni_other_contents) == 133)))

let ymodem_client_network_input (nio:ymodem_client_endpoint_network_io) : array U8.t =
  nio.yni_input

let ymodem_client_network_input_len (nio:ymodem_client_endpoint_network_io) : SZ.t =
  nio.yni_input_len

let ymodem_client_network_output (nio:ymodem_client_endpoint_network_io) : array U8.t =
  nio.yni_output

let ymodem_client_network_output_len (_nio:ymodem_client_endpoint_network_io) : SZ.t =
  1sz

let ymodem_client_network_input_contents (nio:ymodem_client_endpoint_network_io)
  : Ghost.erased TCP.bytes =
  nio.yni_input_contents

let ymodem_client_network_old_output (nio:ymodem_client_endpoint_network_io)
  : Ghost.erased TCP.bytes =
  nio.yni_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_next_action — read the status cell and schedule
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_next_action
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_client_state)
requires
  CC.ymodem_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  ymodem_client_frame_ready i cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CC.ymodem_client_network_frame
  YP.ymodem_client_local
  CC.ymodem_client_local_frame
ensures
  CC.ymodem_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  ymodem_client_action_frame i cfg frame (Ghost.reveal st) action **
  pure (PE.action_not_internal CC.ymodem_client_protocol_implementation action)
{
  unfold (CC.ymodem_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with svs. _;
  let s = Vec.op_Array_Access i.status 0sz;
  fold (CC.ymodem_client_inv i (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  if (s = 0uy) {
    fold (ymodem_client_action_frame i cfg frame (Ghost.reveal st)
      (PE.EndpointLocal (YP.Client_start cfg.ycfg_filename cfg.ycfg_len) ()));
    PE.EndpointLocal (YP.Client_start cfg.ycfg_filename cfg.ycfg_len) ()
  } else if (s = 1uy) {
    let nf : CC.ymodem_client_network_frame = { CC.ycnf_data = frame.yef_ycnf };
    fold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput nf));
    PE.EndpointNeedInput nf
  } else if (s = 2uy) {
    fold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone);
    PE.EndpointDone
  } else {
    fold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed);
    PE.EndpointFailed
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_cancel_action
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_cancel_action
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (st:Ghost.erased YP.ymodem_client_state)
  (action:PE.endpoint_action
    CC.ymodem_client_network_frame
    YP.ymodem_client_local
    CC.ymodem_client_local_frame)
requires ymodem_client_action_frame i cfg frame (Ghost.reveal st) action
ensures ymodem_client_frame_ready i cfg frame (Ghost.reveal st)
{
  match action {
    PE.EndpointNeedInput network_frame -> {
      unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame))
    }
    PE.EndpointLocal ev local_frame -> {
      unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame))
    }
    PE.EndpointDone -> {
      unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointDone)
    }
    PE.EndpointFailed -> {
      unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) PE.EndpointFailed)
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   Framed read helper: assemble the 133-byte SOH frame in yef_soh.
   Writes the SOH lead byte, then reads the 132-byte tail into yef_soh[1..133)
   via a concrete sub-array view (to_mask/sub/from_mask/read/return_sub).
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn fill_soh_tail (ch:TCP.channel) (soh:array U8.t)
requires
  TCP.is_channel ch 'r 's **
  pts_to soh 'sc **
  pure (Seq.length 'sc == 133)
returns _:unit
ensures exists* (r2:TCP.bytes) (sc2:Seq.seq U8.t).
  TCP.is_channel ch r2 's **
  pts_to soh sc2 **
  pure (Seq.length sc2 == 133 /\ Seq.index sc2 0 == 1uy)
{
  pts_to_len soh;
  soh.(0sz) <- 1uy;
  to_mask soh;
  let tail_arr = AC.sub soh 1sz 133;
  from_mask tail_arr;
  let n = TCP.read_full ch tail_arr 132sz;
  to_mask tail_arr;
  AC.return_sub soh;
  from_mask soh;
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_network — peek + framed read of one YMODEM frame
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_prepare_network
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:CC.ymodem_client_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_client_state)
requires
  ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame) **
  ymodem_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:ymodem_client_endpoint_network_io
ensures
  ymodem_client_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (ymodem_client_network_input nio)
    (ymodem_client_network_input_len nio)
    (ymodem_client_network_output nio)
    (ymodem_client_network_output_len nio)
    (Ghost.reveal (ymodem_client_network_input_contents nio))
    (Ghost.reveal (ymodem_client_network_old_output nio)) **
  CC.ymodem_client_network_frame_pre
    network_frame
    (ymodem_client_network_input nio)
    (ymodem_client_network_input_len nio)
    (ymodem_client_network_output nio)
    (ymodem_client_network_output_len nio)
    (Ghost.reveal (ymodem_client_network_input_contents nio))
    (Ghost.reveal (ymodem_client_network_old_output nio)) **
  ymodem_client_network_continuation i cfg frame (Ghost.reveal st) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (ymodem_client_network_input_len nio)
      (Ghost.reveal (ymodem_client_network_old_output nio))
      (ymodem_client_network_output_len nio))
{
  unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  unfold (ymodem_client_frame_ready i cfg frame (Ghost.reveal st));
  with ycnf_d. _;
  unfold (ymodem_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw ctrl_b soh_b ack_b. _;
  (* peek the lead byte into yef_ctrl *)
  let nread = TCP.read_full ch frame.yef_ctrl 1sz;
  with cb1 chunk1. _;
  let lead = frame.yef_ctrl.(0sz);
  if (lead = 1uy) {
    (* SOH: assemble the 133-byte frame; input = yef_soh, other = yef_ctrl *)
    fill_soh_tail ch frame.yef_soh;
    with r2 sc2. _;
    let nio : ymodem_client_endpoint_network_io = {
      yni_is_soh = true;
      yni_input = frame.yef_soh;
      yni_input_len = 133sz;
      yni_output = frame.yef_ack;
      yni_input_contents = Ghost.hide sc2;
      yni_old_output = Ghost.hide ack_b;
      yni_raw_received = Ghost.hide r2;
      yni_other = frame.yef_ctrl;
      yni_other_contents = Ghost.hide cb1;
    };
    (* io continuation *)
    rewrite (TCP.is_channel ch r2 (Ghost.reveal sent))
      as (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) (Ghost.reveal sent));
    rewrite (pts_to frame.yef_ctrl cb1)
      as (pts_to nio.yni_other (Ghost.reveal nio.yni_other_contents));
    fold (ymodem_client_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
    (* network buffers *)
    rewrite (pts_to frame.yef_soh sc2)
      as (pts_to (ymodem_client_network_input nio) (Ghost.reveal (ymodem_client_network_input_contents nio)));
    rewrite (pts_to frame.yef_ack ack_b)
      as (pts_to (ymodem_client_network_output nio) (Ghost.reveal (ymodem_client_network_old_output nio)));
    fold (PE.network_buffers
      (ymodem_client_network_input nio)
      (ymodem_client_network_input_len nio)
      (ymodem_client_network_output nio)
      (ymodem_client_network_output_len nio)
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (Ghost.reveal (ymodem_client_network_old_output nio)));
    (* frame precondition (owns ycnf) *)
    assert (pure (network_frame.CC.ycnf_data == frame.yef_ycnf));
    rewrite (pts_to frame.yef_ycnf ycnf_d)
      as (pts_to network_frame.CC.ycnf_data ycnf_d);
    fold (CC.ymodem_client_network_frame_pre
      network_frame
      (ymodem_client_network_input nio)
      (ymodem_client_network_input_len nio)
      (ymodem_client_network_output nio)
      (ymodem_client_network_output_len nio)
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (Ghost.reveal (ymodem_client_network_old_output nio)));
    fold (ymodem_client_network_continuation i cfg frame (Ghost.reveal st) network_frame);
    assert (pure (CPI.buffers_wf
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (ymodem_client_network_input_len nio)
      (Ghost.reveal (ymodem_client_network_old_output nio))
      (ymodem_client_network_output_len nio)));
    nio
  } else {
    (* control frame: input = yef_ctrl (holds the lead), other = yef_soh *)
    let nio : ymodem_client_endpoint_network_io = {
      yni_is_soh = false;
      yni_input = frame.yef_ctrl;
      yni_input_len = 1sz;
      yni_output = frame.yef_ack;
      yni_input_contents = Ghost.hide cb1;
      yni_old_output = Ghost.hide ack_b;
      yni_raw_received = Ghost.hide (Seq.append raw chunk1);
      yni_other = frame.yef_soh;
      yni_other_contents = Ghost.hide soh_b;
    };
    rewrite (TCP.is_channel ch (Seq.append raw chunk1) (Ghost.reveal sent))
      as (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) (Ghost.reveal sent));
    rewrite (pts_to frame.yef_soh soh_b)
      as (pts_to nio.yni_other (Ghost.reveal nio.yni_other_contents));
    fold (ymodem_client_network_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
    rewrite (pts_to frame.yef_ctrl cb1)
      as (pts_to (ymodem_client_network_input nio) (Ghost.reveal (ymodem_client_network_input_contents nio)));
    rewrite (pts_to frame.yef_ack ack_b)
      as (pts_to (ymodem_client_network_output nio) (Ghost.reveal (ymodem_client_network_old_output nio)));
    fold (PE.network_buffers
      (ymodem_client_network_input nio)
      (ymodem_client_network_input_len nio)
      (ymodem_client_network_output nio)
      (ymodem_client_network_output_len nio)
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (Ghost.reveal (ymodem_client_network_old_output nio)));
    assert (pure (network_frame.CC.ycnf_data == frame.yef_ycnf));
    rewrite (pts_to frame.yef_ycnf ycnf_d)
      as (pts_to network_frame.CC.ycnf_data ycnf_d);
    fold (CC.ymodem_client_network_frame_pre
      network_frame
      (ymodem_client_network_input nio)
      (ymodem_client_network_input_len nio)
      (ymodem_client_network_output nio)
      (ymodem_client_network_output_len nio)
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (Ghost.reveal (ymodem_client_network_old_output nio)));
    fold (ymodem_client_network_continuation i cfg frame (Ghost.reveal st) network_frame);
    assert (pure (CPI.buffers_wf
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (ymodem_client_network_input_len nio)
      (Ghost.reveal (ymodem_client_network_old_output nio))
      (ymodem_client_network_output_len nio)));
    nio
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_action
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_finish_network_action
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (network_frame:CC.ymodem_client_network_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased TCP.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_client_state)
  (st1:Ghost.erased YP.ymodem_client_state)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_client_network_continuation i cfg frame (Ghost.reveal st0) network_frame **
  CC.ymodem_client_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures ymodem_client_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (ymodem_client_network_continuation i cfg frame (Ghost.reveal st0) network_frame);
  unfold (CC.ymodem_client_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with o'. _;
  assert (pure (network_frame.CC.ycnf_data == frame.yef_ycnf));
  rewrite (pts_to network_frame.CC.ycnf_data o')
    as (pts_to frame.yef_ycnf o');
  fold (ymodem_client_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_network_io — write the ACK, case-split, re-establish io_ready
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_finish_network_io
  (i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (frame:ymodem_client_endpoint_frame)
  (nio:ymodem_client_endpoint_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_client_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased YP.ymodem_client_state)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_client_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (ymodem_client_network_input nio) (Ghost.reveal (ymodem_client_network_input_contents nio)) **
  pts_to (ymodem_client_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CC.ymodem_client_protocol_implementation.CPI.pi_system i)
      (Ghost.reveal (ymodem_client_network_input_contents nio))
      (ymodem_client_network_input_len nio)
      (Ghost.reveal (ymodem_client_network_old_output nio))
      (Ghost.reveal out_contents)
      (ymodem_client_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures ymodem_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (ymodem_client_network_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CC.ymodem_client_protocol_implementation.CPI.pi_system i)
    (Ghost.reveal (ymodem_client_network_input_contents nio))
    (ymodem_client_network_input_len nio)
    (Ghost.reveal (ymodem_client_network_old_output nio))
    (Ghost.reveal out_contents)
    (ymodem_client_network_output_len nio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (ymodem_client_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.yni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.yni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.yni_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.yni_raw_received) (Ghost.reveal sent1));
  if (nio.yni_is_soh) {
    (* input = yef_soh, other = yef_ctrl *)
    assert (pure (nio.yni_input == frame.yef_soh));
    assert (pure (nio.yni_other == frame.yef_ctrl));
    rewrite (pts_to (ymodem_client_network_input nio) (Ghost.reveal (ymodem_client_network_input_contents nio)))
      as (pts_to frame.yef_soh (Ghost.reveal (ymodem_client_network_input_contents nio)));
    rewrite (pts_to nio.yni_other (Ghost.reveal nio.yni_other_contents))
      as (pts_to frame.yef_ctrl (Ghost.reveal nio.yni_other_contents));
    rewrite (pts_to (ymodem_client_network_output nio) (Ghost.reveal out_contents))
      as (pts_to frame.yef_ack (Ghost.reveal out_contents));
    fold (ymodem_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
  } else {
    (* input = yef_ctrl, other = yef_soh *)
    assert (pure (nio.yni_input == frame.yef_ctrl));
    assert (pure (nio.yni_other == frame.yef_soh));
    rewrite (pts_to (ymodem_client_network_input nio) (Ghost.reveal (ymodem_client_network_input_contents nio)))
      as (pts_to frame.yef_ctrl (Ghost.reveal (ymodem_client_network_input_contents nio)));
    rewrite (pts_to nio.yni_other (Ghost.reveal nio.yni_other_contents))
      as (pts_to frame.yef_soh (Ghost.reveal nio.yni_other_contents));
    rewrite (pts_to (ymodem_client_network_output nio) (Ghost.reveal out_contents))
      as (pts_to frame.yef_ack (Ghost.reveal out_contents));
    fold (ymodem_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   Local I/O carrier (§ pe_local_io) + continuation + accessors
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type ymodem_client_endpoint_local_io = {
  ylo_output        : array U8.t;
  ylo_old_output    : Ghost.erased TCP.bytes;
  ylo_raw_received  : Ghost.erased TCP.bytes;
  ylo_ctrl_contents : Ghost.erased TCP.bytes;
  ylo_soh_contents  : Ghost.erased TCP.bytes;
}

let ymodem_client_local_io_continuation
  (_i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (frame:ymodem_client_endpoint_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_st:YP.ymodem_client_state)
  (_ev:YP.ymodem_client_local)
  (lio:ymodem_client_endpoint_local_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) sent **
  pts_to frame.yef_ctrl (Ghost.reveal lio.ylo_ctrl_contents) **
  pts_to frame.yef_soh (Ghost.reveal lio.ylo_soh_contents) **
  pure (
    lio.ylo_output == frame.yef_ack /\
    Seq.length (Ghost.reveal lio.ylo_old_output) == 1 /\
    Seq.length (Ghost.reveal lio.ylo_ctrl_contents) == 1 /\
    Seq.length (Ghost.reveal lio.ylo_soh_contents) == 133)

let ymodem_client_local_output (lio:ymodem_client_endpoint_local_io) : array U8.t =
  lio.ylo_output

let ymodem_client_local_output_len (_lio:ymodem_client_endpoint_local_io) : SZ.t =
  1sz

let ymodem_client_local_old_output (lio:ymodem_client_endpoint_local_io)
  : Ghost.erased TCP.bytes =
  lio.ylo_old_output

(* ───────────────────────────────────────────────────────────────────────────
   pe_prepare_local — Client_start (LIVE): output = yef_ack, frame_pre = emp
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_prepare_local
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (ch:TCP.channel)
  (ev:YP.ymodem_client_local)
  (local_frame:CC.ymodem_client_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased YP.ymodem_client_state)
requires
  ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  ymodem_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:ymodem_client_endpoint_local_io
ensures
  ymodem_client_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (ymodem_client_local_output lio)
    (ymodem_client_local_output_len lio)
    (Ghost.reveal (ymodem_client_local_old_output lio)) **
  CC.ymodem_client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (ymodem_client_local_output lio)
    (ymodem_client_local_output_len lio)
    (Ghost.reveal (ymodem_client_local_old_output lio)) **
  ymodem_client_local_continuation i cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (ymodem_client_action_frame i cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  unfold (ymodem_client_frame_ready i cfg frame (Ghost.reveal st));
  with ycnf_d. _;
  unfold (ymodem_client_io_ready i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw ctrl_b soh_b ack_b. _;
  let lio : ymodem_client_endpoint_local_io = {
    ylo_output = frame.yef_ack;
    ylo_old_output = Ghost.hide ack_b;
    ylo_raw_received = Ghost.hide raw;
    ylo_ctrl_contents = Ghost.hide ctrl_b;
    ylo_soh_contents = Ghost.hide soh_b;
  };
  rewrite (TCP.is_channel ch raw (Ghost.reveal sent))
    as (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent));
  rewrite (pts_to frame.yef_ctrl ctrl_b)
    as (pts_to frame.yef_ctrl (Ghost.reveal lio.ylo_ctrl_contents));
  rewrite (pts_to frame.yef_soh soh_b)
    as (pts_to frame.yef_soh (Ghost.reveal lio.ylo_soh_contents));
  fold (ymodem_client_local_io_continuation i ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  rewrite (pts_to frame.yef_ack ack_b)
    as (pts_to (ymodem_client_local_output lio) (Ghost.reveal (ymodem_client_local_old_output lio)));
  fold (PE.local_output_buffer
    (ymodem_client_local_output lio)
    (ymodem_client_local_output_len lio)
    (Ghost.reveal (ymodem_client_local_old_output lio)));
  fold (CC.ymodem_client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (ymodem_client_local_output lio)
    (ymodem_client_local_output_len lio)
    (Ghost.reveal (ymodem_client_local_old_output lio)));
  fold (ymodem_client_local_continuation i cfg frame (Ghost.reveal st) ev local_frame);
  lio
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_action
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_finish_local_action
  (i:CC.ymodem_client_impl)
  (cfg:ymodem_client_config)
  (frame:ymodem_client_endpoint_frame)
  (ev:YP.ymodem_client_local)
  (local_frame:CC.ymodem_client_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_client_state)
  (st1:Ghost.erased YP.ymodem_client_state)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_client_local_continuation i cfg frame (Ghost.reveal st0) ev local_frame **
  CC.ymodem_client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures ymodem_client_frame_ready i cfg frame (Ghost.reveal st1)
{
  unfold (ymodem_client_local_continuation i cfg frame (Ghost.reveal st0) ev local_frame);
  with d. _;
  unfold (CC.ymodem_client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  fold (ymodem_client_frame_ready i cfg frame (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   pe_finish_local_io — write nothing (Client_start produces 0 bytes)
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
fn ymodem_client_finish_local_io
  (i:CC.ymodem_client_impl)
  (ch:TCP.channel)
  (frame:ymodem_client_endpoint_frame)
  (lio:ymodem_client_endpoint_local_io)
  (ev:YP.ymodem_client_local)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased YP.ymodem_client_state)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (st1:Ghost.erased YP.ymodem_client_state)
  (out_contents:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list ymodem_message))
  (local_outputs:Ghost.erased (list unit))
requires
  ymodem_client_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (ymodem_client_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CC.ymodem_client_protocol_implementation.CPI.pi_system i)
      ev
      (Ghost.reveal (ymodem_client_local_old_output lio))
      (Ghost.reveal out_contents)
      (ymodem_client_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures ymodem_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (ymodem_client_local_io_continuation i ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  CPI.lemma_local_process_sent_output_prefix
    (CC.ymodem_client_protocol_implementation.CPI.pi_system i)
    ev
    (Ghost.reveal (ymodem_client_local_old_output lio))
    (Ghost.reveal out_contents)
    (ymodem_client_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (ymodem_client_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.ylo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.ylo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.ylo_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.ylo_raw_received) (Ghost.reveal sent1));
  rewrite (pts_to (ymodem_client_local_output lio) (Ghost.reveal out_contents))
    as (pts_to frame.yef_ack (Ghost.reveal out_contents));
  fold (ymodem_client_io_ready i ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

(* ───────────────────────────────────────────────────────────────────────────
   The 28-field endpoint instance
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let ymodem_client_protocol_endpoint
  : PE.protocol_endpoint
      CC.ymodem_client_impl
      YP.ymodem_client_state
      ymodem_message
      YP.ymodem_client_local
      unit
      CC.ymodem_client_protocol_implementation
  =
  {
    PE.pe_config = ymodem_client_config;
    PE.pe_frame = ymodem_client_endpoint_frame;
    PE.pe_frame_ready = ymodem_client_frame_ready;
    PE.pe_io_ready = ymodem_client_io_ready;
    PE.pe_action_frame = ymodem_client_action_frame;
    PE.pe_network_continuation = ymodem_client_network_continuation;
    PE.pe_local_continuation = ymodem_client_local_continuation;
    PE.pe_next_action = ymodem_client_next_action;
    PE.pe_cancel_action = ymodem_client_cancel_action;
    PE.pe_finish_network_action = ymodem_client_finish_network_action;
    PE.pe_finish_local_action = ymodem_client_finish_local_action;
    PE.pe_network_io = ymodem_client_endpoint_network_io;
    PE.pe_network_io_continuation = ymodem_client_network_io_continuation;
    PE.pe_network_input = ymodem_client_network_input;
    PE.pe_network_input_len = ymodem_client_network_input_len;
    PE.pe_network_output = ymodem_client_network_output;
    PE.pe_network_output_len = ymodem_client_network_output_len;
    PE.pe_network_input_contents = ymodem_client_network_input_contents;
    PE.pe_network_old_output = ymodem_client_network_old_output;
    PE.pe_prepare_network = ymodem_client_prepare_network;
    PE.pe_finish_network_io = ymodem_client_finish_network_io;
    PE.pe_local_io = ymodem_client_endpoint_local_io;
    PE.pe_local_io_continuation = ymodem_client_local_io_continuation;
    PE.pe_local_output = ymodem_client_local_output;
    PE.pe_local_output_len = ymodem_client_local_output_len;
    PE.pe_local_old_output = ymodem_client_local_old_output;
    PE.pe_prepare_local = ymodem_client_prepare_local;
    PE.pe_finish_local_io = ymodem_client_finish_local_io;
  }
