module Calc.Server.EndpointRunner

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Common.ProtocolImplementation
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec
module MR = Pulse.Lib.MonotonicGhostRef

module CalcCP = Calc.Server.CanonicalProtocol
module CalcP = Calc.Protocol

open Calc.Log
open Calc.Impl.Types

noextract
let empty_bytes : TCP.bytes = Seq.empty

fn free_canonical_server
  (srv:CalcCP.canonical_server)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#log:erased calc_log)
requires
  CalcCP.canonical_server_exactly srv received sent log **
  pure (
    Vec.is_full_vec srv.CalcCP.canonical_server_state.stack /\
    Vec.is_full_vec srv.CalcCP.canonical_server_state.size)
ensures emp
{
  unfold (CalcCP.canonical_server_exactly srv received sent log);
  unfold (server_exactly srv.CalcCP.canonical_server_state log);
  with stack_bytes size_seq. _;
  Vec.free srv.CalcCP.canonical_server_state.stack;
  Vec.free srv.CalcCP.canonical_server_state.size;
  drop_ (MR.pts_to srv.CalcCP.canonical_server_state.ghost_log #1.0R log);
  drop_ (MR.pts_to srv.CalcCP.canonical_server_progress #1.0R log)
}

fn rec run_endpoint_loop
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (fuel:SZ.t)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#raw_received:erased TCP.bytes)
  (#log:erased calc_log)
requires
  CalcCP.canonical_server_exactly srv received sent log **
  TCP.is_channel ch raw_received sent **
  Vec.pts_to frame.CalcCP.calc_network_req 'req_bytes **
  Vec.pts_to frame.CalcCP.calc_network_resp 'resp_bytes **
  pure (
    Seq.length 'req_bytes == 5 /\
    Seq.length 'resp_bytes == 5 /\
    Vec.length frame.CalcCP.calc_network_req == 5 /\
    Vec.length frame.CalcCP.calc_network_resp == 5 /\
    Vec.is_full_vec frame.CalcCP.calc_network_req /\
    Vec.is_full_vec frame.CalcCP.calc_network_resp /\
    Vec.is_full_vec srv.CalcCP.canonical_server_state.stack /\
    Vec.is_full_vec srv.CalcCP.canonical_server_state.size)
ensures
  exists* (received1:Ghost.erased TCP.bytes)
          (sent1:Ghost.erased TCP.bytes)
          (raw_received1:Ghost.erased TCP.bytes)
          (log1:Ghost.erased calc_log)
          (req_bytes1:TCP.bytes)
          (resp_bytes1:TCP.bytes).
    CalcCP.canonical_server_exactly
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1) **
    TCP.is_channel ch (Ghost.reveal raw_received1) (Ghost.reveal sent1) **
    Vec.pts_to frame.CalcCP.calc_network_req req_bytes1 **
    Vec.pts_to frame.CalcCP.calc_network_resp resp_bytes1 **
    pure (
      Seq.length req_bytes1 == 5 /\
      Seq.length resp_bytes1 == 5 /\
      Vec.length frame.CalcCP.calc_network_req == 5 /\
      Vec.length frame.CalcCP.calc_network_resp == 5 /\
      Vec.is_full_vec frame.CalcCP.calc_network_req /\
      Vec.is_full_vec frame.CalcCP.calc_network_resp /\
      Vec.is_full_vec srv.CalcCP.canonical_server_state.stack /\
      Vec.is_full_vec srv.CalcCP.canonical_server_state.size)
decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    ()
  } else {
    assert (pure (0 < SZ.v fuel));
    Vec.to_array_pts_to frame.CalcCP.calc_network_req;
    let nread = TCP.read_full ch (Vec.vec_to_array frame.CalcCP.calc_network_req) 5sz;
    with req_bytes_after chunk. _;
    assert (pure (nread == 5sz));
    assert (pure (Seq.length req_bytes_after == 5));
    assert (pure (Seq.length chunk == 5));
    let raw_after = Ghost.hide (Seq.append (Ghost.reveal raw_received) chunk);
    assert (pure (Ghost.reveal raw_after == Seq.append (Ghost.reveal raw_received) chunk));
    rewrite
      (TCP.is_channel
        ch
        (Seq.append (Ghost.reveal raw_received) chunk)
        (Ghost.reveal sent))
      as
      (TCP.is_channel ch (Ghost.reveal raw_after) (Ghost.reveal sent));
    Vec.to_array_pts_to frame.CalcCP.calc_network_resp;
    let inpute = Ghost.hide req_bytes_after;
    let old_oute = Ghost.hide (Ghost.reveal 'resp_bytes);
    assert (pure (Ghost.reveal inpute == req_bytes_after));
    assert (pure (Ghost.reveal old_oute == Ghost.reveal 'resp_bytes));
    fold (CalcCP.calc_network_frame_pre
      frame
      (Vec.vec_to_array frame.CalcCP.calc_network_req)
      5sz
      (Vec.vec_to_array frame.CalcCP.calc_network_resp)
      5sz
      (Ghost.reveal inpute)
      (Ghost.reveal old_oute));
    let result =
      CalcCP.calc_process_network
        srv
        frame
        (Vec.vec_to_array frame.CalcCP.calc_network_req)
        5sz
        (Vec.vec_to_array frame.CalcCP.calc_network_resp)
        5sz
        received
        sent
        log
        inpute
        old_oute;
    with received1 sent1 log1 out_contents consumed wire_outputs local_outputs. _;
    unfold (CalcCP.calc_network_frame_post
      frame
      result
      (Ghost.reveal inpute)
      5sz
      (Ghost.reveal old_oute)
      out_contents
      (Ghost.reveal log)
      (Ghost.reveal log1)
      consumed
      wire_outputs
      local_outputs);
    CPI.lemma_network_process_sent_output_prefix
      (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
      (Ghost.reveal inpute)
      5sz
      (Ghost.reveal old_oute)
      out_contents
      5sz
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      consumed
      wire_outputs
      local_outputs;
    assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length out_contents));
    let nwritten =
      TCP.write
        ch
        (Vec.vec_to_array frame.CalcCP.calc_network_resp)
        result.CPI.process_produced_len;
    assert (pure (nwritten == result.CPI.process_produced_len));
    rewrite
      (TCP.is_channel
        ch
        (Ghost.reveal raw_after)
        (Seq.append
          (Ghost.reveal sent)
          (if SZ.v nwritten <= Seq.length out_contents
           then Seq.slice out_contents 0 (SZ.v nwritten)
           else Seq.create 0 0uy)))
      as
      (TCP.is_channel
        ch
        (Ghost.reveal raw_after)
        (Seq.append
          (Ghost.reveal sent)
          (if SZ.v result.CPI.process_produced_len <= Seq.length out_contents
           then Seq.slice out_contents 0 (SZ.v result.CPI.process_produced_len)
           else Seq.create 0 0uy)));
    rewrite
      (TCP.is_channel
        ch
        (Ghost.reveal raw_after)
        (Seq.append
          (Ghost.reveal sent)
          (if SZ.v result.CPI.process_produced_len <= Seq.length out_contents
           then Seq.slice out_contents 0 (SZ.v result.CPI.process_produced_len)
           else Seq.create 0 0uy)))
      as
      (TCP.is_channel ch (Ghost.reveal raw_after) (Ghost.reveal sent1));
    assert (pure (Seq.length out_contents == 5));
    Vec.to_vec_pts_to frame.CalcCP.calc_network_req;
    Vec.to_vec_pts_to frame.CalcCP.calc_network_resp;
    match result.CPI.process_status {
      CPI.StepOk -> {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        run_endpoint_loop
          srv
          ch
          frame
          next_fuel
          #received1
          #sent1
          #raw_after
          #log1
      }
      CPI.ParseFailed -> {
        ()
      }
      CPI.NeedMoreInput -> {
        ()
      }
      CPI.DecodeError -> {
        ()
      }
      CPI.IllegalTransition -> {
        ()
      }
      CPI.OutputBufferTooSmall -> {
        ()
      }
      CPI.ConnectionFailed -> {
        ()
      }
    }
  }
}

fn run_channel_endpoint
  (ch:TCP.channel)
  (fuel:SZ.t)
requires TCP.is_channel ch empty_bytes empty_bytes
ensures emp
{
  let srv = CalcCP.new_canonical_server ();
  let req = Vec.alloc 0uy 5sz;
  let resp = Vec.alloc 0uy 5sz;
  let frame : CalcCP.calc_network_frame = {
    CalcCP.calc_network_req = req;
    CalcCP.calc_network_resp = resp;
  };
  assert (pure (frame.CalcCP.calc_network_req == req));
  assert (pure (frame.CalcCP.calc_network_resp == resp));
  rewrite (Vec.pts_to req (Seq.create 5 0uy)) as
    (Vec.pts_to frame.CalcCP.calc_network_req (Seq.create 5 0uy));
  rewrite (Vec.pts_to resp (Seq.create 5 0uy)) as
    (Vec.pts_to frame.CalcCP.calc_network_resp (Seq.create 5 0uy));
  run_endpoint_loop
    srv
    ch
    frame
    fuel
    #empty_bytes
    #empty_bytes
    #empty_bytes
    #initial_log;
  with received1 sent1 raw_received1 log1 req_bytes1 resp_bytes1. _;
  TCP.close ch;
  Vec.free frame.CalcCP.calc_network_req;
  Vec.free frame.CalcCP.calc_network_resp;
  free_canonical_server srv #received1 #sent1 #log1
}
