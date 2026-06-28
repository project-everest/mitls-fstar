module Common.ProtocolDriver

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Common.ProtocolImplementation
module CQ = Common.ConnectionStateQuery
module TCP = Common.TCP
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type driver_status (external_action:Type0) =
  | DriverNetworkStep
  | DriverLocalStep
  | DriverNeedsExternal: action:external_action -> driver_status external_action
  | DriverDone
  | DriverFailed

noeq
type driver_result (external_action:Type0) = {
  driver_status: driver_status external_action;
  driver_process_result: option CPI.process_result;
}

noextract
class protocol_driver_io
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (external_action:Type0)
  (protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  (query:CQ.connection_state_query
    impl
    state
    wire_message
    local_event
    local_output
    external_action
    protocol)
  =
{
  pdi_channel:
    Type0;

  pdi_frame:
    Type0;

  pdi_network_io:
    Type0;

  pdi_local_io:
    Type0;

  pdi_ready:
    impl ->
    pdi_channel ->
    pdi_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pdi_network_continuation:
    impl ->
    pdi_channel ->
    pdi_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    pdi_network_io ->
    slprop;

  pdi_network_input:
    pdi_network_io ->
    array U8.t;

  pdi_network_input_len:
    pdi_network_io ->
    SZ.t;

  pdi_network_output:
    pdi_network_io ->
    array U8.t;

  pdi_network_output_len:
    pdi_network_io ->
    SZ.t;

  pdi_network_input_contents:
    pdi_network_io ->
    Ghost.erased TCP.bytes;

  pdi_network_old_output:
    pdi_network_io ->
    Ghost.erased TCP.bytes;

  pdi_prepare_network:
    i:impl ->
    ch:pdi_channel ->
    io_frame:pdi_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt pdi_network_io
        (pdi_ready
          i
          ch
          io_frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun nio ->
          pdi_network_continuation
            i
            ch
            io_frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            nio **
          CQ.network_buffers
            (pdi_network_input nio)
            (pdi_network_input_len nio)
            (pdi_network_output nio)
            (pdi_network_output_len nio)
            (Ghost.reveal (pdi_network_input_contents nio))
            (Ghost.reveal (pdi_network_old_output nio)));

  pdi_finish_network:
    i:impl ->
    ch:pdi_channel ->
    io_frame:pdi_frame ->
    nio:pdi_network_io ->
    result:CPI.process_result ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    received1:Ghost.erased TCP.bytes ->
    sent1:Ghost.erased TCP.bytes ->
    st1:Ghost.erased state ->
    out_contents:Ghost.erased TCP.bytes ->
    consumed:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pdi_network_continuation
          i
          ch
          io_frame
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          nio **
         pts_to
          (pdi_network_input nio)
          (Ghost.reveal (pdi_network_input_contents nio)) **
         pts_to
          (pdi_network_output nio)
          (Ghost.reveal out_contents) **
         pure (
          CPI.network_process_correct
            (protocol.CPI.pi_system i)
            (Ghost.reveal (pdi_network_input_contents nio))
            (pdi_network_input_len nio)
            (Ghost.reveal (pdi_network_old_output nio))
            (Ghost.reveal out_contents)
            (pdi_network_output_len nio)
            (Ghost.reveal received0)
            (Ghost.reveal sent0)
            (Ghost.reveal st0)
            result
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1)
            (Ghost.reveal consumed)
            (Ghost.reveal wire_outputs)
            (Ghost.reveal local_outputs)))
        (fun _ ->
          pdi_ready
            i
            ch
            io_frame
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1));

  pdi_local_continuation:
    impl ->
    pdi_channel ->
    pdi_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    local_event ->
    pdi_local_io ->
    slprop;

  pdi_local_output:
    pdi_local_io ->
    array U8.t;

  pdi_local_output_len:
    pdi_local_io ->
    SZ.t;

  pdi_local_old_output:
    pdi_local_io ->
    Ghost.erased TCP.bytes;

  pdi_prepare_local:
    i:impl ->
    ch:pdi_channel ->
    io_frame:pdi_frame ->
    ev:local_event ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt pdi_local_io
        (pdi_ready
          i
          ch
          io_frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun lio ->
          pdi_local_continuation
            i
            ch
            io_frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            ev
            lio **
          CQ.local_output_buffer
            (pdi_local_output lio)
            (pdi_local_output_len lio)
            (Ghost.reveal (pdi_local_old_output lio)));

  pdi_finish_local:
    i:impl ->
    ch:pdi_channel ->
    io_frame:pdi_frame ->
    lio:pdi_local_io ->
    ev:local_event ->
    result:CPI.process_result ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    received1:Ghost.erased TCP.bytes ->
    sent1:Ghost.erased TCP.bytes ->
    st1:Ghost.erased state ->
    out_contents:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pdi_local_continuation
          i
          ch
          io_frame
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          ev
          lio **
         pts_to
          (pdi_local_output lio)
          (Ghost.reveal out_contents) **
         pure (
          CPI.local_process_correct
            (protocol.CPI.pi_system i)
            ev
            (Ghost.reveal (pdi_local_old_output lio))
            (Ghost.reveal out_contents)
            (pdi_local_output_len lio)
            (Ghost.reveal received0)
            (Ghost.reveal sent0)
            (Ghost.reveal st0)
            result
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1)
            (Ghost.reveal wire_outputs)
            (Ghost.reveal local_outputs)))
        (fun _ ->
          pdi_ready
            i
            ch
            io_frame
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1));
}

fn drive_once
  #impl #state #wire_message #local_event #local_output #external_action
  (#protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  (#query:CQ.connection_state_query
    impl
    state
    wire_message
    local_event
    local_output
    external_action
    protocol)
  (#io:protocol_driver_io
    impl
    state
    wire_message
    local_event
    local_output
    external_action
    protocol
    query)
  (i:impl)
  (cfg:query.CQ.csq_config)
  (query_frame:query.CQ.csq_frame)
  (ch:io.pdi_channel)
  (io_frame:io.pdi_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased state)
requires
  protocol.CPI.pi_invariant
    i
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  query.CQ.csq_frame_ready
    i
    cfg
    query_frame
    (Ghost.reveal st) **
  io.pdi_ready
    i
    ch
    io_frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
returns result:driver_result external_action
ensures
  (match result.driver_status with
  | DriverNetworkStep
  | DriverLocalStep ->
    exists* (received1:Ghost.erased TCP.bytes)
            (sent1:Ghost.erased TCP.bytes)
            (st1:Ghost.erased state).
      protocol.CPI.pi_invariant
        i
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      query.CQ.csq_frame_ready
        i
        cfg
        query_frame
        (Ghost.reveal st1) **
      io.pdi_ready
        i
        ch
        io_frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
  | DriverNeedsExternal _
  | DriverDone
  | DriverFailed ->
      protocol.CPI.pi_invariant
        i
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st) **
      query.CQ.csq_frame_ready
        i
        cfg
        query_frame
        (Ghost.reveal st) **
      io.pdi_ready
        i
        ch
        io_frame
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st))
{
  let next_action = query.CQ.csq_next_action;
  let action =
    next_action
      i
      cfg
      query_frame
      received
      sent
      st;
  match action {
    CQ.NextNeedInput network_frame -> {
      let prepare_network_io = io.pdi_prepare_network;
      let nio = prepare_network_io i ch io_frame received sent st;
      let prepare_network_query = query.CQ.csq_prepare_network;
      prepare_network_query
        i
        cfg
        query_frame
        network_frame
        (io.pdi_network_input nio)
        (io.pdi_network_input_len nio)
        (io.pdi_network_output nio)
        (io.pdi_network_output_len nio)
        st
        (io.pdi_network_input_contents nio)
        (io.pdi_network_old_output nio);
      let process_network = protocol.CPI.pi_process_network;
      let process_result =
        process_network
          i
          network_frame
          (io.pdi_network_input nio)
          (io.pdi_network_input_len nio)
          (io.pdi_network_output nio)
          (io.pdi_network_output_len nio)
          received
          sent
          st
          (io.pdi_network_input_contents nio)
          (io.pdi_network_old_output nio);
      with received1 sent1 st1 out_contents consumed wire_outputs local_outputs.
      assert (
        protocol.CPI.pi_invariant
          i
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (io.pdi_network_input_contents nio))
          (io.pdi_network_input_len nio)
          (Ghost.reveal (io.pdi_network_old_output nio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          consumed
          wire_outputs
          local_outputs);
      let out_contentse = Ghost.hide out_contents;
      let consumede = Ghost.hide consumed;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      let finish_network_query = query.CQ.csq_finish_network;
      assert (pure ((Ghost.reveal out_contentse) == out_contents));
      assert (pure ((Ghost.reveal consumede) == consumed));
      assert (pure ((Ghost.reveal wire_outputse) == wire_outputs));
      assert (pure ((Ghost.reveal local_outputse) == local_outputs));
      rewrite
        (protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (io.pdi_network_input_contents nio))
          (io.pdi_network_input_len nio)
          (Ghost.reveal (io.pdi_network_old_output nio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          consumed
          wire_outputs
          local_outputs)
        as
        (protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (io.pdi_network_input_contents nio))
          (io.pdi_network_input_len nio)
          (Ghost.reveal (io.pdi_network_old_output nio))
          (Ghost.reveal out_contentse)
          (Ghost.reveal st)
          (Ghost.reveal st1)
          (Ghost.reveal consumede)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      finish_network_query
        i
        cfg
        query_frame
        network_frame
        process_result
        (io.pdi_network_input_contents nio)
        (io.pdi_network_input_len nio)
        (io.pdi_network_old_output nio)
        out_contentse
        st
        st1
        consumede
        wire_outputse
        local_outputse;
      let finish_network_io = io.pdi_finish_network;
      finish_network_io
        i
        ch
        io_frame
        nio
        process_result
        received
        sent
        st
        received1
        sent1
        st1
        out_contentse
        consumede
        wire_outputse
        local_outputse;
      {
        driver_status = DriverNetworkStep;
        driver_process_result = Some process_result;
      }
    }
    CQ.NextLocal ev local_frame -> {
      let prepare_local_io = io.pdi_prepare_local;
      let lio = prepare_local_io i ch io_frame ev received sent st;
      let prepare_local_query = query.CQ.csq_prepare_local;
      prepare_local_query
        i
        cfg
        query_frame
        ev
        local_frame
        (io.pdi_local_output lio)
        (io.pdi_local_output_len lio)
        st
        (io.pdi_local_old_output lio);
      let process_local = protocol.CPI.pi_process_local;
      let process_result =
        process_local
          i
          ev
          local_frame
          (io.pdi_local_output lio)
          (io.pdi_local_output_len lio)
          received
          sent
          st
          (io.pdi_local_old_output lio);
      with received1 sent1 st1 out_contents wire_outputs local_outputs.
      assert (
        protocol.CPI.pi_invariant
          i
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (io.pdi_local_old_output lio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs);
      let out_contentse = Ghost.hide out_contents;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      let finish_local_query = query.CQ.csq_finish_local;
      assert (pure ((Ghost.reveal out_contentse) == out_contents));
      assert (pure ((Ghost.reveal wire_outputse) == wire_outputs));
      assert (pure ((Ghost.reveal local_outputse) == local_outputs));
      rewrite
        (protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (io.pdi_local_old_output lio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs)
        as
        (protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (io.pdi_local_old_output lio))
          (Ghost.reveal out_contentse)
          (Ghost.reveal st)
          (Ghost.reveal st1)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      finish_local_query
        i
        cfg
        query_frame
        ev
        local_frame
        process_result
        (io.pdi_local_old_output lio)
        out_contentse
        st
        st1
        wire_outputse
        local_outputse;
      let finish_local_io = io.pdi_finish_local;
      finish_local_io
        i
        ch
        io_frame
        lio
        ev
        process_result
        received
        sent
        st
        received1
        sent1
        st1
        out_contentse
        wire_outputse
        local_outputse;
      {
        driver_status = DriverLocalStep;
        driver_process_result = Some process_result;
      }
    }
    CQ.NextExternal ext -> {
      let cancel_action = query.CQ.csq_cancel_action;
      cancel_action i cfg query_frame st (CQ.NextExternal ext);
      {
        driver_status = DriverNeedsExternal ext;
        driver_process_result = None;
      }
    }
    CQ.NextDone -> {
      let cancel_action = query.CQ.csq_cancel_action;
      cancel_action i cfg query_frame st CQ.NextDone;
      {
        driver_status = DriverDone;
        driver_process_result = None;
      }
    }
    CQ.NextFailed -> {
      let cancel_action = query.CQ.csq_cancel_action;
      cancel_action i cfg query_frame st CQ.NextFailed;
      {
        driver_status = DriverFailed;
        driver_process_result = None;
      }
    }
  }
}
