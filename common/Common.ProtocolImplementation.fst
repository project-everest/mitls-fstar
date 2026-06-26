module Common.ProtocolImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module P = Common.Protocol
module TCP = Common.TCP

type parsed_messages (wire_message:Type0) =
  option (list wire_message & TCP.bytes)

let protocol_state_transport
  (#state:Type0)
  (#wire_message:Type0)
  (#event:Type0)
  (protocol:P.state_machine_protocol state wire_message event)
  (tcp_history_matches:TCP.history -> state -> GTot prop)
  (tcp:TCP.history)
  (st:state)
  : GTot prop =
  tcp_history_matches tcp st /\
  protocol.P.sm_wire_format.P.wf_history_matches
    (protocol.P.sm_processed_history st)
    (protocol.P.sm_wire_log st) /\
  protocol.P.sm_transport_matches
    (protocol.P.sm_processed_history st)
    st

let protocol_network_step
  (#state:Type0)
  (#wire_message:Type0)
  (#event:Type0)
  (protocol:P.state_machine_protocol state wire_message event)
  (tcp_history_matches:TCP.history -> state -> GTot prop)
  (st0:state)
  (tcp0:TCP.history)
  (st1:state)
  (tcp1:TCP.history)
  : GTot prop =
  protocol_state_transport protocol tcp_history_matches tcp0 st0 /\
  protocol_state_transport protocol tcp_history_matches tcp1 st1

let protocol_local_step
  (#state:Type0)
  (#wire_message:Type0)
  (#event:Type0)
  (protocol:P.state_machine_protocol state wire_message event)
  (tcp_history_matches:TCP.history -> state -> GTot prop)
  (st0:state)
  (tcp0:TCP.history)
  (st1:state)
  (tcp1:TCP.history)
  : GTot prop =
  protocol_state_transport protocol tcp_history_matches tcp0 st0 /\
  protocol_state_transport protocol tcp_history_matches tcp1 st1

noextract
(**
  A protocol implementation owns one canonical shape of process specification:
  the argument record determines the old protocol state and TCP history; the
  precondition owns the representation invariant plus any call-frame resources;
  the postcondition returns a new representation invariant indexed by a new TCP
  history, proves both old and new TCP histories match the protocol wire log,
  and records the instance-specific state-machine effect of the operation.
**)
class protocol_implementation
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (event:Type0)
  (network_args:Type0)
  (network_result:Type0)
  (local_args:Type0)
  (local_result:Type0)
  =
{
  pi_protocol:
    P.state_machine_protocol state wire_message event;

  pi_parse_network:
    TCP.bytes -> GTot (parsed_messages wire_message);

  pi_serialize_network:
    wire_message -> GTot (option TCP.bytes);

  pi_serialized_network:
    wire_message ->
    TCP.bytes ->
    GTot prop;

  pi_parse_network_correct:
    bytes:TCP.bytes ->
      Lemma
        (ensures
          (match pi_parse_network bytes with
          | None -> True
          | Some (msgs, residual) ->
            pi_protocol.P.sm_wire_format.P.wf_stream_matches
              P.NetworkReceived
              bytes
              msgs
              residual));

  pi_serialize_network_correct:
    msg:wire_message ->
      Lemma
        (ensures
          (match pi_serialize_network msg with
          | None -> True
          | Some bytes ->
            pi_serialized_network msg bytes));

  pi_tcp_channel:
    impl ->
    TCP.history ->
    slprop;

  pi_ghost_log:
    impl ->
    state ->
    slprop;

  pi_runtime_resources:
    impl ->
    state ->
    TCP.history ->
    slprop;

  pi_invariant:
    impl ->
    state ->
    TCP.history ->
    slprop;

  pi_tcp_history_matches:
    TCP.history ->
    state ->
    GTot prop;

  pi_network_args_state:
    network_args -> GTot state;

  pi_network_args_tcp:
    network_args -> GTot TCP.history;

  pi_local_args_state:
    local_args -> GTot state;

  pi_local_args_tcp:
    local_args -> GTot TCP.history;

  pi_network_frame:
    impl ->
    network_args ->
    slprop;

  pi_network_extra_post:
    impl ->
    network_args ->
    network_result ->
    state ->
    TCP.history ->
    slprop;

  pi_network_effect:
    network_args ->
    network_result ->
    state ->
    TCP.history ->
    state ->
    TCP.history ->
    GTot prop;

  pi_local_frame:
    impl ->
    local_args ->
    slprop;

  pi_local_extra_post:
    impl ->
    local_args ->
    local_result ->
    state ->
    TCP.history ->
    slprop;

  pi_local_effect:
    local_args ->
    local_result ->
    state ->
    TCP.history ->
    state ->
    TCP.history ->
    GTot prop;

  pi_process_network:
    i:impl ->
    args:network_args ->
      stt network_result
        (pi_invariant
          i
          (pi_network_args_state args)
          (pi_network_args_tcp args) **
         pi_network_frame i args **
         pure (protocol_state_transport
          pi_protocol
          pi_tcp_history_matches
          (pi_network_args_tcp args)
          (pi_network_args_state args)))
        (fun result ->
          exists* (st1: Ghost.erased state) (tcp1: Ghost.erased TCP.history).
            pi_invariant i (Ghost.reveal st1) (Ghost.reveal tcp1) **
            pi_network_extra_post
              i
              args
              result
              (Ghost.reveal st1)
              (Ghost.reveal tcp1) **
            pure (
              protocol_network_step
                pi_protocol
                pi_tcp_history_matches
                (pi_network_args_state args)
                (pi_network_args_tcp args)
                (Ghost.reveal st1)
                (Ghost.reveal tcp1) /\
              pi_network_effect
                args
                result
                (pi_network_args_state args)
                (pi_network_args_tcp args)
                (Ghost.reveal st1)
                (Ghost.reveal tcp1)));

  pi_process_local:
    i:impl ->
    args:local_args ->
      stt local_result
        (pi_invariant
          i
          (pi_local_args_state args)
          (pi_local_args_tcp args) **
         pi_local_frame i args **
         pure (protocol_state_transport
          pi_protocol
          pi_tcp_history_matches
          (pi_local_args_tcp args)
          (pi_local_args_state args)))
        (fun result ->
          exists* (st1: Ghost.erased state) (tcp1: Ghost.erased TCP.history).
            pi_invariant i (Ghost.reveal st1) (Ghost.reveal tcp1) **
            pi_local_extra_post
              i
              args
              result
              (Ghost.reveal st1)
              (Ghost.reveal tcp1) **
            pure (
              protocol_local_step
                pi_protocol
                pi_tcp_history_matches
                (pi_local_args_state args)
                (pi_local_args_tcp args)
                (Ghost.reveal st1)
                (Ghost.reveal tcp1) /\
              pi_local_effect
                args
                result
                (pi_local_args_state args)
                (pi_local_args_tcp args)
                (Ghost.reveal st1)
                (Ghost.reveal tcp1)));
}
