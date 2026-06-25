module Common.ProtocolImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module P = Common.Protocol
module TCP = Common.TCP

type parsed_messages (wire_message:Type0) =
  option (list wire_message & TCP.bytes)

noextract
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

  pi_invariant_correct:
    state ->
    TCP.history ->
    GTot prop;

  pi_network_pre:
    impl ->
    network_args ->
    slprop;

  pi_network_post:
    impl ->
    network_args ->
    network_result ->
    slprop;

  pi_local_pre:
    impl ->
    local_args ->
    slprop;

  pi_local_post:
    impl ->
    local_args ->
    local_result ->
    slprop;

  pi_network_signature:
    impl ->
    network_args ->
    GTot Type0;

  pi_local_signature:
    impl ->
    local_args ->
    GTot Type0;
}
