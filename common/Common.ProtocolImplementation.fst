module Common.ProtocolImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module P = Common.Protocol
module TCP = Common.TCP

noextract
class protocol_implementation
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (event:Type0)
  =
{
  pi_protocol:
    P.state_machine_protocol state wire_message event;

  pi_represents:
    impl ->
    state ->
    TCP.history ->
    slprop;
}

