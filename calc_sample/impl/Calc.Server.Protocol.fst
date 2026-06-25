module Calc.Server.Protocol

#lang-pulse

open Pulse.Lib.Pervasives

module CP = Common.Protocol
module CPI = Common.ProtocolImplementation
module TCP = Common.TCP
module CalcP = Calc.Protocol

open Calc.Log
open Calc.Impl.Types

noextract
let calc_server_represents
  (srv:server_state)
  (log:calc_log)
  (tcp:TCP.history)
  : slprop =
  server_exactly srv log **
  pure (
    CalcP.calc_state_valid log /\
    CalcP.calc_transport_matches tcp log
  )

noextract
let calc_server_protocol_implementation
  : CPI.protocol_implementation
      server_state
      calc_log
      CalcP.calc_wire_message
      CalcP.calc_event
  =
  {
    CPI.pi_protocol = CalcP.calc_protocol;
    CPI.pi_represents = calc_server_represents;
  }
