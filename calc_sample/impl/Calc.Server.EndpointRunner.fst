module Calc.Server.EndpointRunner

#lang-pulse

open Pulse.Lib.Pervasives

module Socket = Calc.Server.Socket
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP

fn run_channel_endpoint
  (ch:TCP.channel)
  (fuel:SZ.t)
requires TCP.is_channel ch (Seq.create 0 0uy) (Seq.create 0 0uy)
ensures emp
{
  Socket.run_channel ch fuel
}
