module TLS13.IO

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val channel : Type0
val is_channel: channel -> slprop

fn read (ch: channel) (out: array U8.t) (max_len: SZ.t)
  requires is_channel ch ** pts_to out 'old ** pure (B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes. is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\ SZ.v n <= SZ.v max_len)

fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch ** pts_to buf 'bytes ** pure (B.length 'bytes == SZ.v len)
  returns n: SZ.t
  ensures is_channel ch ** pts_to buf 'bytes ** pure (SZ.v n <= SZ.v len)

