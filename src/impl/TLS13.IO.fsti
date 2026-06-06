module TLS13.IO

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val channel : Type0
val is_channel: channel -> slprop

fn connect_tcp (hostname: array U8.t) (hostname_len: SZ.t) (port: U16.t)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns ch: option channel
  ensures pts_to hostname 'hostname_bytes **
          (match ch with
           | Some c -> is_channel c
           | None -> emp)

fn read (ch: channel) (out: array U8.t) (max_len: SZ.t)
  requires is_channel ch ** pts_to out 'old ** pure (B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes. is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\ SZ.v n <= SZ.v max_len)

fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch ** pts_to buf 'bytes ** pure (SZ.v len <= B.length 'bytes)
  returns n: SZ.t
  ensures is_channel ch ** pts_to buf 'bytes ** pure (SZ.v n <= SZ.v len)

fn close (ch: channel)
  requires is_channel ch
  ensures emp
