module TLS13.IO

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val channel : Type0
val listener : Type0

val is_channel: channel -> received:B.bytes -> sent:B.bytes -> slprop
val is_listener: listener -> bind_host:B.bytes -> port:U16.t -> slprop

fn connect_tcp (hostname: array U8.t) (hostname_len: SZ.t) (port: U16.t)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns ch: option channel
  ensures pts_to hostname 'hostname_bytes **
          (match ch with
           | Some c -> is_channel c B.empty B.empty
           | None -> emp)

fn listen_tcp (bind_host: array U8.t) (bind_host_len: SZ.t) (port: U16.t)
  requires pts_to bind_host 'bind_host_bytes **
          pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns l: option listener
  ensures pts_to bind_host 'bind_host_bytes **
          (match l with
          | Some listener -> is_listener listener 'bind_host_bytes port
          | None -> emp)

fn accept_tcp (l: listener)
  requires is_listener l 'bind_host 'port
  returns ch: option channel
  ensures is_listener l 'bind_host 'port **
          (match ch with
          | Some c -> is_channel c B.empty B.empty
          | None -> emp)

fn close_listener (l: listener)
  requires is_listener l 'bind_host 'port
  ensures emp

fn read (ch: channel) (out: array U8.t) (max_len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to out 'old **
           pure (B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes chunk.
          is_channel ch (B.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                B.length chunk == SZ.v n /\
                Seq.equal chunk
                  (if SZ.v n <= B.length bytes
                   then Seq.slice bytes 0 (SZ.v n)
                   else B.empty))

fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to buf 'bytes **
           pure (SZ.v len <= B.length 'bytes)
  returns n: SZ.t
  ensures is_channel ch (Ghost.reveal 'received)
            (B.append (Ghost.reveal 'sent)
              (if SZ.v n <= B.length (Ghost.reveal 'bytes)
               then Seq.slice (Ghost.reveal 'bytes) 0 (SZ.v n)
               else B.empty)) **
          pts_to buf 'bytes **
          pure (n == len)

fn close (ch: channel)
  requires is_channel ch 'received 'sent
  ensures emp
