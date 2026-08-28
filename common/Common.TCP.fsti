module Common.TCP

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

unfold type bytes = Seq.seq U8.t

noextract
noeq
type history = {
  tcp_received: bytes;
  tcp_sent: bytes;
}

noextract let empty_history : history =
  {
    tcp_received = Seq.empty;
    tcp_sent = Seq.empty;
  }

noextract let append_received (h:history) (chunk:bytes) : history =
  { h with tcp_received = Seq.append h.tcp_received chunk }

noextract let append_sent (h:history) (chunk:bytes) : history =
  { h with tcp_sent = Seq.append h.tcp_sent chunk }

noextract let history_equal (h0 h1:history) : prop =
  Seq.equal h0.tcp_received h1.tcp_received /\
  Seq.equal h0.tcp_sent h1.tcp_sent

noextract let bytes_extends (old:bytes) (next:bytes) : prop =
  Seq.length old <= Seq.length next /\
  Seq.equal old (Seq.slice next 0 (Seq.length old))

noextract let history_extends (old next:history) : prop =
  bytes_extends old.tcp_received next.tcp_received /\
  bytes_extends old.tcp_sent next.tcp_sent

noextract let bytes_exact_prefix (prefix full:bytes) : prop =
  Seq.length prefix <= Seq.length full /\
  Seq.equal prefix (Seq.slice full 0 (Seq.length prefix))

val channel : Type0
val listener : Type0

val is_channel: channel -> received:bytes -> sent:bytes -> slprop
val is_listener: listener -> bind_host:bytes -> port:U16.t -> slprop

fn connect_tcp (hostname: array U8.t) (hostname_len: SZ.t) (port: U16.t)
  requires pts_to hostname 'hostname_bytes **
           pure (Seq.length 'hostname_bytes == SZ.v hostname_len)
  returns ch: option channel
  ensures pts_to hostname 'hostname_bytes **
          (match ch with
           | Some c -> is_channel c (Seq.create 0 0uy) (Seq.create 0 0uy)
           | None -> emp)

fn listen_tcp (bind_host: array U8.t) (bind_host_len: SZ.t) (port: U16.t)
  requires pts_to bind_host 'bind_host_bytes **
          pure (Seq.length 'bind_host_bytes == SZ.v bind_host_len)
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
          | Some c -> is_channel c (Seq.create 0 0uy) (Seq.create 0 0uy)
          | None -> emp)

fn close_listener (l: listener)
  requires is_listener l 'bind_host 'port
  ensures emp

fn read (ch: channel) (out: array U8.t) (max_len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to out 'old **
           pure (Seq.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes chunk.
          is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
          pts_to out bytes **
          pure (Seq.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                Seq.length chunk == SZ.v n /\
                Seq.equal chunk
                  (if SZ.v n <= Seq.length bytes
                   then Seq.slice bytes 0 (SZ.v n)
                   else Seq.create 0 0uy))

fn read_full (ch: channel) (out: array U8.t) (len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to out 'old **
           pure (Seq.length 'old == SZ.v len)
  returns n: SZ.t
  ensures exists* bytes chunk.
          is_channel ch (Seq.append (Ghost.reveal 'received) chunk) (Ghost.reveal 'sent) **
          pts_to out bytes **
          pure (Seq.length bytes == SZ.v len /\
                n == len /\
                Seq.length chunk == SZ.v len /\
                Seq.equal chunk (Seq.slice bytes 0 (SZ.v len)))

fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch 'received 'sent **
           pts_to buf 'bytes **
           pure (SZ.v len <= Seq.length 'bytes)
  returns n: SZ.t
  ensures is_channel ch (Ghost.reveal 'received)
            (Seq.append (Ghost.reveal 'sent)
              (if SZ.v n <= Seq.length (Ghost.reveal 'bytes)
               then Seq.slice (Ghost.reveal 'bytes) 0 (SZ.v n)
               else Seq.create 0 0uy)) **
          pts_to buf 'bytes **
          pure (n == len)

fn close (ch: channel)
  requires is_channel ch 'received 'sent
  ensures emp
