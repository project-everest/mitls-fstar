module TLS13.Connection.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module IO = TLS13.IO
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

val connection : Type0
val is_connection: connection -> slprop

fn client_new
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (#trust_store: X.trust_store)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns c: connection
  ensures pts_to hostname 'hostname_bytes **
          is_connection c

fn client_free (c: connection)
  requires is_connection c
  ensures emp

fn client_connect (c: connection) (ch: IO.channel)
  requires is_connection c ** IO.is_channel ch
  returns ok: bool
  ensures is_connection c ** IO.is_channel ch

fn client_write (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure (B.length 'bytes == SZ.v len)
  returns written: SZ.t
  ensures is_connection c **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (SZ.v written <= SZ.v len)

fn client_write_all (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure (B.length 'bytes == SZ.v len)
  returns ok: bool
  ensures is_connection c **
          IO.is_channel ch **
          pts_to buf 'bytes

fn client_read (c: connection) (ch: IO.channel) (out: array U8.t) (max_len: SZ.t)
  requires is_connection c **
           IO.is_channel ch **
           pts_to out 'old **
           pure (B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* bytes.
          is_connection c **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\ SZ.v n <= SZ.v max_len)

fn client_read_exact (c: connection) (ch: IO.channel) (out: array U8.t) (len: SZ.t)
  requires is_connection c **
           IO.is_channel ch **
           pts_to out 'old **
           pure (B.length 'old == SZ.v len)
  returns ok: bool
  ensures exists* bytes.
          is_connection c **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v len)

fn client_close (c: connection) (ch: IO.channel)
  requires is_connection c ** IO.is_channel ch
  returns ok: bool
  ensures is_connection c ** IO.is_channel ch
