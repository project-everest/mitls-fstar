module TLS13.Connection.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module IO = TLS13.IO
module Rec = TLS13.Record
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

fn export_application_keys
  (c: connection)
  (client_key: array U8.t)
  (client_iv: array U8.t)
  (server_key: array U8.t)
  (server_iv: array U8.t)
  requires is_connection c **
           pts_to client_key 'old_client_key **
           pts_to client_iv 'old_client_iv **
           pts_to server_key 'old_server_key **
           pts_to server_iv 'old_server_iv **
           pure (B.length 'old_client_key == 32 /\
                 B.length 'old_client_iv == 12 /\
                 B.length 'old_server_key == 32 /\
                 B.length 'old_server_iv == 12)
  returns ok: bool
  ensures exists* client_key_bytes client_iv_bytes server_key_bytes server_iv_bytes.
          is_connection c **
          pts_to client_key client_key_bytes **
          pts_to client_iv client_iv_bytes **
          pts_to server_key server_key_bytes **
          pts_to server_iv server_iv_bytes **
          pure (B.length client_key_bytes == 32 /\
                B.length client_iv_bytes == 12 /\
                B.length server_key_bytes == 32 /\
                B.length server_iv_bytes == 12)

fn client_write_application_record
  (c: connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (key: array U8.t)
  (iv: array U8.t)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (chunk_len: SZ.t)
  requires is_connection c **
           Rec.is_record_state record_state 'record_s **
           IO.is_channel ch **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pts_to buf 'bytes **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12 /\
                 B.length 'bytes == SZ.v total_len /\
                 SZ.v chunk_len > 0 /\
                 SZ.v chunk_len <= 4096 /\
                 SZ.v offset + SZ.v chunk_len <= SZ.v total_len)
  returns ok: bool
  ensures exists* record_s'.
          is_connection c **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes **
          pts_to buf 'bytes

fn client_read_application_record
  (c: connection)
  (ch: IO.channel)
  (record_state: Rec.record_state)
  (key: array U8.t)
  (iv: array U8.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires is_connection c **
           Rec.is_record_state record_state 'record_s **
           IO.is_channel ch **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pts_to out 'old **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12 /\
                 B.length 'old == SZ.v total_len /\
                 SZ.v remaining > 0 /\
                 SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns n: SZ.t
  ensures exists* record_s' bytes.
          is_connection c **
          Rec.is_record_state record_state record_s' **
          IO.is_channel ch **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len /\
                SZ.v n <= SZ.v remaining)

fn client_close (c: connection) (ch: IO.channel)
  requires is_connection c ** IO.is_channel ch
  returns ok: bool
  ensures is_connection c ** IO.is_channel ch
