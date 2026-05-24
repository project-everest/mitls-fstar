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

fn client_connect
  (c: connection)
  (ch: IO.channel)
  (client_key: array U8.t)
  (client_iv: array U8.t)
  (server_key: array U8.t)
  (server_iv: array U8.t)
  requires is_connection c **
           IO.is_channel ch **
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
          IO.is_channel ch **
          pts_to client_key client_key_bytes **
          pts_to client_iv client_iv_bytes **
          pts_to server_key server_key_bytes **
          pts_to server_iv server_iv_bytes **
          pure (B.length client_key_bytes == 32 /\
                B.length client_iv_bytes == 12 /\
                B.length server_key_bytes == 32 /\
                B.length server_iv_bytes == 12)

fn client_write_raw_record
  (c: connection)
  (ch: IO.channel)
  (header: array U8.t)
  (header_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  requires   is_connection c **
  IO.is_channel ch **
  pts_to header 'header_bytes **
  pts_to cipher 'cipher_bytes **
  pure (B.length 'header_bytes == SZ.v header_len /\
        B.length 'cipher_bytes == SZ.v cipher_len)
  returns ok: bool
  ensures is_connection c **
          IO.is_channel ch **
          pts_to header 'header_bytes **
          pts_to cipher 'cipher_bytes

fn client_read_raw_record_header
  (c: connection)
  (ch: IO.channel)
  (header: array U8.t)
  (header_len: SZ.t)
  requires   is_connection c **
  IO.is_channel ch **
  pts_to header 'old_header **
  pure (B.length 'old_header == SZ.v header_len /\
        SZ.v header_len == 5)
  returns ok: bool
  ensures exists* header_bytes.
          is_connection c **
          IO.is_channel ch **
          pts_to header header_bytes **
          pure (B.length header_bytes == 5)

fn client_read_raw_record_fragment
  (c: connection)
  (ch: IO.channel)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  requires   is_connection c **
  IO.is_channel ch **
  pts_to cipher 'old_cipher **
  pure (B.length 'old_cipher == SZ.v cipher_len)
  returns ok: bool
  ensures exists* cipher_bytes.
          is_connection c **
          IO.is_channel ch **
          pts_to cipher cipher_bytes **
          pure (B.length cipher_bytes == SZ.v cipher_len)

fn client_close (c: connection) (ch: IO.channel)
  requires is_connection c ** IO.is_channel ch
  returns ok: bool
  ensures is_connection c ** IO.is_channel ch
