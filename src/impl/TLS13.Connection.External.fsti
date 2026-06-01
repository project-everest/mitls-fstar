module TLS13.Connection.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module IO = TLS13.IO
module Rec = TLS13.Record
module SZ = FStar.SizeT
module U16 = FStar.UInt16
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
  requires is_connection c **
           IO.is_channel ch
  returns ok: bool
  ensures is_connection c **
          IO.is_channel ch

fn derive_application_keys
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

fn validate_certificate
  (c: connection)
  (leaf_der: array U8.t)
  (leaf_der_len: SZ.t)
  requires is_connection c **
           pts_to leaf_der 'leaf_der_bytes **
           pure (B.length 'leaf_der_bytes == SZ.v leaf_der_len)
  returns ok: bool
  ensures is_connection c **
          pts_to leaf_der 'leaf_der_bytes

fn verify_certificate_signature
  (c: connection)
  (certificate_verify_input: array U8.t)
  (certificate_verify_input_len: SZ.t)
  (signature_scheme: U16.t)
  (signature: array U8.t)
  (signature_len: SZ.t)
  requires is_connection c **
           pts_to certificate_verify_input 'input_bytes **
           pts_to signature 'signature_bytes **
           pure (B.length 'input_bytes == SZ.v certificate_verify_input_len /\
                B.length 'signature_bytes == SZ.v signature_len)
  returns ok: bool
  ensures is_connection c **
          pts_to certificate_verify_input 'input_bytes **
          pts_to signature 'signature_bytes

fn client_write_raw
  (c: connection)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires   is_connection c **
  IO.is_channel ch **
  pts_to buf 'bytes **
  pure (B.length 'bytes == SZ.v total_len /\
        SZ.v remaining > 0 /\
        SZ.v offset + SZ.v remaining <= SZ.v total_len)
  returns n: SZ.t
  ensures is_connection c **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (SZ.v n <= SZ.v remaining)

fn client_read_raw
  (c: connection)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires   is_connection c **
  IO.is_channel ch **
  pts_to buf 'old **
  pure (B.length 'old == SZ.v total_len /\
        SZ.v remaining > 0 /\
        SZ.v offset + SZ.v remaining <= SZ.v total_len)
  returns n: SZ.t
  ensures exists* bytes.
          is_connection c **
          IO.is_channel ch **
          pts_to buf bytes **
          pure (B.length bytes == SZ.v total_len /\
                SZ.v n <= SZ.v remaining)

fn client_close (c: connection) (ch: IO.channel)
  requires is_connection c ** IO.is_channel ch
  returns ok: bool
  ensures is_connection c ** IO.is_channel ch
