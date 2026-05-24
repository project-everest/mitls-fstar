module TLS13.Handshake.FlightState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Rec = TLS13.Record
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val flight_state : Type0
val is_flight_state: flight_state -> slprop

fn flight_state_new ()
  returns st: flight_state
  ensures is_flight_state st

fn flight_state_free (st: flight_state)
  requires is_flight_state st
  ensures emp

fn reset (st: flight_state)
  requires is_flight_state st
  ensures is_flight_state st

fn set_client_hello
  (st: flight_state)
  (hello: array U8.t)
  (hello_capacity: SZ.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_capacity /\
                 SZ.v hello_capacity == 512 /\
                 SZ.v hello_len <= SZ.v hello_capacity)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes

fn copy_client_hello
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 512)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 512)

fn client_hello_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn set_server_hello
  (st: flight_state)
  (hello: array U8.t)
  (hello_capacity: SZ.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_capacity /\
                 SZ.v hello_capacity == 4096 /\
                 SZ.v hello_len <= SZ.v hello_capacity)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes

fn copy_server_hello
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 4096)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 4096)

fn server_hello_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn set_server_handshake
  (st: flight_state)
  (messages: array U8.t)
  (messages_capacity: SZ.t)
  requires is_flight_state st **
           pts_to messages 'messages_bytes **
           pure (B.length 'messages_bytes == SZ.v messages_capacity /\
                 SZ.v messages_capacity == 32768)
  ensures is_flight_state st **
          pts_to messages 'messages_bytes

fn copy_server_handshake
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)

fn set_handshake_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes

fn copy_handshake_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)

fn set_client_handshake_traffic_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes

fn copy_client_handshake_traffic_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)

fn set_client_handshake_key_iv
  (st: flight_state)
  (key: array U8.t)
  (key_len: SZ.t)
  (iv: array U8.t)
  (iv_len: SZ.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'iv_bytes == SZ.v iv_len /\
                 SZ.v key_len == 32 /\
                 SZ.v iv_len == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes

fn copy_client_handshake_key_iv
  (st: flight_state)
  (key_out: array U8.t)
  (key_out_len: SZ.t)
  (iv_out: array U8.t)
  (iv_out_len: SZ.t)
  requires is_flight_state st **
           pts_to key_out 'old_key **
           pts_to iv_out 'old_iv **
           pure (B.length 'old_key == SZ.v key_out_len /\
                 B.length 'old_iv == SZ.v iv_out_len /\
                 SZ.v key_out_len == 32 /\
                 SZ.v iv_out_len == 12)
  ensures exists* key_bytes iv_bytes.
          is_flight_state st **
          pts_to key_out key_bytes **
          pts_to iv_out iv_bytes **
          pure (B.length key_bytes == 32 /\
                B.length iv_bytes == 12)

fn seal_client_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old_out **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old_out == SZ.v plain_len + 16)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old_out)

fn set_server_handshake_traffic_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes

fn copy_server_handshake_traffic_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)

fn set_server_handshake_key_iv
  (st: flight_state)
  (key: array U8.t)
  (key_len: SZ.t)
  (iv: array U8.t)
  (iv_len: SZ.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'iv_bytes == SZ.v iv_len /\
                 SZ.v key_len == 32 /\
                 SZ.v iv_len == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes

fn copy_server_handshake_key_iv
  (st: flight_state)
  (key_out: array U8.t)
  (key_out_len: SZ.t)
  (iv_out: array U8.t)
  (iv_out_len: SZ.t)
  requires is_flight_state st **
           pts_to key_out 'old_key **
           pts_to iv_out 'old_iv **
           pure (B.length 'old_key == SZ.v key_out_len /\
                 B.length 'old_iv == SZ.v iv_out_len /\
                 SZ.v key_out_len == 32 /\
                 SZ.v iv_out_len == 12)
  ensures exists* key_bytes iv_bytes.
          is_flight_state st **
          pts_to key_out key_bytes **
          pts_to iv_out iv_bytes **
          pure (B.length key_bytes == 32 /\
                B.length iv_bytes == 12)

fn install_server_handshake_record_keys
  (st: flight_state)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes

fn open_server_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old_out **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old_out + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old_out)

fn process_server_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 SZ.v aad_len == 5 /\
                 16 < SZ.v cipher_len /\
                 SZ.v cipher_len <= 20000)
  returns ok: bool
  ensures is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes

fn handshake_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn parsed_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn pending_handshake_message_complete (st: flight_state)
  requires is_flight_state st
  returns complete: bool
  ensures is_flight_state st

fn pending_handshake_message_type (st: flight_state)
  requires is_flight_state st
  returns msg_type: U8.t
  ensures is_flight_state st

fn append_handshake_len (st: flight_state) (fragment_len: SZ.t) (capacity: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_encrypted_extensions (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_pending_encrypted_extensions (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_certificate (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_pending_certificate (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn set_certificate_leaf (st: flight_state) (leaf_offset: SZ.t) (leaf_len: SZ.t)
  requires is_flight_state st
  ensures is_flight_state st

fn accept_certificate_verify (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn set_certificate_verify_signature
  (st: flight_state)
  (signature_scheme: U16.t)
  (signature_offset: SZ.t)
  (signature_len: SZ.t)
  requires is_flight_state st
  ensures is_flight_state st

fn mark_certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  ensures is_flight_state st

fn accept_finished (st: flight_state) (message_len: SZ.t) (body_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn set_server_finished_verify_data
  (st: flight_state)
  (verify_data: array U8.t)
  (verify_data_len: SZ.t)
  requires is_flight_state st **
           pts_to verify_data 'verify_data_bytes **
           pure (B.length 'verify_data_bytes == SZ.v verify_data_len /\
                 SZ.v verify_data_len == 32)
  ensures is_flight_state st **
          pts_to verify_data 'verify_data_bytes

fn copy_server_finished_verify_data
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)

fn certificate_verify_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st

fn certificate_leaf_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st

fn certificate_leaf_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn certificate_verify_signature_scheme (st: flight_state)
  requires is_flight_state st
  returns scheme: U16.t
  ensures is_flight_state st

fn certificate_verify_signature_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st

fn certificate_verify_signature_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn server_before_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn server_through_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st

fn saw_certificate (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn saw_certificate_verify (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  returns verified: bool
  ensures is_flight_state st

fn saw_finished (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn encrypted_handshake_complete (st: flight_state)
  requires is_flight_state st
  returns complete: bool
  ensures is_flight_state st
