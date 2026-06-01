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

type flight_view = {
  saw_encrypted_extensions: bool;
  saw_certificate: bool;
  saw_certificate_verify: bool;
  certificate_verify_verified: bool;
  saw_finished: bool;
  server_before_finished_len: (l:SZ.t{SZ.v l <= 32768});
  server_through_finished_len: (l:SZ.t{SZ.v l <= 32768});
}

let empty_flight_view : flight_view = {
  saw_encrypted_extensions = false;
  saw_certificate = false;
  saw_certificate_verify = false;
  certificate_verify_verified = false;
  saw_finished = false;
  server_before_finished_len = 0sz;
  server_through_finished_len = 0sz;
}

let flight_view_with_certificate_verify_verified (view: flight_view) : flight_view =
  { view with certificate_verify_verified = true }

val is_flight_state: flight_state -> slprop
val flight_state_exactly: flight_state -> flight_view -> slprop

ghost
fn reveal_flight_view (st: flight_state)
  requires is_flight_state st
  ensures exists* view. flight_state_exactly st view

ghost
fn hide_flight_view (st: flight_state)
  requires flight_state_exactly st 'view
  ensures is_flight_state st

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

fn set_client_hello_fragment
  (st: flight_state)
  (hello: array U8.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_len /\
                 SZ.v hello_len <= 512)
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
  returns len: (l:SZ.t{SZ.v l <= 512})
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

fn set_server_hello_fragment
  (st: flight_state)
  (hello: array U8.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_len /\
                 SZ.v hello_len <= 4096)
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
  returns len: (l:SZ.t{SZ.v l <= 4096})
  ensures is_flight_state st

fn derive_server_handshake_keys_from_share
  (st: flight_state)
  (server_key_share: array U8.t)
  (server_key_share_len: SZ.t)
  requires is_flight_state st **
           pts_to server_key_share 'key_share_bytes **
           pure (B.length 'key_share_bytes == SZ.v server_key_share_len /\
                 SZ.v server_key_share_len == 32)
  returns ok: bool
  ensures is_flight_state st **
          pts_to server_key_share 'key_share_bytes

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
  requires is_flight_state st **
           pure (SZ.v leaf_len <= 32768)
  ensures is_flight_state st

fn accept_certificate_verify (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_pending_certificate_verify (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn set_certificate_verify_signature
  (st: flight_state)
  (signature_scheme: U16.t)
  (signature_offset: SZ.t)
  (signature_len: SZ.t)
  requires is_flight_state st **
           pure (SZ.v signature_len <= 32768)
  ensures is_flight_state st

fn mark_certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  ensures is_flight_state st

fn mark_certificate_verify_verified_exact (st: flight_state)
  requires flight_state_exactly st 'view
  ensures flight_state_exactly st (flight_view_with_certificate_verify_verified 'view)

fn accept_finished (st: flight_state) (message_len: SZ.t) (body_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn accept_pending_finished (st: flight_state)
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

fn verify_server_finished (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st

fn derive_application_keys
  (st: flight_state)
  (client_key: array U8.t)
  (client_key_len: SZ.t)
  (client_iv: array U8.t)
  (client_iv_len: SZ.t)
  (server_key: array U8.t)
  (server_key_len: SZ.t)
  (server_iv: array U8.t)
  (server_iv_len: SZ.t)
  requires is_flight_state st **
           pts_to client_key 'old_client_key **
           pts_to client_iv 'old_client_iv **
           pts_to server_key 'old_server_key **
           pts_to server_iv 'old_server_iv **
           pure (B.length 'old_client_key == SZ.v client_key_len /\
                 B.length 'old_client_iv == SZ.v client_iv_len /\
                 B.length 'old_server_key == SZ.v server_key_len /\
                 B.length 'old_server_iv == SZ.v server_iv_len /\
                 SZ.v client_key_len == 32 /\
                 SZ.v client_iv_len == 12 /\
                 SZ.v server_key_len == 32 /\
                 SZ.v server_iv_len == 12)
  returns ok: bool
  ensures exists* client_key_bytes client_iv_bytes server_key_bytes server_iv_bytes.
          is_flight_state st **
          pts_to client_key client_key_bytes **
          pts_to client_iv client_iv_bytes **
          pts_to server_key server_key_bytes **
          pts_to server_iv server_iv_bytes **
          pure (B.length client_key_bytes == 32 /\
                B.length client_iv_bytes == 12 /\
                B.length server_key_bytes == 32 /\
                B.length server_iv_bytes == 12)

fn build_client_finished_record
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 58)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 58)

fn build_certificate_verify_input
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 130)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130)

fn copy_certificate_leaf_der
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)

fn copy_certificate_verify_signature
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)

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
  returns len: (l:SZ.t{SZ.v l <= 32768})
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
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st

fn server_before_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st

fn server_before_finished_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_before_finished_len)

fn server_through_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st

fn server_through_finished_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_through_finished_len)

fn saw_certificate (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn saw_certificate_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_certificate)

fn saw_certificate_verify (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn saw_certificate_verify_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_certificate_verify)

fn certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  returns verified: bool
  ensures is_flight_state st

fn certificate_verify_verified_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns verified: bool
  ensures flight_state_exactly st 'view **
          pure (verified == 'view.certificate_verify_verified)

fn saw_finished (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st

fn saw_finished_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_finished)

fn encrypted_handshake_complete (st: flight_state)
  requires is_flight_state st
  returns complete: bool
  ensures is_flight_state st

fn encrypted_handshake_complete_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns complete: bool
  ensures flight_state_exactly st 'view **
          pure (complete == ('view.saw_encrypted_extensions && 'view.saw_finished))
