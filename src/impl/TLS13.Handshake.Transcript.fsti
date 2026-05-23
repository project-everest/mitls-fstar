module TLS13.Handshake.Transcript

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn hash_client_server_handshake
  (client_hello: array U8.t)
  (client_hello_len: SZ.t)
  (server_hello: array U8.t)
  (server_hello_len: SZ.t)
  (server_handshake: array U8.t)
  (server_handshake_len: SZ.t)
  (out: array U8.t)
  requires pts_to client_hello 'client_hello_bytes **
           pts_to server_hello 'server_hello_bytes **
           pts_to server_handshake 'server_handshake_bytes **
           pts_to out 'old_out **
           pure (B.length 'client_hello_bytes == SZ.v client_hello_len /\
                 B.length 'server_hello_bytes == SZ.v server_hello_len /\
                 B.length 'server_handshake_bytes == SZ.v server_handshake_len /\
                 B.length 'old_out == 32 /\
                 SZ.v client_hello_len + SZ.v server_hello_len + SZ.v server_handshake_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to client_hello 'client_hello_bytes **
          pts_to server_hello 'server_hello_bytes **
          pts_to server_handshake 'server_handshake_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (B.append (B.append 'client_hello_bytes 'server_hello_bytes) 'server_handshake_bytes)))

fn equal32
  (a: array U8.t)
  (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns eq: bool
  ensures pts_to a 'a_bytes ** pts_to b 'b_bytes
