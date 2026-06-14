module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CS = TLS13.Spec.ConnectionState
module CR = TLS13.Impl.ConnectionState.Repr
module O = TLS13.OpenSSL
module S = TLS13.Impl.Server
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8

val server_driver : Type0

noextract
val server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity))
           | None ->
             emp)
