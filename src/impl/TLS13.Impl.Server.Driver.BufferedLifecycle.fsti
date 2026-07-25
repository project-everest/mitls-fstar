module TLS13.Impl.Server.Driver.BufferedLifecycle

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module O = TLS13.OpenSSL
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn new_server_with_credentials
  (credentials:O.server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (#supported_profile_provider:erased SP.server_supported_profile_provider)
  requires
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity) **
    pts_to certificate_chain 'certificate_chain_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'certificate_chain_bytes <=
        Bounds.max_server_certificate_chain_len)
  returns result:option DS.top_server_driver
  ensures
    pts_to certificate_chain 'certificate_chain_bytes **
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity **
      (match result with
       | Some d ->
         DS.top_server_driver_live
           d
           (CR.server_initial_state
             (Ghost.reveal 'certificate_chain_bytes)
             credential_identity)
           (Ghost.reveal 'certificate_chain_bytes)
           credential_identity **
         pure (
           ST.server_state_correct
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity) /\
           ST.server_end_to_end_invariant
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity))
       | None -> emp))

fn free
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_closed
      d 'st 'certificate_chain 'credential_identity
  ensures DS.top_server_driver_released d 'st
