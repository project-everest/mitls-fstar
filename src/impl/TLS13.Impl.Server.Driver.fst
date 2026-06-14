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

noeq type server_driver = {
  server_driver_server: S.server;
  server_driver_credentials: O.server_credentials;
}

noextract
let server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity

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
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let erased_identity : erased CS.server_credential_identity =
        Ghost.hide credential_identity;
      let s =
        S.new_server_erased_credential_identity
          certificate_chain
          certificate_chain_len
          #erased_identity;
      assert (pure (Ghost.reveal erased_identity == credential_identity));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            (Ghost.reveal erased_identity)))
        as
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      let d = {
        server_driver_server = s;
        server_driver_credentials = creds;
      };
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (S.connection_exactly
          d.server_driver_server
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        as
        (O.is_server_credentials
          d.server_driver_credentials
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
}
