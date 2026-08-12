module TLS13.OpenSSL

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val auth_config : Type0
val auth_context : Type0
val server_credentials : Type0

val is_auth_config :
  auth_config ->
  server_name:B.bytes ->
  trust_anchors:B.bytes ->
  validation_time_seconds:SZ.t ->
  slprop
val is_auth_context : auth_context -> slprop
val is_server_credentials:
  server_credentials ->
  certificate_chain:B.bytes ->
  credential_identity:CS.server_credential_identity ->
  slprop

fn auth_config_new
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len)
  returns config: auth_config
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          is_auth_config
            config
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds

fn auth_context_new
  (config:auth_config)
  requires is_auth_config
    config
    'server_name_bytes
    'trust_anchors_bytes
    'validation_time_seconds
  returns ctx: auth_context
  ensures is_auth_config
           config
           'server_name_bytes
           'trust_anchors_bytes
           'validation_time_seconds **
          is_auth_context ctx

fn auth_config_free (config:auth_config)
  requires is_auth_config
    config
    'server_name_bytes
    'trust_anchors_bytes
    'validation_time_seconds
  ensures emp

fn server_credentials_new
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_credentials
  ensures exists* credential_identity.
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some creds ->
             is_server_credentials
               creds
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity
           | None -> emp)

fn server_credentials_clone (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  returns clone: server_credentials
  ensures is_server_credentials creds 'certificate_chain 'credential_identity **
          is_server_credentials clone 'certificate_chain 'credential_identity

fn sign_certificate_verify
  (creds:server_credentials)
  (input:array U8.t)
  (input_len:SZ.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to input 'input_bytes **
           pts_to signature 'old_signature **
           pure (SZ.v input_len <= B.length 'input_bytes /\
                 B.length 'old_signature == SZ.v signature_capacity)
  returns result: option SZ.t
  ensures exists* signature_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to input 'input_bytes **
          pts_to signature signature_bytes **
          pure (SZ.v input_len <= B.length (Ghost.reveal 'input_bytes) /\
                B.length signature_bytes == SZ.v signature_capacity /\
                (match result with
                 | Some signature_len ->
                   SZ.v signature_len <= SZ.v signature_capacity /\
                   SZ.v signature_len <= B.length signature_bytes /\
                   C.verify_signature
                     T.Rsa_pss_rsae_sha256
                     (Ghost.reveal 'credential_identity)
                     (Seq.slice (Ghost.reveal 'input_bytes) 0 (SZ.v input_len))
                     (Seq.slice signature_bytes 0 (SZ.v signature_len))
                 | None -> True))

fn copy_server_certificate_chain
  (creds:server_credentials)
  (out:array U8.t)
  (out_capacity:SZ.t)
  requires is_server_credentials creds 'certificate_chain 'credential_identity **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity)
  returns result: option SZ.t
  ensures exists* out_bytes.
          is_server_credentials creds 'certificate_chain 'credential_identity **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_capacity /\
                (match result with
                 | Some written ->
                  SZ.v written == B.length (Ghost.reveal 'certificate_chain) /\
                  SZ.v written <= SZ.v out_capacity /\
                  Seq.equal
                    (Seq.slice out_bytes 0 (SZ.v written))
                    (Ghost.reveal 'certificate_chain)
                 | None ->
                   B.length (Ghost.reveal 'certificate_chain) > SZ.v out_capacity))

fn validate_certificate_for_local_event
  (ctx:auth_context)
  (#st:erased CS.connection_state)
  (leaf_der:array U8.t)
  (leaf_der_capacity:SZ.t)
  (leaf_der_len:SZ.t)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires is_auth_context ctx **
           pts_to leaf_der 'leaf_der_bytes **
           pts_to payload 'old_payload **
           pure (B.length 'leaf_der_bytes == SZ.v leaf_der_capacity /\
                 SZ.v leaf_der_len <= SZ.v leaf_der_capacity /\
                 B.length 'old_payload == SZ.v payload_len)
  returns ok:bool
  ensures exists* payload_bytes.
          is_auth_context ctx **
          pts_to leaf_der 'leaf_der_bytes **
          pts_to payload payload_bytes **
          pure (B.length payload_bytes == SZ.v payload_len /\
                (ok == true ==>
                CT.local_input_wf
                  (reveal st)
                  CT.LocalValidateCertificate
                  payload_bytes))

fn verify_certificate_signature_for_local_event
  (ctx:auth_context)
  (#st:erased CS.connection_state)
  (certificate_verify_input:array U8.t)
  (certificate_verify_input_capacity:SZ.t)
  (certificate_verify_input_len:SZ.t)
  (signature_scheme:U16.t)
  (signature:array U8.t)
  (signature_capacity:SZ.t)
  (signature_len:SZ.t)
  requires is_auth_context ctx **
           pts_to certificate_verify_input 'input_bytes **
           pts_to signature 'signature_bytes **
           pure (B.length 'input_bytes == SZ.v certificate_verify_input_capacity /\
                 SZ.v certificate_verify_input_len <= SZ.v certificate_verify_input_capacity /\
                 B.length 'signature_bytes == SZ.v signature_capacity /\
                 SZ.v signature_len <= SZ.v signature_capacity)
  returns ok:bool
  ensures is_auth_context ctx **
          pts_to certificate_verify_input 'input_bytes **
          pts_to signature 'signature_bytes **
          pure (ok == true ==>
                CT.local_input_wf
                  (reveal st)
                  CT.LocalVerifyCertificateSignature
                  B.empty)

(** Hand the auth context the certificates the peer sent alongside its leaf.

    Public CAs issue end-entity certificates from intermediate CAs, so a peer's
    leaf is essentially never signed directly by a configured trust anchor.
    Without the intermediates the validator cannot build a chain and rejects
    every real-world server.  The certificates supplied here are untrusted
    chain-building material only: which chains are acceptable remains entirely
    a function of the trust anchors configured in the [auth_config].

    [chain] holds the DER encoding of every certificate the peer sent, with
    entry [i] occupying [chain[offsets[i] .. offsets[i] + lens[i])] and entry 0
    being the leaf.  This is exactly the layout [copy_certificate_chain]
    produces.

    The call is a hint: it constrains nothing about the connection state, and
    so carries no postcondition beyond preserving its arguments.  Certificate
    acceptance is still decided by [validate_certificate_for_local_event],
    whose specification is unchanged. *)
fn set_peer_certificate_chain
  (ctx:auth_context)
  (chain:array U8.t)
  (chain_capacity:SZ.t)
  (chain_len:SZ.t)
  (offsets:array SZ.t)
  (lens:array SZ.t)
  (entries_capacity:SZ.t)
  (count:SZ.t)
  requires is_auth_context ctx **
           pts_to chain 'chain_bytes **
           pts_to offsets 'offsets_seq **
           pts_to lens 'lens_seq **
           pure (B.length 'chain_bytes == SZ.v chain_capacity /\
                 SZ.v chain_len <= SZ.v chain_capacity /\
                 Seq.length 'offsets_seq == SZ.v entries_capacity /\
                 Seq.length 'lens_seq == SZ.v entries_capacity /\
                 SZ.v count <= SZ.v entries_capacity)
  returns _:unit
  ensures is_auth_context ctx **
          pts_to chain 'chain_bytes **
          pts_to offsets 'offsets_seq **
          pts_to lens 'lens_seq

fn auth_context_free (ctx:auth_context)
  requires is_auth_context ctx
  ensures emp

fn server_credentials_free (creds:server_credentials)
  requires is_server_credentials creds 'certificate_chain 'credential_identity
  ensures emp
