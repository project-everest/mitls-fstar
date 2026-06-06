module TLS13.OpenSSL

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

val auth_context : Type0

val is_auth_context : auth_context -> slprop

fn auth_context_new
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len)
  returns result: option auth_context
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some ctx -> is_auth_context ctx
           | None -> emp)

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

fn auth_context_free (ctx:auth_context)
  requires is_auth_context ctx
  ensures emp
