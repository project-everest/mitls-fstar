module TLS13.X509

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

val validation_context : Type0
val is_validation_context: validation_context -> X.trust_store -> X.validation_time -> slprop

fn validate_chain
  (ctx: validation_context)
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (certs: array U8.t)
  (certs_len: SZ.t)
  requires is_validation_context ctx 'trust_store 'validation_time **
           pts_to hostname 'hostname_bytes **
           pts_to certs 'cert_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len /\
                 B.length 'cert_bytes == SZ.v certs_len)
  returns peer: option X.peer_identity
  ensures is_validation_context ctx 'trust_store 'validation_time **
          pts_to hostname 'hostname_bytes **
          pts_to certs 'cert_bytes **
          pure (peer == X.validate_chain
                          (Ghost.reveal 'hostname_bytes)
                          'validation_time
                          'trust_store
                          [Ghost.reveal 'cert_bytes])

fn verify_peer_signature
  (peer: X.peer_identity)
  (scheme: T.signature_scheme)
  (message: array U8.t)
  (message_len: SZ.t)
  (signature: array U8.t)
  (signature_len: SZ.t)
  requires pts_to message 'message_bytes **
          pts_to signature 'signature_bytes **
          pure (B.length 'message_bytes == SZ.v message_len /\
                B.length 'signature_bytes == SZ.v signature_len)
  returns ok: bool
  ensures pts_to message 'message_bytes **
          pts_to signature 'signature_bytes **
          pure (ok == C.verify_signature
                        scheme
                        peer.X.leaf_public_key
                        (Ghost.reveal 'message_bytes)
                        (Ghost.reveal 'signature_bytes))
