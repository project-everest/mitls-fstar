module TLS13.X509

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module SZ = FStar.SizeT
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
