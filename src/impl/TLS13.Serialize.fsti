module TLS13.Serialize

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

fn serialize_supported_client_hello (hello: H.client_hello) (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old **
           pure (B.length 'old == SZ.v out_len /\
                 B.length (W.serialize_supported_client_hello hello) == SZ.v out_len)
  returns ok: bool
  ensures pts_to out (W.serialize_supported_client_hello hello) ** pure ok

fn serialize_handshake (msg: H.handshake_msg) (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old **
           pure (B.length 'old == SZ.v out_len /\
                 B.length (W.serialize_handshake msg) == SZ.v out_len)
  returns ok: bool
  ensures pts_to out (W.serialize_handshake msg) ** pure ok

fn serialize_server_certificate_verify_input
  (transcript_hash: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to transcript_hash 'hash_bytes **
           pts_to out 'old **
           pure (B.length 'hash_bytes == 32 /\
                 B.length 'old == SZ.v out_len /\
                 B.length (W.serialize_server_certificate_verify_input (Ghost.reveal 'hash_bytes)) == SZ.v out_len)
  returns ok: bool
  ensures pts_to transcript_hash 'hash_bytes **
          pts_to out (W.serialize_server_certificate_verify_input (Ghost.reveal 'hash_bytes)) **
          pure ok

fn serialize_record (content_type: T.content_type) (fragment: array U8.t) (fragment_len: SZ.t) (out: array U8.t) (out_len: SZ.t)
  requires pts_to fragment 'fragment_bytes **
           pts_to out 'old **
           pure (B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old == SZ.v out_len /\
                 B.length (W.serialize_record content_type (Ghost.reveal 'fragment_bytes)) == SZ.v out_len)
  returns ok: bool
  ensures pts_to fragment 'fragment_bytes **
          pts_to out (W.serialize_record content_type (Ghost.reveal 'fragment_bytes)) **
          pure ok
