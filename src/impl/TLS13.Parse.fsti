module TLS13.Parse

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

fn parse_handshake (input: array U8.t) (input_len: SZ.t)
  requires pts_to input 'bytes ** pure (B.length 'bytes == SZ.v input_len)
  returns parsed: option (H.handshake_msg & nat)
  ensures pts_to input 'bytes ** pure (parsed == W.parse_handshake (Ghost.reveal 'bytes))

fn parse_supported_server_hello (input: array U8.t) (input_len: SZ.t)
  requires pts_to input 'bytes ** pure (B.length 'bytes == SZ.v input_len)
  returns parsed: option H.server_hello
  ensures pts_to input 'bytes **
          pure (parsed == W.parse_supported_server_hello (Ghost.reveal 'bytes))

fn parse_certificate_leaf_der (input: array U8.t) (input_len: SZ.t)
  requires pts_to input 'bytes ** pure (B.length 'bytes == SZ.v input_len)
  returns parsed: option B.bytes
  ensures pts_to input 'bytes **
          pure (parsed == W.parse_certificate_leaf_der (Ghost.reveal 'bytes))

fn parse_certificate_verify (input: array U8.t) (input_len: SZ.t)
  requires pts_to input 'bytes ** pure (B.length 'bytes == SZ.v input_len)
  returns parsed: option H.certificate_verify
  ensures pts_to input 'bytes **
          pure (parsed == W.parse_certificate_verify (Ghost.reveal 'bytes))

fn parse_record (input: array U8.t) (input_len: SZ.t)
  requires pts_to input 'bytes ** pure (B.length 'bytes == SZ.v input_len)
  returns parsed: option (TLS13.Types.content_type & TLS13.Record.Spec.sealed_record & nat)
  ensures pts_to input 'bytes ** pure (parsed == W.parse_record (Ghost.reveal 'bytes))
