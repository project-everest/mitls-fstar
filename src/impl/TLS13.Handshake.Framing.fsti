module TLS13.Handshake.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn build_server_certificate_verify_input
  (transcript_hash: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to transcript_hash 'hash_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'hash_bytes == 32 /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 130)
  ensures exists* out_bytes.
          pts_to transcript_hash 'hash_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130)

fn parse_handshake_header
  (input: array U8.t)
  (input_len: SZ.t)
  (msg_type_out: array U8.t)
  (msg_type_out_len: SZ.t)
  (body_len_out: array U8.t)
  (body_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to msg_type_out 'old_msg_type **
           pts_to body_len_out 'old_body_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_msg_type == SZ.v msg_type_out_len /\
                 B.length 'old_body_len == SZ.v body_len_out_len /\
                 SZ.v msg_type_out_len == 1 /\
                 SZ.v body_len_out_len == 3)
  returns ok: bool
  ensures exists* msg_type_bytes body_len_bytes.
          pts_to input 'input_bytes **
          pts_to msg_type_out msg_type_bytes **
          pts_to body_len_out body_len_bytes **
          pure (B.length msg_type_bytes == 1 /\
                B.length body_len_bytes == 3 /\
                (ok ==> SZ.v input_len >= 4) /\
                (not ok ==> SZ.v input_len < 4))

fn parse_certificate_verify_body
  (input: array U8.t)
  (input_len: SZ.t)
  (signature_scheme_out: array U8.t)
  (signature_scheme_out_len: SZ.t)
  (signature_len_out: array U8.t)
  (signature_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to signature_scheme_out 'old_signature_scheme **
           pts_to signature_len_out 'old_signature_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                B.length 'old_signature_scheme == SZ.v signature_scheme_out_len /\
                B.length 'old_signature_len == SZ.v signature_len_out_len /\
                SZ.v signature_scheme_out_len == 2 /\
                SZ.v signature_len_out_len == 2)
  returns ok: bool
  ensures exists* signature_scheme_bytes signature_len_bytes.
          pts_to input 'input_bytes **
          pts_to signature_scheme_out signature_scheme_bytes **
          pts_to signature_len_out signature_len_bytes **
          pure (B.length signature_scheme_bytes == 2 /\
                B.length signature_len_bytes == 2 /\
                (ok ==> SZ.v input_len >= 4))

fn parse_certificate_leaf_der_offsets
  (input: array U8.t)
  (input_len: SZ.t)
  (leaf_offset_out: array U8.t)
  (leaf_offset_out_len: SZ.t)
  (leaf_len_out: array U8.t)
  (leaf_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to leaf_offset_out 'old_leaf_offset **
           pts_to leaf_len_out 'old_leaf_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_leaf_offset == SZ.v leaf_offset_out_len /\
                 B.length 'old_leaf_len == SZ.v leaf_len_out_len /\
                 SZ.v leaf_offset_out_len == 2 /\
                 SZ.v leaf_len_out_len == 2)
  returns ok: bool
  ensures exists* leaf_offset_bytes leaf_len_bytes.
          pts_to input 'input_bytes **
          pts_to leaf_offset_out leaf_offset_bytes **
          pts_to leaf_len_out leaf_len_bytes **
          pure (B.length leaf_offset_bytes == 2 /\
                B.length leaf_len_bytes == 2 /\
                (ok ==> SZ.v input_len >= 9))
