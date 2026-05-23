module TLS13.Handshake.Transcript.External

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn sha256_three
  (a: array U8.t)
  (a_len: SZ.t)
  (b: array U8.t)
  (b_len: SZ.t)
  (c: array U8.t)
  (c_len: SZ.t)
  (out: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pts_to c 'c_bytes **
           pts_to out 'old_out **
           pure (B.length 'a_bytes == SZ.v a_len /\
                 B.length 'b_bytes == SZ.v b_len /\
                 B.length 'c_bytes == SZ.v c_len /\
                 B.length 'old_out == 32 /\
                 SZ.v a_len + SZ.v b_len + SZ.v c_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pts_to c 'c_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (B.append (B.append 'a_bytes 'b_bytes) 'c_bytes)))
