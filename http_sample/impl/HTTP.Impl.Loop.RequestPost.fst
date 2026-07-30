module HTTP.Impl.Loop.RequestPost

#lang-pulse

(**
  Reachability driver for the verified POST request-head emitter
  `HTTP.Impl.Codec.RequestPost.http_emit_request_post`.

  `http_build_post_head` is a thin top-level wrapper that fills `out` with the
  byte-exact POST request head for `target` + a `Content-Length` of `len` (its
  body of `len` bytes is sent separately by the caller).  Its sole purpose is to
  be a `HTTP.Impl.*.Loop.*` bundle root so KaRaMeL dead-code elimination keeps
  `http_emit_request_post` in the `HTTP_Verified` C bundle for the
  `request_post_test` harness.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module W   = HTTP.Wire.Common
module CL  = HTTP.Impl.Codec.Length
module RP  = HTTP.Impl.Codec.RequestPost

open HTTP.Wire.Length

(* Emit the POST request head into `out`; on a space-free target the bytes equal
   the spec `ser_request_post target len`. *)
fn http_build_post_head
  (target: array U8.t) (target_len: SZ.t) (len: U32.t) (out: array U8.t)
  requires
    pts_to target 't ** pts_to out 'o **
    pure (Seq.length 't == SZ.v target_len /\ W.space_free 't /\
          U32.v len < W.max_len8 /\
          SZ.v target_len + 40 < pow2 32 /\
          Seq.length 'o == 36 + SZ.v target_len + CL.dec_width (U32.v len))
  ensures
    pts_to target 't **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 36 + SZ.v target_len + CL.dec_width (U32.v len)))
{
  RP.http_emit_request_post target target_len len out;
}
