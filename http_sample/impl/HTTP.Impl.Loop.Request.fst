module HTTP.Impl.Loop.Request

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** driver over the verified method-aware
  request-line parser `HTTP.Impl.Codec.RequestLine.http_parse_request_line`.

  `http_method_eq` parses the request line at the head of `inp[0..n)` and
  reports whether the recovered method token equals the caller-provided name
  `nm` (exact, case-sensitive — HTTP methods are upper-case tokens).  This is
  the primitive a server uses to dispatch on the method (e.g. "is this a
  `POST`?").  Besides being useful it keeps `http_parse_request_line` reachable
  through KaRaMeL dead-code elimination so the leaf is exported into the
  `HTTP_Verified` C bundle for the `request_line_test` harness.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ  = FStar.SizeT
module Seq = FStar.Seq
module U8  = FStar.UInt8
module R   = Pulse.Lib.Reference
module RL  = HTTP.Impl.Codec.RequestLine

open Pulse.Lib.BoundedIntegers

(* Parse the request line and return true iff its method equals `nm` (exact).
   The equality scan runs unconditionally in the `match_ci_at` idiom: the
   accumulator `m` starts true only if the line parsed and the lengths agree, so
   when it is false the `while` never runs; while it is true, the method length
   is in bounds of both arrays (from the leaf's postcondition), carried as a
   constant proposition guarded by `m` in the invariant.  Memory-safe.  This
   avoids the Error-228 divergent-block join from calling a `while`-containing
   helper inside a conditional. *)
fn http_method_eq
  (inp: array U8.t) (n: SZ.t) (nm: array U8.t) (nm_len: SZ.t)
  requires
    pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v nm_len <= Seq.length 'm)
  returns b: bool
  ensures pts_to inp 'i ** pts_to nm 'm
{
  let mut pok   = false;
  let mut pmlen = 0sz;
  let mut ptoff = 0sz;
  let mut ptlen = 0sz;
  RL.http_parse_request_line inp n pok pmlen ptoff ptlen;
  let ok   = !pok;
  let mlen = !pmlen;
  let mut k = 0sz;
  let mut m = ok && SZ.eq mlen nm_len;
  while (SZ.lt !k mlen && !m)
  invariant exists* (vk:SZ.t) (vm:bool).
    R.pts_to k vk ** R.pts_to m vm ** pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v vk <= SZ.v mlen /\
          (vm == true ==> (SZ.v mlen <= Seq.length 'i /\ SZ.v mlen <= Seq.length 'm)))
  decreases (Prims.op_Subtraction (SZ.v mlen) (SZ.v (!k)))
  {
    let vk = !k;
    let c = inp.(vk);
    let e = nm.(vk);
    m := U8.eq c e;
    k := SZ.add vk 1sz;
  };
  !m
}
