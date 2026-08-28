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


open FStar.SizeT { (+), (-), ( * ), (/), (%), (<), (<=), (>), (>=) }
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
  decreases (Prims.op_Minus (SZ.v mlen) (SZ.v (!k)))
  {
    let vk = !k;
    let c = inp.(vk);
    let e = nm.(vk);
    m := U8.eq c e;
    k := SZ.add vk 1sz;
  };
  !m
}

(* Parse the request line at the head of `inp[0..n)` and report whether it is
   well-formed (method + target + recognized HTTP-version token).  A server uses
   this to answer `400 Bad Request` on an unparseable request line instead of
   silently dropping.  Memory-safe; no loop, so no divergent-block hazard. *)
fn http_request_line_ok
  (inp: array U8.t) (n: SZ.t)
  requires
    pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  returns b: bool
  ensures pts_to inp 'i
{
  let mut pok   = false;
  let mut pmlen = 0sz;
  let mut ptoff = 0sz;
  let mut ptlen = 0sz;
  RL.http_parse_request_line inp n pok pmlen ptoff ptlen;
  !pok
}

(* Parse the request line and report whether its method token is one of the
   eight standard HTTP methods (GET, HEAD, POST, PUT, DELETE, CONNECT, OPTIONS,
   TRACE).  A server uses this to answer `501 Not Implemented` for any other
   (syntactically valid) method.  The method occupies `inp[0..mlen)`; we read the
   first seven positions at indices clamped into `[0, n)` (guarded by `ok` and
   the parsed length, so every access is in bounds) and match each known token by
   exact length + bytes.  Memory-safe; no loop. *)
fn http_method_known
  (inp: array U8.t) (n: SZ.t)
  requires
    pts_to inp 'i **
    pure (0 < SZ.v n /\ SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  returns b: bool
  ensures pts_to inp 'i
{
  let mut pok   = false;
  let mut pmlen = 0sz;
  let mut ptoff = 0sz;
  let mut ptlen = 0sz;
  RL.http_parse_request_line inp n pok pmlen ptoff ptlen;
  let ok   = !pok;
  let mlen = !pmlen;
  (* Clamp each read index into [0, n): index k is used only when ok holds and
     k < mlen (<= n), otherwise it collapses to 0 (< n by precondition). *)
  let i0 = 0sz;
  let i1 = (if (ok && SZ.lt 1sz mlen) then 1sz else 0sz);
  let i2 = (if (ok && SZ.lt 2sz mlen) then 2sz else 0sz);
  let i3 = (if (ok && SZ.lt 3sz mlen) then 3sz else 0sz);
  let i4 = (if (ok && SZ.lt 4sz mlen) then 4sz else 0sz);
  let i5 = (if (ok && SZ.lt 5sz mlen) then 5sz else 0sz);
  let i6 = (if (ok && SZ.lt 6sz mlen) then 6sz else 0sz);
  let b0 = inp.(i0);
  let b1 = inp.(i1);
  let b2 = inp.(i2);
  let b3 = inp.(i3);
  let b4 = inp.(i4);
  let b5 = inp.(i5);
  let b6 = inp.(i6);
  let is_get =
    ok && SZ.eq mlen 3sz &&
    U8.eq b0 0x47uy && U8.eq b1 0x45uy && U8.eq b2 0x54uy;
  let is_put =
    ok && SZ.eq mlen 3sz &&
    U8.eq b0 0x50uy && U8.eq b1 0x55uy && U8.eq b2 0x54uy;
  let is_head =
    ok && SZ.eq mlen 4sz &&
    U8.eq b0 0x48uy && U8.eq b1 0x45uy && U8.eq b2 0x41uy && U8.eq b3 0x44uy;
  let is_post =
    ok && SZ.eq mlen 4sz &&
    U8.eq b0 0x50uy && U8.eq b1 0x4Fuy && U8.eq b2 0x53uy && U8.eq b3 0x54uy;
  let is_trace =
    ok && SZ.eq mlen 5sz &&
    U8.eq b0 0x54uy && U8.eq b1 0x52uy && U8.eq b2 0x41uy && U8.eq b3 0x43uy &&
    U8.eq b4 0x45uy;
  let is_delete =
    ok && SZ.eq mlen 6sz &&
    U8.eq b0 0x44uy && U8.eq b1 0x45uy && U8.eq b2 0x4Cuy && U8.eq b3 0x45uy &&
    U8.eq b4 0x54uy && U8.eq b5 0x45uy;
  let is_options =
    ok && SZ.eq mlen 7sz &&
    U8.eq b0 0x4Fuy && U8.eq b1 0x50uy && U8.eq b2 0x54uy && U8.eq b3 0x49uy &&
    U8.eq b4 0x4Fuy && U8.eq b5 0x4Euy && U8.eq b6 0x53uy;
  let is_connect =
    ok && SZ.eq mlen 7sz &&
    U8.eq b0 0x43uy && U8.eq b1 0x4Fuy && U8.eq b2 0x4Euy && U8.eq b3 0x4Euy &&
    U8.eq b4 0x45uy && U8.eq b5 0x43uy && U8.eq b6 0x54uy;
  is_get || is_put || is_head || is_post || is_trace || is_delete ||
  is_options || is_connect
}

(* Parse the request line and report whether its method is one this server
   actually IMPLEMENTS: GET, HEAD, or POST.  A server answers `405 Method Not
   Allowed` for a syntactically valid, recognized-but-unsupported method (e.g.
   DELETE/PUT).  Same in-bounds inline-byte matching as `http_method_known`;
   memory-safe, loop-free. *)
fn http_method_allowed
  (inp: array U8.t) (n: SZ.t)
  requires
    pts_to inp 'i **
    pure (0 < SZ.v n /\ SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  returns b: bool
  ensures pts_to inp 'i
{
  let mut pok   = false;
  let mut pmlen = 0sz;
  let mut ptoff = 0sz;
  let mut ptlen = 0sz;
  RL.http_parse_request_line inp n pok pmlen ptoff ptlen;
  let ok   = !pok;
  let mlen = !pmlen;
  let i0 = 0sz;
  let i1 = (if (ok && SZ.lt 1sz mlen) then 1sz else 0sz);
  let i2 = (if (ok && SZ.lt 2sz mlen) then 2sz else 0sz);
  let i3 = (if (ok && SZ.lt 3sz mlen) then 3sz else 0sz);
  let b0 = inp.(i0);
  let b1 = inp.(i1);
  let b2 = inp.(i2);
  let b3 = inp.(i3);
  let is_get =
    ok && SZ.eq mlen 3sz &&
    U8.eq b0 0x47uy && U8.eq b1 0x45uy && U8.eq b2 0x54uy;
  let is_head =
    ok && SZ.eq mlen 4sz &&
    U8.eq b0 0x48uy && U8.eq b1 0x45uy && U8.eq b2 0x41uy && U8.eq b3 0x44uy;
  let is_post =
    ok && SZ.eq mlen 4sz &&
    U8.eq b0 0x50uy && U8.eq b1 0x4Fuy && U8.eq b2 0x53uy && U8.eq b3 0x54uy;
  is_get || is_head || is_post
}
