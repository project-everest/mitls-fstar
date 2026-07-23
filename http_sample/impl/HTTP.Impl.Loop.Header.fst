module HTTP.Impl.Loop.Header

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** driver that exercises the verified single-line
  header parser `HTTP.Impl.Codec.Header.http_parse_header_field` in a loop,
  mirroring the scanning-driver idiom of the other `HTTP.Impl.*.Loop.*` modules.

  `http_count_headers` walks a header block field-by-field starting at offset 0:
  it repeatedly parses one field-line, advances past it, and counts it, stopping
  at the terminating empty CRLF (`is_end`), at the first malformed line, or if a
  parse fails to make forward progress.  It returns the number of well-formed
  header field-lines seen before the terminator.

  Its real job is twofold: (1) it is a genuine, useful consumer of the leaf
  (counting headers), and (2) by calling the leaf from a top-level driver it
  keeps `http_parse_header_field` reachable through KaRaMeL's dead-code
  elimination so the leaf is exported into the `HTTP_Verified` C bundle for the
  `header_parse_test` harness to drive directly.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ  = FStar.SizeT
module Seq = FStar.Seq
module U8  = FStar.UInt8
module R   = Pulse.Lib.Reference
module Hdr = HTTP.Impl.Codec.Header

open Pulse.Lib.BoundedIntegers

(* Count the well-formed header field-lines in `inp[0..n)` up to (and not
   including) the terminating empty CRLF.  Memory-safe; the returned count is
   bounded by `n` because every counted line strictly advances the cursor. *)
fn http_count_headers (inp: array U8.t) (n: SZ.t)
  requires
    pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  returns _cnt:SZ.t
  ensures
    pts_to inp 'i
{
  let mut pos     = 0sz;
  let mut cnt     = 0sz;
  let mut go      = true;
  let mut pis_end = false;
  let mut pok     = false;
  let mut pnlen   = 0sz;
  let mut pvoff   = 0sz;
  let mut pvlen   = 0sz;
  let mut pnext   = 0sz;
  while (!go)
  invariant exists* (vpos vcnt:SZ.t) (vgo ve vok:bool) (a b c d:SZ.t).
    R.pts_to pos vpos ** R.pts_to cnt vcnt ** R.pts_to go vgo **
    R.pts_to pis_end ve ** R.pts_to pok vok **
    R.pts_to pnlen a ** R.pts_to pvoff b ** R.pts_to pvlen c ** R.pts_to pnext d **
    pts_to inp 'i **
    pure (SZ.v vpos <= SZ.v n /\ SZ.v vcnt <= SZ.v vpos /\
          SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  {
    let vpos = !pos;
    Hdr.http_parse_header_field inp n vpos pis_end pok pnlen pvoff pvlen pnext;
    let isend = !pis_end;
    let ok = !pok;
    if (isend || not ok) {
      go := false;
    } else {
      let nx = !pnext;
      if (SZ.gt nx vpos) {
        pos := nx;
        let vcnt = !cnt;
        Hdr.lemma_fits32 (SZ.v vcnt + 1);
        cnt := SZ.add vcnt 1sz;
      } else {
        go := false;
      }
    }
  };
  !cnt
}
