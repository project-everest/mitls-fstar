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
module Resp = HTTP.Impl.Codec.Response

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
  decreases %[(if !go then 1 else 0); Prims.op_Subtraction (SZ.v n) (SZ.v (!pos))]
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

(* Case-insensitive equality of `inp[pos .. pos+nm_len)` and `nm[0 .. nm_len)`.
   Both sides are lowercased so the target `nm` need not be pre-normalised.
   Returns false (safely) if the input is too short.  Memory-safe only — a
   straight-line `stt` block in the `match_ci_at` idiom (the length check is
   folded into the `ok` accumulator so the `while` runs unconditionally, dodging
   the stt/stt_div divergent-block join). *)
fn ci_eq_at
  (inp: array U8.t) (n: SZ.t) (pos: SZ.t) (nm: array U8.t) (nm_len: SZ.t)
  requires
    pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v pos <= SZ.v n /\ SZ.v nm_len <= Seq.length 'm)
  returns b: bool
  ensures pts_to inp 'i ** pts_to nm 'm ** pure (SZ.v n <= Seq.length 'i)
{
  let mut k  = 0sz;
  let mut ok = true;
  if SZ.lt (SZ.sub n pos) nm_len {
    ok := false;
  };
  while (SZ.lt !k nm_len && !ok)
  invariant exists* (vk:SZ.t) (vok:bool).
    R.pts_to k vk ** R.pts_to ok vok ** pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v vk <= SZ.v nm_len /\ SZ.v n <= Seq.length 'i /\
          SZ.v nm_len <= Seq.length 'm /\
          (vok ==> SZ.v pos + SZ.v nm_len <= SZ.v n))
  decreases (Prims.op_Subtraction (SZ.v nm_len) (SZ.v (!k)))
  {
    let vk = !k;
    let c = inp.(SZ.add pos vk);
    let e = nm.(vk);
    ok := U8.eq (Resp.to_lower c) (Resp.to_lower e);
    k := SZ.add vk 1sz;
  };
  !ok
}

(* Find the first header field-line in `inp[0..n)` whose field-name equals `nm`
   (case-insensitive, exact length `nm_len`) and report its field-value slice.
   On success `pfound := true`, `pvoff`/`pvlen` delimit the value bytes
   `inp[voff .. voff+vlen)` (in bounds, from the leaf's postcondition); on
   failure (terminator, malformed line, no match, or no forward progress)
   `pfound := false`.  Memory-safe. *)
fn http_find_header
  (inp: array U8.t) (n: SZ.t) (nm: array U8.t) (nm_len: SZ.t)
  (pfound: R.ref bool) (pvoff: R.ref SZ.t) (pvlen: R.ref SZ.t)
  requires
    pts_to inp 'i ** pts_to nm 'm **
    R.pts_to pfound 'f0 ** R.pts_to pvoff 'o0 ** R.pts_to pvlen 'l0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v nm_len <= Seq.length 'm)
  ensures
    pts_to inp 'i ** pts_to nm 'm **
    (exists* (found:bool) (voff vlen:SZ.t).
       R.pts_to pfound found ** R.pts_to pvoff voff ** R.pts_to pvlen vlen **
       pure (found == true ==> SZ.v voff + SZ.v vlen <= SZ.v n))
{
  let mut pos     = 0sz;
  let mut go      = true;
  let mut pis_end = false;
  let mut pok     = false;
  let mut pnlen   = 0sz;
  let mut voffr   = 0sz;
  let mut vlenr   = 0sz;
  let mut pnext   = 0sz;
  pfound := false;
  while (!go)
  invariant exists* (vpos:SZ.t) (vgo ve vok vfound:bool) (a e1 e2 d vo vl:SZ.t).
    R.pts_to pos vpos ** R.pts_to go vgo ** R.pts_to pis_end ve ** R.pts_to pok vok **
    R.pts_to pnlen a ** R.pts_to voffr e1 ** R.pts_to vlenr e2 ** R.pts_to pnext d **
    R.pts_to pfound vfound ** R.pts_to pvoff vo ** R.pts_to pvlen vl **
    pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v vpos <= SZ.v n /\ SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\
          SZ.v nm_len <= Seq.length 'm /\
          (vfound == true ==> SZ.v vo + SZ.v vl <= SZ.v n))
  decreases %[(if !go then 1 else 0); Prims.op_Subtraction (SZ.v n) (SZ.v (!pos))]
  {
    let vpos = !pos;
    Hdr.http_parse_header_field inp n vpos pis_end pok pnlen voffr vlenr pnext;
    let isend = !pis_end;
    let ok = !pok;
    if (isend || not ok) {
      go := false;
    } else {
      let nlen = !pnlen;
      let voff = !voffr;
      let vlen = !vlenr;
      let nx   = !pnext;
      let lenmatch  = SZ.eq nlen nm_len;
      let bytematch = ci_eq_at inp n vpos nm nm_len;
      if (lenmatch && bytematch) {
        pfound := true;
        pvoff  := voff;
        pvlen  := vlen;
        go     := false;
      } else {
        if SZ.gt nx vpos {
          pos := nx;
        } else {
          go := false;
        }
      }
    }
  }
}

(* Look up a header by name via the general field iterator and parse its value
   as a decimal, re-expressing the Content-Length lookup on top of the header
   model rather than a bespoke whitelist scan.  `pfound := true` iff a matching
   header line was found; `pval` then holds the decimal value of its value slice
   (clamped by the verified `parse_dec_at`; 0 when the header is absent or its
   value has no leading digits).  Memory-safe. *)
fn http_header_dec
  (inp: array U8.t) (n: SZ.t) (nm: array U8.t) (nm_len: SZ.t)
  (pfound: R.ref bool) (pval: R.ref FStar.UInt32.t)
  requires
    pts_to inp 'i ** pts_to nm 'm **
    R.pts_to pfound 'f0 ** R.pts_to pval 'v0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v nm_len <= Seq.length 'm)
  ensures
    pts_to inp 'i ** pts_to nm 'm **
    (exists* (found:bool) (v:FStar.UInt32.t).
       R.pts_to pfound found ** R.pts_to pval v)
{
  let mut voffr = 0sz;
  let mut vlenr = 0sz;
  pval := 0ul;
  http_find_header inp n nm nm_len pfound voffr vlenr;
  let found = !pfound;
  if found {
    let voff = !voffr;
    let _numeric = Resp.parse_dec_at inp n voff pval;
    ()
  }
}

(* Enumerate every header field-line in `inp[0..n)` into four caller-provided,
   parallel output arrays of capacity `cap`: record `k` is
     name  = inp[noff[k] .. noff[k]+nlen[k]),
     value = inp[voff[k] .. voff[k]+vlen[k]).
   `pcount` receives the number of records written (<= cap).  Enumeration stops
   at the terminating empty CRLF, the first malformed line, when the output is
   full, or if a line fails to advance the cursor.  Memory-safe; each recorded
   field is proved correct per-line by the leaf `http_parse_header_field`. *)
fn http_parse_headers
  (inp: array U8.t) (n: SZ.t) (cap: SZ.t)
  (noff: array SZ.t) (nlen: array SZ.t) (voff: array SZ.t) (vlen: array SZ.t)
  (pcount: R.ref SZ.t)
  requires
    pts_to inp 'i ** pts_to noff 'no ** pts_to nlen 'nl **
    pts_to voff 'vo ** pts_to vlen 'vl ** R.pts_to pcount 'c0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v cap < pow2 32 /\
          Seq.length 'no == SZ.v cap /\ Seq.length 'nl == SZ.v cap /\
          Seq.length 'vo == SZ.v cap /\ Seq.length 'vl == SZ.v cap)
  ensures
    pts_to inp 'i **
    (exists* (no nl vo vl:Seq.seq SZ.t) (count:SZ.t).
       pts_to noff no ** pts_to nlen nl ** pts_to voff vo ** pts_to vlen vl **
       R.pts_to pcount count **
       pure (SZ.v count <= SZ.v cap))
{
  let mut pos     = 0sz;
  let mut cnt     = 0sz;
  let mut go      = true;
  let mut pis_end = false;
  let mut pok     = false;
  let mut pnl     = 0sz;
  let mut voffr   = 0sz;
  let mut vlenr   = 0sz;
  let mut pnext   = 0sz;
  while (!go)
  invariant exists* (vpos vcnt:SZ.t) (vgo ve vok:bool) (a e1 e2 d:SZ.t)
                    (no nl vo vl:Seq.seq SZ.t).
    R.pts_to pos vpos ** R.pts_to cnt vcnt ** R.pts_to go vgo **
    R.pts_to pis_end ve ** R.pts_to pok vok **
    R.pts_to pnl a ** R.pts_to voffr e1 ** R.pts_to vlenr e2 ** R.pts_to pnext d **
    pts_to inp 'i ** pts_to noff no ** pts_to nlen nl **
    pts_to voff vo ** pts_to vlen vl **
    pure (SZ.v vpos <= SZ.v n /\ SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\
          SZ.v vcnt <= SZ.v cap /\ SZ.v cap < pow2 32 /\
          Seq.length no == SZ.v cap /\ Seq.length nl == SZ.v cap /\
          Seq.length vo == SZ.v cap /\ Seq.length vl == SZ.v cap)
  decreases %[(if !go then 1 else 0); Prims.op_Subtraction (SZ.v n) (SZ.v (!pos))]
  {
    let vpos = !pos;
    let vcnt = !cnt;
    if (SZ.gte vcnt cap) {
      go := false;
    } else {
      Hdr.http_parse_header_field inp n vpos pis_end pok pnl voffr vlenr pnext;
      let isend = !pis_end;
      let ok = !pok;
      if (isend || not ok) {
        go := false;
      } else {
        let nl_ = !pnl;
        let vo_ = !voffr;
        let vl_ = !vlenr;
        let nx  = !pnext;
        noff.(vcnt) <- vpos;
        nlen.(vcnt) <- nl_;
        voff.(vcnt) <- vo_;
        vlen.(vcnt) <- vl_;
        Hdr.lemma_fits32 (SZ.v vcnt + 1);
        cnt := SZ.add vcnt 1sz;
        if SZ.gt nx vpos {
          pos := nx;
        } else {
          go := false;
        }
      }
    }
  };
  pcount := !cnt;
}

(* ── Request-framing validation (RFC 7230 §3.3.3 anti-smuggling) ───────────────

   Two verified helpers used by the server before it acts on a request's framing:

   `http_count_header_named` counts the well-formed header field-lines in
   `inp[0..n)` whose field-name equals `nm` (case-insensitive, exact length
   `nm_len`) — the name-filtered analogue of `http_count_headers`.  Memory-safe;
   the count is bounded by `n` because every counted line strictly advances the
   cursor.

   `http_request_framing_ok` applies the anti-smuggling policy on top of it: a
   request head is UNAMBIGUOUS (returns `true`) unless it carries a
   `Content-Length` alongside a `Transfer-Encoding`, or more than one
   `Content-Length` line — both of which are request-smuggling vectors that a
   conformant server must reject (with `400`).  Memory-safe. *)
fn http_count_header_named
  (inp: array U8.t) (n: SZ.t) (nm: array U8.t) (nm_len: SZ.t)
  requires
    pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v nm_len <= Seq.length 'm)
  returns _cnt:SZ.t
  ensures
    pts_to inp 'i ** pts_to nm 'm
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
    pts_to inp 'i ** pts_to nm 'm **
    pure (SZ.v vpos <= SZ.v n /\ SZ.v vcnt <= SZ.v vpos /\
          SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\ SZ.v nm_len <= Seq.length 'm)
  decreases %[(if !go then 1 else 0); Prims.op_Subtraction (SZ.v n) (SZ.v (!pos))]
  {
    let vpos = !pos;
    Hdr.http_parse_header_field inp n vpos pis_end pok pnlen pvoff pvlen pnext;
    let isend = !pis_end;
    let ok = !pok;
    if (isend || not ok) {
      go := false;
    } else {
      let nlen = !pnlen;
      let nx   = !pnext;
      let lenmatch  = SZ.eq nlen nm_len;
      let bytematch = ci_eq_at inp n vpos nm nm_len;
      if (SZ.gt nx vpos) {
        if (lenmatch && bytematch) {
          let vcnt = !cnt;
          Hdr.lemma_fits32 (SZ.v vcnt + 1);
          cnt := SZ.add vcnt 1sz;
          pos := nx;
        } else {
          pos := nx;
        }
      } else {
        go := false;
      }
    }
  };
  !cnt
}

fn http_request_framing_ok
  (inp: array U8.t) (n: SZ.t)
  (cl: array U8.t) (cl_len: SZ.t)
  (te: array U8.t) (te_len: SZ.t)
  requires
    pts_to inp 'i ** pts_to cl 'c ** pts_to te 't **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32 /\
          SZ.v cl_len <= Seq.length 'c /\ SZ.v te_len <= Seq.length 't)
  returns b: bool
  ensures
    pts_to inp 'i ** pts_to cl 'c ** pts_to te 't
{
  let clc = http_count_header_named inp n cl cl_len;
  let tec = http_count_header_named inp n te te_len;
  let cl_dup    = SZ.gt clc 1sz;
  let cl_and_te = SZ.gt clc 0sz && SZ.gt tec 0sz;
  not (cl_dup || cl_and_te)
}

(* ── Header-block limit enforcement (DoS defense) ─────────────────────────────

   Walk the header block `inp[0..n)` field-line by field-line and report whether
   it stays within the caller-supplied limits: at most `max_headers` field-lines,
   and no single field-line longer than `max_line` bytes (its length is the
   cursor advance `next - pos`, i.e. the whole line up to and including its CRLF).
   Returns `false` as soon as either bound is exceeded — a server answers `431
   Request Header Fields Too Large`.  Memory-safe; the walk terminates because
   every counted line strictly advances the cursor (lexicographic measure on the
   `go` flag then the remaining bytes). *)
fn http_header_limits_ok
  (inp: array U8.t) (n: SZ.t) (max_headers: SZ.t) (max_line: SZ.t)
  requires
    pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  returns b: bool
  ensures
    pts_to inp 'i
{
  let mut pos     = 0sz;
  let mut cnt     = 0sz;
  let mut bad     = false;
  let mut go      = true;
  let mut pis_end = false;
  let mut pok     = false;
  let mut pnlen   = 0sz;
  let mut pvoff   = 0sz;
  let mut pvlen   = 0sz;
  let mut pnext   = 0sz;
  while (!go)
  invariant exists* (vpos vcnt:SZ.t) (vgo vbad ve vok:bool) (a b c d:SZ.t).
    R.pts_to pos vpos ** R.pts_to cnt vcnt ** R.pts_to bad vbad ** R.pts_to go vgo **
    R.pts_to pis_end ve ** R.pts_to pok vok **
    R.pts_to pnlen a ** R.pts_to pvoff b ** R.pts_to pvlen c ** R.pts_to pnext d **
    pts_to inp 'i **
    pure (SZ.v vpos <= SZ.v n /\ SZ.v vcnt <= SZ.v vpos /\
          SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  decreases %[(if !go then 1 else 0); Prims.op_Subtraction (SZ.v n) (SZ.v (!pos))]
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
        let vcnt = !cnt;
        Hdr.lemma_fits32 (SZ.v vcnt + 1);
        let ncnt = SZ.add vcnt 1sz;
        cnt := ncnt;
        let linelen   = SZ.sub nx vpos;
        let overline  = SZ.gt linelen max_line;
        let overcount = SZ.gt ncnt max_headers;
        if (overline || overcount) {
          bad := true;
          pos := nx;
          go  := false;
        } else {
          pos := nx;
        }
      } else {
        go := false;
      }
    }
  };
  not !bad
}
