module HTTP.Impl.Codec.Response

#lang-pulse

(**
  Verified Pulse parsers for a *real* origin-server HTTP/1.1 response head, as
  produced by an external web server (e.g. the reply to GET http://example.com/):

    "HTTP/1.1 " ddd " " reason-phrase CRLF
    (header-name ": " header-value CRLF)*
    CRLF
    <body>

  Real responses carry a variable, unordered set of headers, so — unlike the
  fixed 43-byte head handled by HTTP.Impl.Codec.Length.http_recv_response — this
  is a *scanning* parser.  We only ever PARSE server responses (never emit
  them), so, like the request-recv leaf, the deliverable is a memory-safe parser
  that extracts what the client needs to frame the body:

    * the numeric status code (proved to equal `W.dec_dec3` of bytes 9..11), and
    * the body framing: Content-Length n, Transfer-Encoding: chunked, or
      read-to-EOF (Connection: close with no length).

  All array reads are proved in-bounds by the Pulse VC; the framing scanners
  additionally return the concrete facts (matched header position / parsed
  value) that they establish while walking the buffer.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module Cast = FStar.Int.Cast
module R    = Pulse.Lib.Reference
module W    = HTTP.Wire.Common

(* ── Status line ───────────────────────────────────────────────────────────────

   Parse the status line prefix "HTTP/1.1 " (9 bytes) + 3-digit status code +
   a separating space.  On success `pcode` holds the code and we prove it equals
   the spec decode `W.dec_dec3` of the three code bytes (positions 9..11).       *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
fn http_parse_status_line (inp: array U8.t) (n: SZ.t) (pcode: R.ref U16.t)
  requires
    pts_to inp 'i ** R.pts_to pcode 'c0 **
    pure (Seq.length 'i == SZ.v n)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (cv:U16.t).
       R.pts_to pcode cv **
       pure (ok == true ==>
         (Seq.length 'i == SZ.v n /\ 13 <= SZ.v n /\
          100 <= U16.v cv /\ U16.v cv < 1000 /\
          W.dec3_ok (Seq.slice 'i 9 12) /\
          Prims.op_Equality #nat (U16.v cv) (W.dec_dec3 (Seq.slice 'i 9 12)))))
{
  if SZ.lt n 13sz {
    false
  } else {
    let p0 = inp.(0sz); let p1 = inp.(1sz); let p2 = inp.(2sz);
    let p3 = inp.(3sz); let p4 = inp.(4sz); let p5 = inp.(5sz);
    let p6 = inp.(6sz); let p7 = inp.(7sz); let p8 = inp.(8sz);
    let pref_ok =
      U8.eq p0 0x48uy && U8.eq p1 0x54uy && U8.eq p2 0x54uy && U8.eq p3 0x50uy &&
      U8.eq p4 0x2Fuy && U8.eq p5 0x31uy && U8.eq p6 0x2Euy && U8.eq p7 0x31uy &&
      U8.eq p8 0x20uy;
    let b9  = inp.(9sz);  let b10 = inp.(10sz);
    let b11 = inp.(11sz); let b12 = inp.(12sz);
    let dok = W.is_dec b9 && W.is_dec b10 && W.is_dec b11;
    let sp_ok = U8.eq b12 0x20uy;
    if (pref_ok && dok && sp_ok) {
      let c9  = Cast.uint8_to_uint16 (U8.sub b9  0x30uy);
      let c10 = Cast.uint8_to_uint16 (U8.sub b10 0x30uy);
      let c11 = Cast.uint8_to_uint16 (U8.sub b11 0x30uy);
      let code = U16.add (U16.add (U16.mul 100us c9) (U16.mul 10us c10)) c11;
      if (U16.lte 100us code && U16.lt code 1000us) {
        Seq.lemma_index_slice ('i <: Seq.seq U8.t) 9 12 0;
        Seq.lemma_index_slice ('i <: Seq.seq U8.t) 9 12 1;
        Seq.lemma_index_slice ('i <: Seq.seq U8.t) 9 12 2;
        pcode := code;
        true
      } else {
        false
      }
    } else {
      false
    }
  }
}
#pop-options

(* ── Case-insensitive header-name matching ─────────────────────────────────────

   Lowercasing folds ASCII 'A'..'Z' to 'a'..'z'; other bytes pass through.
   Header field-names are case-insensitive per RFC 9110, so we match against a
   lowercase literal delivered by a pure byte dispatcher.                        *)

let to_lower (b:U8.t) : U8.t =
  if U8.lte 0x41uy b && U8.lte b 0x5Auy then U8.add b 0x20uy else b

(* Match `len` lowercased bytes of `inp` starting at `pos` against the literal
   produced by `name_byte`.  Purely a bounds-checked scan (memory-safe). *)
fn match_ci_at
  (inp: array U8.t) (n: SZ.t) (pos: SZ.t) (len: SZ.t)
  (name_byte: (k:SZ.t) -> U8.t)
  requires pts_to inp 'i ** pure (Seq.length 'i == SZ.v n /\ SZ.v pos <= SZ.v n)
  returns b: bool
  ensures pts_to inp 'i ** pure (Seq.length 'i == SZ.v n)
{
  if SZ.lt (SZ.sub n pos) len {
    false
  } else {
    let mut k = 0sz;
    let mut ok = true;
    while (SZ.lt !k len && !ok)
    invariant exists* (vk:SZ.t) (vok:bool).
      R.pts_to k vk ** R.pts_to ok vok ** pts_to inp 'i **
      pure (SZ.v vk <= SZ.v len /\ Seq.length 'i == SZ.v n /\
            SZ.v pos + SZ.v len <= SZ.v n)
    {
      let vk = !k;
      let c = inp.(SZ.add pos vk);
      let e = name_byte vk;
      ok := U8.eq (to_lower c) e;
      k := SZ.add vk 1sz;
    };
    !ok
  }
}

module CW = HTTP.Wire.Common

(* size_t is >= 32 bits on every real target; the small index sums vi+k here can
   exceed F*'s SizeT 2^16 auto-`fits` line, so discharge sub-2^32 `fits`
   explicitly (same open assumption as the other HTTP impl leaves). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x

(* Lowercase literal byte dispatchers (default 0uy outside range). *)
let cl_name_byte (k:SZ.t) : U8.t =
  if      SZ.eq k 0sz  then 0x63uy else if SZ.eq k 1sz  then 0x6Fuy
  else if SZ.eq k 2sz  then 0x6Euy else if SZ.eq k 3sz  then 0x74uy
  else if SZ.eq k 4sz  then 0x65uy else if SZ.eq k 5sz  then 0x6Euy
  else if SZ.eq k 6sz  then 0x74uy else if SZ.eq k 7sz  then 0x2Duy
  else if SZ.eq k 8sz  then 0x6Cuy else if SZ.eq k 9sz  then 0x65uy
  else if SZ.eq k 10sz then 0x6Euy else if SZ.eq k 11sz then 0x67uy
  else if SZ.eq k 12sz then 0x74uy else if SZ.eq k 13sz then 0x68uy
  else if SZ.eq k 14sz then 0x3Auy else 0x00uy

let te_name_byte (k:SZ.t) : U8.t =
  if      SZ.eq k 0sz  then 0x74uy else if SZ.eq k 1sz  then 0x72uy
  else if SZ.eq k 2sz  then 0x61uy else if SZ.eq k 3sz  then 0x6Euy
  else if SZ.eq k 4sz  then 0x73uy else if SZ.eq k 5sz  then 0x66uy
  else if SZ.eq k 6sz  then 0x65uy else if SZ.eq k 7sz  then 0x72uy
  else if SZ.eq k 8sz  then 0x2Duy else if SZ.eq k 9sz  then 0x65uy
  else if SZ.eq k 10sz then 0x6Euy else if SZ.eq k 11sz then 0x63uy
  else if SZ.eq k 12sz then 0x6Fuy else if SZ.eq k 13sz then 0x64uy
  else if SZ.eq k 14sz then 0x69uy else if SZ.eq k 15sz then 0x6Euy
  else if SZ.eq k 16sz then 0x67uy else if SZ.eq k 17sz then 0x3Auy else 0x00uy

let chunked_byte (k:SZ.t) : U8.t =
  if      SZ.eq k 0sz then 0x63uy else if SZ.eq k 1sz then 0x68uy
  else if SZ.eq k 2sz then 0x75uy else if SZ.eq k 3sz then 0x6Euy
  else if SZ.eq k 4sz then 0x6Buy else if SZ.eq k 5sz then 0x65uy
  else if SZ.eq k 6sz then 0x64uy else 0x00uy

(* Parse a decimal value at `start` (after skipping OWS spaces), clamped to
   < max_len8.  Memory-safe; returns whether any digit was read. *)
fn parse_dec_at (inp: array U8.t) (n: SZ.t) (start: SZ.t) (pval: R.ref U32.t)
  requires
    pts_to inp 'i ** R.pts_to pval 'v0 **
    pure (Seq.length 'i == SZ.v n /\ SZ.v start <= SZ.v n)
  returns found: bool
  ensures
    pts_to inp 'i **
    (exists* (v:U32.t). R.pts_to pval v ** pure (U32.v v < CW.max_len8))
{
  (* skip optional leading spaces *)
  let mut j = start;
  let mut sgo = true;
  while (!sgo)
  invariant exists* (vj:SZ.t) (vs:bool).
    R.pts_to j vj ** R.pts_to sgo vs ** pts_to inp 'i **
    pure (SZ.v vj <= SZ.v n /\ Seq.length 'i == SZ.v n)
  {
    let vj = !j;
    if SZ.lt vj n {
      let c = inp.(vj);
      if U8.eq c 0x20uy { j := SZ.add vj 1sz } else { sgo := false }
    } else { sgo := false }
  };
  (* read decimal digits, clamp at 99_999_999 *)
  let mut acc = 0ul;
  let mut any = false;
  let mut dgo = true;
  while (!dgo)
  invariant exists* (vj:SZ.t) (va:U32.t) (vy:bool) (vg:bool).
    R.pts_to j vj ** R.pts_to acc va ** R.pts_to any vy ** R.pts_to dgo vg **
    pts_to inp 'i **
    pure (SZ.v vj <= SZ.v n /\ Seq.length 'i == SZ.v n /\ U32.v va < CW.max_len8)
  {
    let vj = !j;
    if SZ.lt vj n {
      let c = inp.(vj);
      if CW.is_dec c {
        let d = Cast.uint8_to_uint32 (U8.sub c 0x30uy);
        let na = U32.add (U32.mul !acc 10ul) d;
        if U32.lt na 100000000ul { acc := na } else { acc := 99999999ul };
        any := true;
        j := SZ.add vj 1sz;
      } else { dgo := false }
    } else { dgo := false }
  };
  pval := !acc;
  !any
}

(* Scan the current header line (from `start` up to CRLF or `n`) for a
   case-insensitive "chunked" token.  Memory-safe. *)
fn line_has_chunked (inp: array U8.t) (n: SZ.t) (start: SZ.t)
  requires pts_to inp 'i ** pure (Seq.length 'i == SZ.v n /\ SZ.v start <= SZ.v n)
  returns b: bool
  ensures pts_to inp 'i ** pure (Seq.length 'i == SZ.v n)
{
  let mut j = start;
  let mut found = false;
  let mut go = true;
  while (!go)
  invariant exists* (vj:SZ.t) (vf:bool) (vg:bool).
    R.pts_to j vj ** R.pts_to found vf ** R.pts_to go vg ** pts_to inp 'i **
    pure (SZ.v vj <= SZ.v n /\ Seq.length 'i == SZ.v n)
  {
    let vj = !j;
    if SZ.lt vj n {
      let c = inp.(vj);
      if U8.eq c 0x0Duy {
        go := false
      } else {
        let m = match_ci_at inp n vj 7sz chunked_byte;
        if m { found := true; go := false } else { j := SZ.add vj 1sz }
      }
    } else { go := false }
  };
  !found
}

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
fn try_content_length
  (inp: array U8.t) (n: SZ.t) (vi: SZ.t)
  (phas_cl: R.ref bool) (pcl: R.ref U32.t)
  requires
    pts_to inp 'i ** R.pts_to phas_cl 'hc0 ** R.pts_to pcl 'cl0 **
    pure (Seq.length 'i == SZ.v n /\ SZ.v vi <= SZ.v n /\ SZ.v n + 18 < pow2 32 /\
          U32.v 'cl0 < CW.max_len8)
  ensures
    pts_to inp 'i **
    (exists* (hc:bool) (cl:U32.t).
       R.pts_to phas_cl hc ** R.pts_to pcl cl ** pure (U32.v cl < CW.max_len8))
{
  lemma_fits32 (SZ.v vi + 15);
  if SZ.lte (SZ.add vi 15sz) n {
    let mcl = match_ci_at inp n vi 15sz cl_name_byte;
    if mcl {
      let _ = parse_dec_at inp n (SZ.add vi 15sz) pcl;
      phas_cl := true;
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
fn try_transfer_encoding
  (inp: array U8.t) (n: SZ.t) (vi: SZ.t) (pchunked: R.ref bool)
  requires
    pts_to inp 'i ** R.pts_to pchunked 'ch0 **
    pure (Seq.length 'i == SZ.v n /\ SZ.v vi <= SZ.v n /\ SZ.v n + 18 < pow2 32)
  ensures
    pts_to inp 'i ** (exists* (ch:bool). R.pts_to pchunked ch)
{
  lemma_fits32 (SZ.v vi + 18);
  if SZ.lte (SZ.add vi 18sz) n {
    let mte = match_ci_at inp n vi 18sz te_name_byte;
    if mte {
      let hc = line_has_chunked inp n (SZ.add vi 18sz);
      if hc { pchunked := true } else { () }
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

(* ── Framing scanner ───────────────────────────────────────────────────────────

   Walk the response header block line by line (each header line starts right
   after a CRLF; the status line is line 0).  At each header-line start, match
   the two framing-relevant header names case-insensitively:

     * "Content-Length:" -> parse the decimal value into `pcl`, set `phas_cl`;
     * "Transfer-Encoding:" -> if the value contains "chunked", set `pchunked`.

   Returns whether the empty-line header terminator (CRLF at a line start) was
   seen.  Memory-safe: every array read is proved in-bounds, and the parsed
   Content-Length is clamped < max_len8.  (Precondition `SZ.v n < pow2 32` — a
   header block never approaches 4 GiB — keeps the small index sums in SizeT.)   *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
fn is_crlf_at (inp: array U8.t) (n: SZ.t) (vi: SZ.t)
  requires pts_to inp 'i ** pure (Seq.length 'i == SZ.v n /\ SZ.v vi < SZ.v n)
  returns b: bool
  ensures pts_to inp 'i **
    pure (Seq.length 'i == SZ.v n /\ (b == true ==> SZ.v vi + 1 < SZ.v n))
{
  if SZ.lt (SZ.add vi 1sz) n {
    let a = inp.(vi);
    let b = inp.(SZ.add vi 1sz);
    U8.eq a 0x0Duy && U8.eq b 0x0Auy
  } else {
    false
  }
}

fn http_parse_framing
  (inp: array U8.t) (n: SZ.t)
  (pchunked: R.ref bool) (phas_cl: R.ref bool) (pcl: R.ref U32.t)
  requires
    pts_to inp 'i **
    R.pts_to pchunked 'ch0 ** R.pts_to phas_cl 'hc0 ** R.pts_to pcl 'cl0 **
    pure (Seq.length 'i == SZ.v n /\ SZ.v n + 18 < pow2 32)
  returns ended: bool
  ensures
    pts_to inp 'i **
    (exists* (ch:bool) (hc:bool) (cl:U32.t).
       R.pts_to pchunked ch ** R.pts_to phas_cl hc ** R.pts_to pcl cl **
       pure (U32.v cl < CW.max_len8))
{
  let mut i = 0sz;
  let mut sol = false;     (* is index i the start of a header line? *)
  let mut ended = false;
  pchunked := false;
  phas_cl  := false;
  pcl      := 0ul;
  while (SZ.lt !i n && not !ended)
  invariant exists* (vi:SZ.t) (vsol:bool) (ve:bool) (ch:bool) (hc:bool) (cl:U32.t).
    R.pts_to i vi ** R.pts_to sol vsol ** R.pts_to ended ve **
    R.pts_to pchunked ch ** R.pts_to phas_cl hc ** R.pts_to pcl cl **
    pts_to inp 'i **
    pure (SZ.v vi <= SZ.v n /\ Seq.length 'i == SZ.v n /\ SZ.v n + 18 < pow2 32 /\
          U32.v cl < CW.max_len8)
  {
    let vi = !i;
    let vsol = !sol;
    lemma_fits32 (SZ.v vi + 2);
    lemma_fits32 (SZ.v vi + 15);
    lemma_fits32 (SZ.v vi + 18);
    (* is there a CRLF starting at vi? *)
    let crlf = is_crlf_at inp n vi;
    if crlf {
      if vsol {
        ended := true;              (* empty line at a line start: end of head *)
      } else {
        sol := true;                (* next line (at vi+2) is a header line *)
        i := SZ.add vi 2sz;
      }
    } else {
      if vsol {
        try_content_length inp n vi phas_cl pcl;
        try_transfer_encoding inp n vi pchunked;
        sol := false;
        i := SZ.add vi 1sz;
      } else {
        sol := false;
        i := SZ.add vi 1sz;
      }
    }
  };
  !ended
}
#pop-options

(* ── Combined response-head parser ─────────────────────────────────────────────

   Parse a full response head that already resides in `inp` (the client reads
   bytes until the CRLF-CRLF terminator, then calls this).  Composes the
   status-line parser and the framing scanner:

     * `pcode`    <- numeric status code (proved == W.dec_dec3 of bytes 9..11),
     * `pchunked` <- true iff a "Transfer-Encoding: chunked" header was seen,
     * `phas_cl`  <- true iff a "Content-Length:" header was seen,
     * `pcl`      <- the parsed Content-Length (clamped < max_len8).

   Body framing precedence (RFC 9112 §6): chunked wins over Content-Length; if
   neither is present the body runs to EOF (Connection: close).  Returns `ok` =
   the status line parsed AND the header terminator was found.                   *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
fn http_parse_response_head
  (inp: array U8.t) (n: SZ.t)
  (pcode: R.ref U16.t) (pchunked: R.ref bool) (phas_cl: R.ref bool) (pcl: R.ref U32.t)
  requires
    pts_to inp 'i **
    R.pts_to pcode 'c0 ** R.pts_to pchunked 'ch0 **
    R.pts_to phas_cl 'hc0 ** R.pts_to pcl 'cl0 **
    pure (Seq.length 'i == SZ.v n /\ SZ.v n + 18 < pow2 32)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (code:U16.t) (ch:bool) (hc:bool) (cl:U32.t).
       R.pts_to pcode code ** R.pts_to pchunked ch **
       R.pts_to phas_cl hc ** R.pts_to pcl cl **
       pure (U32.v cl < CW.max_len8 /\
         (ok == true ==>
           (Seq.length 'i == SZ.v n /\ 13 <= SZ.v n /\
            100 <= U16.v code /\ U16.v code < 1000 /\
            CW.dec3_ok (Seq.slice 'i 9 12) /\
            Prims.op_Equality #nat (U16.v code) (CW.dec_dec3 (Seq.slice 'i 9 12))))))
{
  let sok = http_parse_status_line inp n pcode;
  if sok {
    let ended = http_parse_framing inp n pchunked phas_cl pcl;
    ended
  } else {
    pchunked := false;
    phas_cl  := false;
    pcl      := 0ul;
    false
  }
}
#pop-options
