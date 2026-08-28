module HTTP.Impl.Codec.Header

#lang-pulse

(**
  Verified Pulse parser for a *single* HTTP/1.1 header field-line (RFC 9112 §5):

      field-line = field-name ":" OWS field-value OWS CRLF

  `http_parse_header_field` scans one header line out of a fixed, never-written
  buffer `inp` starting at `start`, indexing everything into the ghost sequence
  `'i`.  It is a *scanning* parser in the same idiom as
  `HTTP.Impl.Codec.Response.parse_dec_at`: four bounds-checked loops (an
  end-of-headers check, a name scan, an OWS skip, and a value scan), each of
  which is proved memory-safe by the Pulse VC and each of which returns the
  concrete facts it establishes while walking the buffer.  On success we tie the
  imperative result to the pure spec `HTTP.Wire.Header.parse_field`.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module SP   = FStar.Seq.Properties
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module Cast = FStar.Int.Cast
module R    = Pulse.Lib.Reference
module W    = HTTP.Wire.Common
module H    = HTTP.Wire.Header

(* size_t is >= 32 bits on every real target; the small index sums here can
   exceed F*'s SizeT 2^16 auto-`fits` line, so discharge sub-2^32 `fits`
   explicitly (same open assumption as the other HTTP impl leaves). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x

(* `cj + 1` fits size_t whenever a colon was actually found (so `cj < n`). *)
let lemma_ok1_fits (start cj n:SZ.t) (foundc:bool)
  : Lemma (requires SZ.v n < pow2 32 /\ (foundc == true ==> SZ.v cj < SZ.v n))
          (ensures ((foundc && SZ.lt start cj) == true ==> FStar.SizeT.fits (SZ.v cj + 1)))
  = if foundc && SZ.lt start cj then lemma_fits32 (SZ.v cj + 1)

(* ── Pure bridging lemmas ─────────────────────────────────────────────────── *)

(* A slice splits into two adjacent slices. *)
let lemma_slice_split (s:Seq.seq U8.t) (a b c:nat)
  : Lemma (requires a <= b /\ b <= c /\ c <= Seq.length s)
          (ensures Seq.slice s a c == Seq.append (Seq.slice s a b) (Seq.slice s b c))
  = Seq.lemma_split (Seq.slice s a c) (b - a);
    Seq.slice_slice s a c 0 (b - a);
    Seq.slice_slice s a c (b - a) (c - a)

(* The converse of `H.lemma_all_name_index`: an all-`name_char` sequence is
   `all_name`. *)
#push-options "--fuel 2 --ifuel 1"
let rec lemma_all_name_of_forall (t:Seq.seq U8.t)
  : Lemma (requires (forall (i:nat). i < Seq.length t ==> H.name_char (Seq.index t i)))
          (ensures H.all_name t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      let tl = Seq.slice t 1 (Seq.length t) in
      assert (forall (i:nat). i < Seq.length tl ==> Seq.index tl i == Seq.index t (i + 1));
      lemma_all_name_of_forall tl
    end

let rec lemma_all_value_of_forall (t:Seq.seq U8.t)
  : Lemma (requires (forall (i:nat). i < Seq.length t ==> H.value_char (Seq.index t i)))
          (ensures H.all_value t)
          (decreases Seq.length t)
  = if Seq.length t = 0 then ()
    else begin
      let tl = Seq.slice t 1 (Seq.length t) in
      assert (forall (i:nat). i < Seq.length tl ==> Seq.index tl i == Seq.index t (i + 1));
      lemma_all_value_of_forall tl
    end
#pop-options

(* Analogue of `H.lemma_idx_of_run` for the leading OWS run: if every byte of
   `pre` is OWS and `rest` does not begin with OWS, the leading OWS run of
   `pre ++ rest` is exactly `Seq.length pre`. *)
let rec lemma_ows_run (pre rest:Seq.seq U8.t)
  : Lemma (requires (forall (i:nat). i < Seq.length pre ==> H.is_ows (Seq.index pre i)) /\
                    (Seq.length rest = 0 \/ not (H.is_ows (Seq.index rest 0))))
          (ensures H.ows_prefix_len (Seq.append pre rest) == Seq.length pre)
          (decreases Seq.length pre)
  = let s = Seq.append pre rest in
    if Seq.length pre = 0 then
      Seq.lemma_eq_intro s rest
    else begin
      let pre' = Seq.slice pre 1 (Seq.length pre) in
      Seq.lemma_eq_intro (Seq.slice s 1 (Seq.length s)) (Seq.append pre' rest);
      assert (Seq.index s 0 == Seq.index pre 0);
      assert (forall (i:nat). i < Seq.length pre' ==> Seq.index pre' i == Seq.index pre (i + 1));
      lemma_ows_run pre' rest
    end

(* ── Per-phase fact lemmas (kept in minimal context) ──────────────────────── *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let lemma_name_facts (s:Seq.seq U8.t) (start cj n:nat)
  : Lemma (requires start <= cj /\ cj < n /\ n <= Seq.length s /\
                    Seq.index s cj == H.bColon /\
                    (forall (k:nat). start <= k /\ k < cj ==> H.name_char (Seq.index s k)))
          (ensures
             H.idx_of (Seq.append (Seq.slice s start cj) (Seq.slice s cj n)) H.bColon == cj - start /\
             H.all_name (Seq.slice s start cj))
  = assert (forall (i:nat). i < Seq.length (Seq.slice s start cj) ==>
              H.name_char (Seq.index (Seq.slice s start cj) i));
    H.lemma_idx_of_run (Seq.slice s start cj) H.bColon (Seq.slice s cj n);
    lemma_all_name_of_forall (Seq.slice s start cj)

let lemma_ows_facts (s:Seq.seq U8.t) (cj voff n:nat)
  : Lemma (requires cj + 1 <= voff /\ voff <= n /\ n <= Seq.length s /\
                    (forall (p:nat). cj + 1 <= p /\ p < voff ==> H.is_ows (Seq.index s p)) /\
                    (voff < n ==> not (H.is_ows (Seq.index s voff))))
          (ensures
             H.ows_prefix_len (Seq.append (Seq.slice s (cj + 1) voff) (Seq.slice s voff n))
               == voff - (cj + 1))
  = assert (forall (i:nat). i < Seq.length (Seq.slice s (cj + 1) voff) ==>
              H.is_ows (Seq.index (Seq.slice s (cj + 1) voff) i));
    if voff < n then Seq.lemma_index_slice s voff n 0;
    lemma_ows_run (Seq.slice s (cj + 1) voff) (Seq.slice s voff n)

let lemma_value_facts (s:Seq.seq U8.t) (voff ei n:nat)
  : Lemma (requires voff <= ei /\ ei < n /\ n <= Seq.length s /\
                    Seq.index s ei == W.bCR /\
                    (forall (q:nat). voff <= q /\ q < ei ==> H.value_char (Seq.index s q)))
          (ensures
             H.idx_of (Seq.append (Seq.slice s voff ei) (Seq.slice s ei n)) W.bCR == ei - voff /\
             H.all_value (Seq.slice s voff ei))
  = assert (forall (i:nat). i < Seq.length (Seq.slice s voff ei) ==>
              H.value_char (Seq.index (Seq.slice s voff ei) i));
    H.lemma_idx_of_run (Seq.slice s voff ei) W.bCR (Seq.slice s ei n);
    lemma_all_value_of_forall (Seq.slice s voff ei)
#pop-options

(* ── The functional tie ───────────────────────────────────────────────────────

   Given the concrete facts established by the four scanning loops (colon at
   `cj`, all-`name_char` name, maximal OWS run ending at `voff`, first CR at
   `ei`, terminating LF at `ei+1`), `parse_field` of the suffix `s[start..n)`
   yields exactly `Some (name, value, consumed)`.                              *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let lemma_parse_field_tie
  (s:Seq.seq U8.t) (start n cj voff ei:nat)
  : Lemma
    (requires
      start <= n /\ n <= Seq.length s /\
      start < cj /\ cj < n /\ Seq.index s cj == H.bColon /\
      (forall (k:nat). start <= k /\ k < cj ==> H.name_char (Seq.index s k)) /\
      cj + 1 <= voff /\ voff <= n /\
      (forall (p:nat). cj + 1 <= p /\ p < voff ==> H.is_ows (Seq.index s p)) /\
      (voff < n ==> not (H.is_ows (Seq.index s voff))) /\
      voff <= ei /\ ei < n /\ Seq.index s ei == W.bCR /\
      (forall (q:nat). voff <= q /\ q < ei ==> H.value_char (Seq.index s q)) /\
      ei + 1 < n /\ Seq.index s (ei + 1) == W.bLF)
    (ensures
      H.parse_field (Seq.slice s start n) ==
        Some (Seq.slice s start cj, Seq.slice s voff ei, ei + 2 - start))
  = (* Work directly with `Seq.slice s start n` (the literal `input` of
       `parse_field`) so the `slice_slice` / `lemma_index_slice` SMTPats fire
       inside the unfolded `parse_field` VC. *)
    lemma_slice_split s start cj n;
    lemma_name_facts s start cj n;
    lemma_slice_split s (cj + 1) voff n;
    lemma_ows_facts s cj voff n;
    lemma_slice_split s voff ei n;
    lemma_value_facts s voff ei n;
    (* guide the unfolded `parse_field` step by step *)
    assert (H.idx_of (Seq.slice s start n) H.bColon == cj - start);
    assert (Seq.slice (Seq.slice s start n) 0 (cj - start) == Seq.slice s start cj);
    assert (H.all_name (Seq.slice s start cj));
    assert (Seq.slice (Seq.slice s start n) (cj - start + 1) (n - start) == Seq.slice s (cj + 1) n);
    assert (H.ows_prefix_len (Seq.slice s (cj + 1) n) == voff - (cj + 1));
    assert (Seq.slice (Seq.slice s start n) (voff - start) (n - start) == Seq.slice s voff n);
    assert (H.idx_of (Seq.slice s voff n) W.bCR == ei - voff);
    Seq.slice_slice s start n (voff - start) (ei - start);
    assert (Seq.slice (Seq.slice s start n) (voff - start) (ei - start) == Seq.slice s voff ei);
    assert (H.all_value (Seq.slice s voff ei));
    Seq.lemma_index_slice s start n (ei - start + 1);
    assert (Seq.index (Seq.slice s start n) (ei - start + 1) == Seq.index s (ei + 1))
#pop-options

(* ── Phase 1: end-of-headers check ────────────────────────────────────────────
   Return `true` iff the line at `start` is the empty CRLF that terminates the
   header block.  Expression-return so the fact threads per-branch.            *)
fn check_end (inp: array U8.t) (n: SZ.t) (start: SZ.t)
  requires pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v start <= SZ.v n /\ SZ.v n < pow2 32)
  returns b: bool
  ensures pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\
      (b == true ==>
      (SZ.v start + 2 <= SZ.v n /\
       Seq.index 'i (SZ.v start) == W.bCR /\
       Seq.index 'i (SZ.v start + 1) == W.bLF)))
{
  if SZ.lt start n {
    lemma_fits32 (SZ.v start + 1);
    let s1 = SZ.add start 1sz;
    if SZ.lt s1 n {
      let c0 = inp.(start);
      let c1 = inp.(s1);
      U8.eq c0 W.bCR && U8.eq c1 W.bLF
    } else { false }
  } else { false }
}

(* ── Phase 2: name scan ───────────────────────────────────────────────────────
   Scan `[start, cj)` of `name_char` bytes until the first colon.  Writes the
   colon position to `pcj` and returns whether a colon was found.             *)
fn scan_name (inp: array U8.t) (n: SZ.t) (start: SZ.t) (pcj: R.ref SZ.t)
  requires pts_to inp 'i ** R.pts_to pcj 'c0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v start <= SZ.v n /\ SZ.v n < pow2 32)
  returns foundc: bool
  ensures pts_to inp 'i **
    (exists* (cj:SZ.t). R.pts_to pcj cj **
      pure (SZ.v n <= Seq.length 'i /\
            SZ.v start <= SZ.v cj /\ SZ.v cj <= SZ.v n /\
            (forall (k:nat). SZ.v start <= k /\ k < SZ.v cj ==> H.name_char (Seq.index 'i k)) /\
            (foundc == true ==>
              (SZ.v cj < SZ.v n /\ Seq.index 'i (SZ.v cj) == H.bColon))))
{
  let mut j = start;
  let mut foundc = false;
  let mut ng = true;
  while (!ng)
  invariant exists* (vj:SZ.t) (vf:bool) (vg:bool).
    R.pts_to j vj ** R.pts_to foundc vf ** R.pts_to ng vg ** pts_to inp 'i **
    pure (SZ.v start <= SZ.v vj /\ SZ.v vj <= SZ.v n /\ SZ.v n <= Seq.length 'i /\
          (forall (k:nat). SZ.v start <= k /\ k < SZ.v vj ==> H.name_char (Seq.index 'i k)) /\
          (vf == true ==> (SZ.v vj < SZ.v n /\ Seq.index 'i (SZ.v vj) == H.bColon)))
  decreases %[(if !ng then 1 else 0); Prims.op_Minus (SZ.v n) (SZ.v (!j))]
  {
    let vj = !j;
    if SZ.lt vj n {
      let c = inp.(vj);
      if U8.eq c H.bColon {
        foundc := true;
        ng := false;
      } else {
        if H.name_char c {
          lemma_fits32 (SZ.v vj + 1);
          j := SZ.add vj 1sz;
        } else {
          ng := false;
        }
      }
    } else {
      ng := false;
    }
  };
  pcj := !j;
  !foundc
}

(* ── Phase 3: OWS skip ────────────────────────────────────────────────────────
   Skip the leading OWS run of `[from, n)`; write the first non-OWS position to
   `pk`.                                                                        *)
fn skip_ows (inp: array U8.t) (n: SZ.t) (from: SZ.t) (pk: R.ref SZ.t)
  requires pts_to inp 'i ** R.pts_to pk 'k0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v from <= SZ.v n /\ SZ.v n < pow2 32)
  ensures pts_to inp 'i **
    (exists* (voff:SZ.t). R.pts_to pk voff **
      pure (SZ.v n <= Seq.length 'i /\
            SZ.v from <= SZ.v voff /\ SZ.v voff <= SZ.v n /\
            (forall (p:nat). SZ.v from <= p /\ p < SZ.v voff ==> H.is_ows (Seq.index 'i p)) /\
            (SZ.v voff < SZ.v n ==> not (H.is_ows (Seq.index 'i (SZ.v voff))))))
{
  let mut k = from;
  let mut og = true;
  while (!og)
  invariant exists* (vk:SZ.t) (vg:bool).
    R.pts_to k vk ** R.pts_to og vg ** pts_to inp 'i **
    pure (SZ.v from <= SZ.v vk /\ SZ.v vk <= SZ.v n /\ SZ.v n <= Seq.length 'i /\
          (forall (p:nat). SZ.v from <= p /\ p < SZ.v vk ==> H.is_ows (Seq.index 'i p)) /\
          (vg == false ==>
            (SZ.v vk == SZ.v n \/
             (SZ.v vk < SZ.v n /\ not (H.is_ows (Seq.index 'i (SZ.v vk)))))))
  decreases %[(if !og then 1 else 0); Prims.op_Minus (SZ.v n) (SZ.v (!k))]
  {
    let vk = !k;
    if SZ.lt vk n {
      let c = inp.(vk);
      if H.is_ows c {
        lemma_fits32 (SZ.v vk + 1);
        k := SZ.add vk 1sz;
      } else {
        og := false;
      }
    } else {
      og := false;
    }
  };
  pk := !k;
}

(* ── Phase 4: value scan ──────────────────────────────────────────────────────
   Scan `[from, ei)` of `value_char` bytes until the first CR.  Writes the CR
   position to `pei` and returns whether a CR was found.                       *)
fn scan_value (inp: array U8.t) (n: SZ.t) (from: SZ.t) (pei: R.ref SZ.t)
  requires pts_to inp 'i ** R.pts_to pei 'e0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v from <= SZ.v n /\ SZ.v n < pow2 32)
  returns foundcr: bool
  ensures pts_to inp 'i **
    (exists* (ei:SZ.t). R.pts_to pei ei **
      pure (SZ.v n <= Seq.length 'i /\
            SZ.v from <= SZ.v ei /\ SZ.v ei <= SZ.v n /\
            (forall (q:nat). SZ.v from <= q /\ q < SZ.v ei ==> H.value_char (Seq.index 'i q)) /\
            (foundcr == true ==>
              (SZ.v ei < SZ.v n /\ Seq.index 'i (SZ.v ei) == W.bCR))))
{
  let mut m2 = from;
  let mut fcr = false;
  let mut vg = true;
  while (!vg)
  invariant exists* (vm:SZ.t) (vf:bool) (vgg:bool).
    R.pts_to m2 vm ** R.pts_to fcr vf ** R.pts_to vg vgg ** pts_to inp 'i **
    pure (SZ.v from <= SZ.v vm /\ SZ.v vm <= SZ.v n /\ SZ.v n <= Seq.length 'i /\
          (forall (q:nat). SZ.v from <= q /\ q < SZ.v vm ==> H.value_char (Seq.index 'i q)) /\
          (vf == true ==> (SZ.v vm < SZ.v n /\ Seq.index 'i (SZ.v vm) == W.bCR)))
  decreases %[(if !vg then 1 else 0); Prims.op_Minus (SZ.v n) (SZ.v (!m2))]
  {
    let vm = !m2;
    if SZ.lt vm n {
      let c = inp.(vm);
      if U8.eq c W.bCR {
        fcr := true;
        vg := false;
      } else {
        if H.value_char c {
          lemma_fits32 (SZ.v vm + 1);
          m2 := SZ.add vm 1sz;
        } else {
          vg := false;
        }
      }
    } else {
      vg := false;
    }
  };
  pei := !m2;
  !fcr
}

(* ── Phase 5 helper: CRLF terminator check ────────────────────────────────────
   Return `true` iff `ei+1 < n` and `inp[ei+1] == LF`.  Expression-return.     *)
fn check_lf (inp: array U8.t) (n: SZ.t) (ei: SZ.t)
  requires pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v ei <= SZ.v n /\ SZ.v n < pow2 32)
  returns b: bool
  ensures pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\
      (b == true ==>
      (SZ.v ei + 1 < SZ.v n /\ Seq.index 'i (SZ.v ei + 1) == W.bLF)))
{
  if SZ.lt ei n {
    lemma_fits32 (SZ.v ei + 1);
    let e1 = SZ.add ei 1sz;
    if SZ.lt e1 n {
      let cl = inp.(e1);
      U8.eq cl W.bLF
    } else { false }
  } else { false }
}

(* ── The deliverable ─────────────────────────────────────────────────────────
   Parse one header field-line at `start`.  On `ok /\ not is_end` the outputs
   are tied to `H.parse_field` of the suffix `'i[start..n)`.                    *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
fn http_parse_header_field
  (inp: array U8.t) (n: SZ.t) (start: SZ.t)
  (pis_end: R.ref bool) (pok: R.ref bool)
  (pnlen: R.ref SZ.t) (pvoff: R.ref SZ.t) (pvlen: R.ref SZ.t) (pnext: R.ref SZ.t)
  requires
    pts_to inp 'i ** R.pts_to pis_end 'e0 ** R.pts_to pok 'k0 **
    R.pts_to pnlen 'nl0 ** R.pts_to pvoff 'vo0 ** R.pts_to pvlen 'vl0 ** R.pts_to pnext 'nx0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v start <= SZ.v n /\ SZ.v n < pow2 32)
  ensures
    pts_to inp 'i **
    (exists* (isend ok:bool) (nlen voff vlen next:SZ.t).
       R.pts_to pis_end isend ** R.pts_to pok ok **
       R.pts_to pnlen nlen ** R.pts_to pvoff voff ** R.pts_to pvlen vlen ** R.pts_to pnext next **
       pure (
         SZ.v start <= SZ.v n /\ SZ.v n <= Seq.length 'i /\
         (let sfx = Seq.slice 'i (SZ.v start) (SZ.v n) in
          (isend == true ==>
             (SZ.v start + 2 <= SZ.v n /\
              Seq.index 'i (SZ.v start) == W.bCR /\ Seq.index 'i (SZ.v start + 1) == W.bLF)) /\
          ((ok == true /\ isend == false) ==>
             (SZ.v start + SZ.v nlen <= SZ.v n /\
              SZ.v start <= SZ.v voff /\ SZ.v voff + SZ.v vlen <= SZ.v n /\
              SZ.v voff <= SZ.v next /\ SZ.v next <= SZ.v n /\
              H.parse_field sfx ==
                Some (Seq.slice 'i (SZ.v start) (SZ.v start + SZ.v nlen),
                      Seq.slice 'i (SZ.v voff) (SZ.v voff + SZ.v vlen),
                      SZ.v next - SZ.v start))))))
{
  let isend = check_end inp n start;
  pis_end := isend;
  pok := false;
  (* name scan *)
  let mut cjr = start;
  let foundc = scan_name inp n start cjr;
  let cj = !cjr;
  let ok1 = foundc && SZ.lt start cj;
  (* OWS skip starting one past the colon (or a harmless in-bounds base) *)
  lemma_ok1_fits start cj n foundc;
  let cbase = if ok1 { SZ.add cj 1sz } else { start };
  let mut voffr = start;
  skip_ows inp n cbase voffr;
  let voff = !voffr;
  (* value scan *)
  let mut eir = voff;
  let foundcr = scan_value inp n voff eir;
  let ei = !eir;
  (* terminator check *)
  let lfok = check_lf inp n ei;
  (* finalize: tail `if` so the ensures is discharged per-branch *)
  if (ok1 && foundcr && lfok) {
    lemma_fits32 (SZ.v ei + 2);
    lemma_parse_field_tie ('i <: Seq.seq U8.t) (SZ.v start) (SZ.v n) (SZ.v cj) (SZ.v voff) (SZ.v ei);
    pnlen := SZ.sub cj start;
    pvoff := voff;
    pvlen := SZ.sub ei voff;
    pnext := SZ.add ei 2sz;
    pok := true;
  }
}
#pop-options
