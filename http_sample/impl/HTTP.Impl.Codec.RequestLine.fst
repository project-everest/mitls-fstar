module HTTP.Impl.Codec.RequestLine

#lang-pulse

(**
  Verified Pulse scanning parser for a *real* client's HTTP/1.1 request line,
  method-aware (accepts POST and any other method):

      METHOD SP target SP "HTTP/1.1" CRLF  header-lines*  CRLF

  `http_parse_request_line` recovers the method token (bytes before the first
  space) and the space-free target token (bytes before the second space), then
  requires the version token "HTTP/1.1\r\n", ignoring every byte after it (all
  header lines).  It is a scanning parser in the same idiom as
  `HTTP.Impl.Codec.Header.http_parse_header_field`: two bounds-checked space
  scans plus a fixed 10-byte version compare, each proved memory-safe by the
  Pulse VC, then tied to the pure spec `HTTP.Wire.Length.parse_request_line_m`.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module SP   = FStar.Seq.Properties
module U8   = FStar.UInt8
module R    = Pulse.Lib.Reference
module W    = HTTP.Wire.Common

open HTTP.Wire.Length

(* size_t is >= 32 bits on every real target; the small index sums here can
   exceed F*'s SizeT 2^16 auto-`fits` line, so discharge sub-2^32 `fits`
   explicitly (same open assumption as the other HTTP impl leaves). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x

(* `mp + 1` fits size_t whenever a first space was actually found (so `mp < n`). *)
let lemma_succ_fits (mp n:SZ.t) (foundm:bool)
  : Lemma (requires SZ.v n < pow2 32 /\ (foundm == true ==> SZ.v mp < SZ.v n))
          (ensures (foundm == true ==> FStar.SizeT.fits (SZ.v mp + 1)))
  = if foundm then lemma_fits32 (SZ.v mp + 1)

(* A byte sequence with no embedded space (0x20) is `space_free` (a W.token).
   Local copy of the same lemma in impl/HTTP.Impl.Codec.Length.fst. *)
let rec lemma_space_free_no_space (b:Seq.seq U8.t)
  : Lemma (requires (forall (j:nat). j < Seq.length b ==> Seq.index b j <> W.bSP))
          (ensures W.space_free b)
          (decreases Seq.length b)
  = if Seq.length b = 0 then ()
    else begin
      let tl = Seq.slice b 1 (Seq.length b) in
      assert (forall (j:nat). j < Seq.length tl ==> Seq.index tl j == Seq.index b (j + 1));
      lemma_space_free_no_space tl
    end

(* ── Executable version literal "HTTP/1.1\r\n" ─────────────────────────────── *)
let req_ver_list0 : list U8.t =
  [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy]

(* One executable byte of `req_ver`, tied to `Seq.index req_ver` below.  Must be
   `inline_for_extraction`: `req_ver` lives in the (non-extracted) spec module,
   so a runtime `Seq.index req_ver` would emit an unresolved extern under
   KaRaMeL — instead we compare against these inlined constant bytes. *)
inline_for_extraction
let req_ver_byte (k:SZ.t{SZ.v k < 10}) : U8.t =
  if      SZ.eq k 0sz then 0x48uy
  else if SZ.eq k 1sz then 0x54uy
  else if SZ.eq k 2sz then 0x54uy
  else if SZ.eq k 3sz then 0x50uy
  else if SZ.eq k 4sz then 0x2Fuy
  else if SZ.eq k 5sz then 0x31uy
  else if SZ.eq k 6sz then 0x2Euy
  else if SZ.eq k 7sz then 0x31uy
  else if SZ.eq k 8sz then 0x0Duy
  else                     0x0Auy

let lemma_req_ver_byte (k:SZ.t{SZ.v k < 10})
  : Lemma (ensures req_ver_byte k == Seq.index req_ver (SZ.v k))
  = assert_norm (req_ver == Seq.seq_of_list req_ver_list0);
    assert_norm (List.Tot.length req_ver_list0 == 10);
    FStar.Seq.Properties.lemma_seq_of_list_index req_ver_list0 (SZ.v k);
    assert_norm (List.Tot.index req_ver_list0 0 == 0x48uy);
    assert_norm (List.Tot.index req_ver_list0 1 == 0x54uy);
    assert_norm (List.Tot.index req_ver_list0 2 == 0x54uy);
    assert_norm (List.Tot.index req_ver_list0 3 == 0x50uy);
    assert_norm (List.Tot.index req_ver_list0 4 == 0x2Fuy);
    assert_norm (List.Tot.index req_ver_list0 5 == 0x31uy);
    assert_norm (List.Tot.index req_ver_list0 6 == 0x2Euy);
    assert_norm (List.Tot.index req_ver_list0 7 == 0x31uy);
    assert_norm (List.Tot.index req_ver_list0 8 == 0x0Duy);
    assert_norm (List.Tot.index req_ver_list0 9 == 0x0Auy)

(* ── Deliverable 1: pure round-trip lemma ──────────────────────────────────────

   Generalizes `HTTP.Impl.Codec.Length.lemma_parse_request_line_ok` (a single,
   GET-hardcoded split) to the TWO-split, method-aware form: rebuild
   `inp == meth ++ (SP :: inp[mp+1..])` for the first split and
   `inp[mp+1..] == target ++ (SP :: inp[sp+1..])` for the second, so `split_sp`
   cuts at each first space, then match the version token.                     *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let lemma_parse_request_line_m_ok (inp:Seq.seq U8.t) (mp sp:nat)
  : Lemma
    (requires
       mp < sp /\ sp + 11 <= Seq.length inp /\
       (forall (k:nat). k < mp ==> Seq.index inp k =!= W.bSP) /\
       Seq.index inp mp == W.bSP /\
       (forall (j:nat). mp < j /\ j < sp ==> Seq.index inp j =!= W.bSP) /\
       Seq.index inp sp == W.bSP /\
       (forall (k:nat). k < 10 ==> Seq.index inp (sp + 1 + k) == Seq.index req_ver k))
    (ensures
       parse_request_line_m inp ==
         Some (Seq.slice inp 0 mp, Seq.slice inp (mp + 1) sp))
  = let n = Seq.length inp in
    (* ── first split: split_sp inp == Some(meth, rest_m) ── *)
    let meth = Seq.slice inp 0 mp in
    lemma_space_free_no_space meth;
    let rest_m = Seq.slice inp (mp + 1) n in
    let mid_m  = Seq.cons W.bSP rest_m in
    let apnd_m = Seq.append meth mid_m in
    assert (Seq.length mid_m == n - mp);
    introduce forall (j:nat{j < Seq.length inp}).
        Seq.index inp j == Seq.index apnd_m j
    with (
      if j < mp then Seq.lemma_index_app1 meth mid_m j
      else Seq.lemma_index_app2 meth mid_m j
    );
    Seq.lemma_eq_intro inp apnd_m;
    W.split_sp_append (meth <: W.token) rest_m;
    assert (W.split_sp inp == Some (meth, rest_m));
    (* ── second split: split_sp rest_m == Some(target, rest_t) ── *)
    let target = Seq.slice inp (mp + 1) sp in
    lemma_space_free_no_space target;
    let rest_t = Seq.slice inp (sp + 1) n in
    let mid_t  = Seq.cons W.bSP rest_t in
    let apnd_t = Seq.append target mid_t in
    assert (Seq.length mid_t == n - sp);
    introduce forall (j:nat{j < Seq.length rest_m}).
        Seq.index rest_m j == Seq.index apnd_t j
    with (
      let tlen = sp - (mp + 1) in
      if j < tlen then Seq.lemma_index_app1 target mid_t j
      else Seq.lemma_index_app2 target mid_t j
    );
    Seq.lemma_eq_intro rest_m apnd_t;
    W.split_sp_append (target <: W.token) rest_t;
    assert (W.split_sp rest_m == Some (target, rest_t));
    (* ── version token ── *)
    assert (Seq.length rest_t >= 10);
    Seq.lemma_eq_intro (Seq.slice rest_t 0 10) req_ver;
    W.lemma_bseq_eq (Seq.slice rest_t 0 10) req_ver
#pop-options

(* Bridge the pure round-trip lemma (stated over a whole seq) to the buffer
   prefix `inp[0..n)` the Pulse leaf constrains, converting `slice (slice i 0 n)`
   back to `slice i`.                                                          *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_finalize (i:Seq.seq U8.t) (n mp sp:nat)
  : Lemma
    (requires
       n <= Seq.length i /\ mp < sp /\ sp + 11 <= n /\
       (forall (k:nat). k < mp ==> Seq.index i k =!= W.bSP) /\
       Seq.index i mp == W.bSP /\
       (forall (j:nat). mp < j /\ j < sp ==> Seq.index i j =!= W.bSP) /\
       Seq.index i sp == W.bSP /\
       (forall (k:nat). k < 10 ==> Seq.index i (sp + 1 + k) == Seq.index req_ver k))
    (ensures
       parse_request_line_m (Seq.slice i 0 n) ==
         Some (Seq.slice i 0 mp, Seq.slice i (mp + 1) sp))
  = let s = Seq.slice i 0 n in
    assert (Seq.length s == n);
    assert (forall (k:nat). k < n ==> Seq.index s k == Seq.index i k);
    lemma_parse_request_line_m_ok s mp sp;
    Seq.slice_slice i 0 n 0 mp;
    Seq.slice_slice i 0 n (mp + 1) sp;
    assert (Seq.slice s 0 mp == Seq.slice i 0 mp);
    assert (Seq.slice s (mp + 1) sp == Seq.slice i (mp + 1) sp)
#pop-options

(* ── Phase helper: scan for the first space in [from, n) ───────────────────────
   Return `found` and (via `pj`) the first index `j` with `inp[j] == SP`, or `n`
   if none; accumulate the "no space before `j`" fact.                         *)
fn scan_sp (inp: array U8.t) (n: SZ.t) (from: SZ.t) (pj: R.ref SZ.t)
  requires pts_to inp 'i ** R.pts_to pj 'j0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v from <= SZ.v n /\ SZ.v n < pow2 32)
  returns found: bool
  ensures pts_to inp 'i **
    (exists* (j:SZ.t). R.pts_to pj j **
      pure (SZ.v n <= Seq.length 'i /\
            SZ.v from <= SZ.v j /\ SZ.v j <= SZ.v n /\
            (forall (k:nat). SZ.v from <= k /\ k < SZ.v j ==> Seq.index 'i k =!= W.bSP) /\
            (found == true ==> (SZ.v j < SZ.v n /\ Seq.index 'i (SZ.v j) == W.bSP))))
{
  let mut j = from;
  let mut g = true;
  while (!g)
  invariant exists* (vj:SZ.t) (vg:bool).
    R.pts_to j vj ** R.pts_to g vg ** pts_to inp 'i **
    pure (SZ.v from <= SZ.v vj /\ SZ.v vj <= SZ.v n /\ SZ.v n <= Seq.length 'i /\
          (forall (k:nat). SZ.v from <= k /\ k < SZ.v vj ==> Seq.index 'i k =!= W.bSP) /\
          (vg == false ==>
            (SZ.v vj == SZ.v n \/
             (SZ.v vj < SZ.v n /\ Seq.index 'i (SZ.v vj) == W.bSP))))
  decreases %[(if !g then 1 else 0); Prims.op_Minus (SZ.v n) (SZ.v (!j))]
  {
    let vj = !j;
    if SZ.lt vj n {
      let c = inp.(vj);
      if U8.eq c W.bSP {
        g := false;
      } else {
        lemma_fits32 (SZ.v vj + 1);
        j := SZ.add vj 1sz;
      }
    } else {
      g := false;
    }
  };
  let jf = !j;
  pj := jf;
  SZ.lt jf n
}

(* ── Phase helper: compare the 10 bytes inp[sp+1 .. sp+11] to req_ver ─────────── *)
fn check_ver (inp: array U8.t) (n: SZ.t) (sp: SZ.t)
  requires pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v sp <= SZ.v n /\ SZ.v n < pow2 32)
  returns ok: bool
  ensures pts_to inp 'i **
    pure (SZ.v n <= Seq.length 'i /\
      (ok == true ==>
        (SZ.v sp + 11 <= SZ.v n /\
         (forall (k:nat). k < 10 ==> Seq.index 'i (SZ.v sp + 1 + k) == Seq.index req_ver k))))
{
  let rem = SZ.sub n sp;
  if SZ.lte 11sz rem {
    (* sp + 11 <= n *)
    lemma_fits32 (SZ.v sp + 1);
    let base = SZ.add sp 1sz;
    let mut k = 0sz;
    let mut good = true;
    let mut g = true;
    while (!g)
    invariant exists* (vk:SZ.t) (vgood:bool) (vg:bool).
      R.pts_to k vk ** R.pts_to good vgood ** R.pts_to g vg ** pts_to inp 'i **
      pure (SZ.v vk <= 10 /\ SZ.v n <= Seq.length 'i /\ SZ.v sp + 11 <= SZ.v n /\
            SZ.v base == SZ.v sp + 1 /\
            (vgood == true ==>
              (forall (kk:nat). kk < SZ.v vk ==> Seq.index 'i (SZ.v sp + 1 + kk) == Seq.index req_ver kk)) /\
            (vg == false ==> (SZ.v vk == 10 \/ vgood == false)))
    decreases %[(if !g then 1 else 0); Prims.op_Minus (SZ.v 10sz) (SZ.v (!k))]
    {
      let vk = !k;
      let vgood = !good;
      if (SZ.lt vk 10sz && vgood) {
        lemma_fits32 (SZ.v sp + 1 + SZ.v vk);
        let idx = SZ.add base vk;
        let c = inp.(idx);
        lemma_req_ver_byte vk;
        let want = req_ver_byte vk;
        if U8.eq c want {
          lemma_fits32 (SZ.v vk + 1);
          k := SZ.add vk 1sz;
        } else {
          good := false;
          g := false;
        }
      } else {
        g := false;
      }
    };
    !good
  } else {
    false
  }
}

(* ── Deliverable 2: the verified Pulse leaf ────────────────────────────────────
   Parse a real client's request line at offset 0.  On `ok` the outputs identify
   method = inp[0..mlen) and target = inp[toff..toff+tlen) and are tied to
   `parse_request_line_m (inp[0..n))`.                                          *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
fn http_parse_request_line
  (inp: array U8.t) (n: SZ.t)
  (pok: R.ref bool)
  (pmlen: R.ref SZ.t)
  (ptoff: R.ref SZ.t) (ptlen: R.ref SZ.t)
  requires
    pts_to inp 'i ** R.pts_to pok 'k0 ** R.pts_to pmlen 'm0 **
    R.pts_to ptoff 'to0 ** R.pts_to ptlen 'tl0 **
    pure (SZ.v n <= Seq.length 'i /\ SZ.v n < pow2 32)
  ensures
    pts_to inp 'i **
    (exists* (ok:bool) (mlen toff tlen:SZ.t).
       R.pts_to pok ok ** R.pts_to pmlen mlen **
       R.pts_to ptoff toff ** R.pts_to ptlen tlen **
       pure (SZ.v n <= Seq.length 'i /\
         (ok == true ==>
            (SZ.v mlen <= SZ.v n /\ SZ.v toff <= SZ.v n /\ SZ.v toff + SZ.v tlen <= SZ.v n /\
             parse_request_line_m (Seq.slice 'i 0 (SZ.v n)) ==
               Some (Seq.slice 'i 0 (SZ.v mlen),
                     Seq.slice 'i (SZ.v toff) (SZ.v toff + SZ.v tlen))))))
{
  pok := false;
  (* first space: method = inp[0..mp) *)
  let mut mpr = 0sz;
  let foundm = scan_sp inp n 0sz mpr;
  let mp = !mpr;
  (* second space starts one past the method's space *)
  lemma_succ_fits mp n foundm;
  let base2 = if foundm { SZ.add mp 1sz } else { 0sz };
  let mut spr = base2;
  let foundsp = scan_sp inp n base2 spr;
  let sp = !spr;
  (* version token *)
  let verok = check_ver inp n sp;
  (* finalize: tail `if` so the ensures is discharged per-branch *)
  let cont = foundm && not (SZ.eq mp 0sz) && foundsp && verok;
  if cont {
    lemma_fits32 (SZ.v mp + 1);
    lemma_finalize ('i <: Seq.seq U8.t) (SZ.v n) (SZ.v mp) (SZ.v sp);
    pmlen := mp;
    ptoff := SZ.add mp 1sz;
    ptlen := SZ.sub sp (SZ.add mp 1sz);
    pok := true;
  }
}
#pop-options
