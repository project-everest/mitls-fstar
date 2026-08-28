module HTTP.Impl.Codec.RequestPost

#lang-pulse

(**
  Verified Pulse emitter for an HTTP/1.1 client POST request HEAD carrying a
  variable-width `Content-Length`:

    "POST " target " HTTP/1.1\r\nContent-Length: " <digits(len)> "\r\n\r\n"

  proved byte-exact against `HTTP.Wire.Length.ser_request_post`.  Mirrors the
  request-line emitter `HTTP.Impl.Codec.Request.http_emit_request_host` (fixed
  literal + variable-token regions) and the variable-width digit run of
  `HTTP.Impl.Codec.Length.http_emit_response_var` (right-to-left decimal fill).
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ  = FStar.SizeT
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module R   = Pulse.Lib.Reference
module Ghost = FStar.Ghost
module W   = HTTP.Wire.Common
module CL  = HTTP.Impl.Codec.Length

open HTTP.Wire.Length

(* ── Executable literal bytes: "POST " (5 bytes) ───────────────────────────── *)
inline_for_extraction
let lit_post_byte (k:SZ.t{SZ.v k < 5}) : U8.t =
  if      SZ.eq k 0sz then 0x50uy
  else if SZ.eq k 1sz then 0x4Fuy
  else if SZ.eq k 2sz then 0x53uy
  else if SZ.eq k 3sz then 0x54uy
  else                     0x20uy

let lemma_lit_post_byte (k:SZ.t{SZ.v k < 5})
  : Lemma (lit_post_byte k == Seq.index lit_post (SZ.v k))
= assert_norm (Seq.index lit_post 0 == 0x50uy);
  assert_norm (Seq.index lit_post 1 == 0x4Fuy);
  assert_norm (Seq.index lit_post 2 == 0x53uy);
  assert_norm (Seq.index lit_post 3 == 0x54uy);
  assert_norm (Seq.index lit_post 4 == 0x20uy)

(* ── mid27 machinery: " HTTP/1.1\r\nContent-Length: " (27 bytes) ────────────── *)
(* seq_of_list length reduction stalls above ~17 bytes done directly, so carry
   the length in the type via the seq_of_list return type (cf. mid17/tail23). *)
noextract
let req_post_mid_list0 : list U8.t =
  [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;
   0x43uy;0x6Fuy;0x6Euy;0x74uy;0x65uy;0x6Euy;0x74uy;0x2Duy;0x4Cuy;0x65uy;0x6Euy;
   0x67uy;0x74uy;0x68uy;0x3Auy;0x20uy]

noextract
let mid27 : (x:Seq.seq U8.t{Seq.length x == 27}) =
  assert_norm (req_post_mid == Seq.seq_of_list req_post_mid_list0);
  assert_norm (List.Tot.length req_post_mid_list0 == 27); req_post_mid

inline_for_extraction
let req_post_mid_byte (k:SZ.t{SZ.v k < 27}) : U8.t =
  if      SZ.eq k 0sz  then 0x20uy
  else if SZ.eq k 1sz  then 0x48uy
  else if SZ.eq k 2sz  then 0x54uy
  else if SZ.eq k 3sz  then 0x54uy
  else if SZ.eq k 4sz  then 0x50uy
  else if SZ.eq k 5sz  then 0x2Fuy
  else if SZ.eq k 6sz  then 0x31uy
  else if SZ.eq k 7sz  then 0x2Euy
  else if SZ.eq k 8sz  then 0x31uy
  else if SZ.eq k 9sz  then 0x0Duy
  else if SZ.eq k 10sz then 0x0Auy
  else if SZ.eq k 11sz then 0x43uy
  else if SZ.eq k 12sz then 0x6Fuy
  else if SZ.eq k 13sz then 0x6Euy
  else if SZ.eq k 14sz then 0x74uy
  else if SZ.eq k 15sz then 0x65uy
  else if SZ.eq k 16sz then 0x6Euy
  else if SZ.eq k 17sz then 0x74uy
  else if SZ.eq k 18sz then 0x2Duy
  else if SZ.eq k 19sz then 0x4Cuy
  else if SZ.eq k 20sz then 0x65uy
  else if SZ.eq k 21sz then 0x6Euy
  else if SZ.eq k 22sz then 0x67uy
  else if SZ.eq k 23sz then 0x74uy
  else if SZ.eq k 24sz then 0x68uy
  else if SZ.eq k 25sz then 0x3Auy
  else                      0x20uy

noextract
let req_post_mid_list : list U8.t =
  [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;
   0x43uy;0x6Fuy;0x6Euy;0x74uy;0x65uy;0x6Euy;0x74uy;0x2Duy;0x4Cuy;0x65uy;0x6Euy;
   0x67uy;0x74uy;0x68uy;0x3Auy;0x20uy]

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let lemma_req_post_mid_byte (k:SZ.t{SZ.v k < 27})
  : Lemma (requires Seq.length mid27 == 27)
          (ensures req_post_mid_byte k == Seq.index mid27 (SZ.v k))
= assert_norm (mid27 == Seq.seq_of_list req_post_mid_list);
  assert_norm (List.Tot.length req_post_mid_list == 27);
  FStar.Seq.Properties.lemma_seq_of_list_index req_post_mid_list (SZ.v k);
  assert_norm (List.Tot.index req_post_mid_list 0  == 0x20uy);
  assert_norm (List.Tot.index req_post_mid_list 1  == 0x48uy);
  assert_norm (List.Tot.index req_post_mid_list 2  == 0x54uy);
  assert_norm (List.Tot.index req_post_mid_list 3  == 0x54uy);
  assert_norm (List.Tot.index req_post_mid_list 4  == 0x50uy);
  assert_norm (List.Tot.index req_post_mid_list 5  == 0x2Fuy);
  assert_norm (List.Tot.index req_post_mid_list 6  == 0x31uy);
  assert_norm (List.Tot.index req_post_mid_list 7  == 0x2Euy);
  assert_norm (List.Tot.index req_post_mid_list 8  == 0x31uy);
  assert_norm (List.Tot.index req_post_mid_list 9  == 0x0Duy);
  assert_norm (List.Tot.index req_post_mid_list 10 == 0x0Auy);
  assert_norm (List.Tot.index req_post_mid_list 11 == 0x43uy);
  assert_norm (List.Tot.index req_post_mid_list 12 == 0x6Fuy);
  assert_norm (List.Tot.index req_post_mid_list 13 == 0x6Euy);
  assert_norm (List.Tot.index req_post_mid_list 14 == 0x74uy);
  assert_norm (List.Tot.index req_post_mid_list 15 == 0x65uy);
  assert_norm (List.Tot.index req_post_mid_list 16 == 0x6Euy);
  assert_norm (List.Tot.index req_post_mid_list 17 == 0x74uy);
  assert_norm (List.Tot.index req_post_mid_list 18 == 0x2Duy);
  assert_norm (List.Tot.index req_post_mid_list 19 == 0x4Cuy);
  assert_norm (List.Tot.index req_post_mid_list 20 == 0x65uy);
  assert_norm (List.Tot.index req_post_mid_list 21 == 0x6Euy);
  assert_norm (List.Tot.index req_post_mid_list 22 == 0x67uy);
  assert_norm (List.Tot.index req_post_mid_list 23 == 0x74uy);
  assert_norm (List.Tot.index req_post_mid_list 24 == 0x68uy);
  assert_norm (List.Tot.index req_post_mid_list 25 == 0x3Auy);
  assert_norm (List.Tot.index req_post_mid_list 26 == 0x20uy)
#pop-options

(* ── Serialize reconstruction (opaque prefix, cf. Length.srv_bytes) ────── *)

(* Whole POST head as one opaque sequence, so the fill loops track a single
   forall against `postbytes` rather than juggling the five region quantifiers. *)
[@@ "opaque_to_smt"]
noextract
let postbytes (target:W.token) (len:content_len) : Seq.seq U8.t =
  ser_request_post target len

(* Per-position byte inventory of the POST head, exposed once. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let lemma_post_index (target:W.token) (len:content_len)
  : Lemma
    (ensures (
       let s = postbytes target len in
       let ee = W.enc_dec_var len in
       let tl = Seq.length target in
       let d = Seq.length ee in
       Seq.length lit_post == 5 /\
       Seq.length mid27 == 27 /\
       Seq.length cl_tail_post == 4 /\
       mid27 == req_post_mid /\
       Seq.length s == 36 + tl + d /\
       (forall (k:nat{k < 5}).  Seq.index s k == Seq.index lit_post k) /\
       (forall (j:nat{j < tl}). Seq.index s (5 + j) == Seq.index target j) /\
       (forall (k:nat{k < 27}). Seq.index s (5 + tl + k) == Seq.index mid27 k) /\
       (forall (j:nat{j < d}).  Seq.index s (5 + tl + 27 + j) == Seq.index ee j) /\
       (forall (k:nat{k < 4}).  Seq.index s (5 + tl + 27 + d + k) == Seq.index cl_tail_post k)))
= reveal_opaque (`%postbytes) (postbytes target len);
  assert_norm (Seq.length lit_post == 5);
  assert (Seq.length mid27 == 27);
  assert_norm (Seq.length cl_tail_post == 4);
  assert_norm (mid27 == req_post_mid)
#pop-options

(* Merge the prefix [0,32+tl), digit [32+tl,32+tl+d) and tail [32+tl+d,36+tl+d)
   correspondences into whole-buffer equality, then package the token existential. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let lemma_post_final (tok:W.token) (len:content_len) (s:Seq.seq U8.t)
  : Lemma
    (requires
       (let tl = Seq.length tok in
        let d  = Seq.length (W.enc_dec_var len) in
        Seq.length (postbytes tok len) == 36 + tl + d /\
        Seq.length s == 36 + tl + d /\
        (forall (m:nat). m < 32 + tl ==>
           Seq.index s m == Seq.index (postbytes tok len) m) /\
        (forall (jj:nat). jj < d ==>
           Seq.index s (32 + tl + jj) == Seq.index (postbytes tok len) (32 + tl + jj)) /\
        (forall (kk:nat). kk < 4 ==>
           Seq.index s (32 + tl + d + kk) == Seq.index (postbytes tok len) (32 + tl + d + kk))))
    (ensures (exists (tk:W.token).
                (tk <: Seq.seq U8.t) == (tok <: Seq.seq U8.t) /\ s == ser_request_post tk len))
= lemma_post_index tok len;                        (* Seq.length pb == 36 + tl + d *)
  let pb = postbytes tok len in
  let tl = Seq.length tok in
  let d  = Seq.length (W.enc_dec_var len) in
  assert (Seq.length pb == 36 + tl + d);
  assert (Seq.length s == 36 + tl + d);
  introduce forall (i:nat{i < Seq.length s}). Seq.index s i == Seq.index pb i
  with (
    if i < 32 + tl then ()
    else if i < 32 + tl + d then
      assert (Seq.index s (32 + tl + (i - 32 - tl))
                == Seq.index pb (32 + tl + (i - 32 - tl)))
    else
      assert (Seq.index s (32 + tl + d + (i - 32 - tl - d))
                == Seq.index pb (32 + tl + d + (i - 32 - tl - d)))
  );
  Seq.lemma_eq_intro s pb;
  reveal_opaque (`%postbytes) (postbytes tok len);
  introduce exists (tk:W.token).
     (tk <: Seq.seq U8.t) == (tok <: Seq.seq U8.t) /\ s == ser_request_post tk len
  with tok and ()
#pop-options

(* ── The verified emitter ──────────────────────────────────────────────────── *)

#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"
fn http_emit_request_post
  (target: array U8.t) (target_len: SZ.t) (len: U32.t) (out: array U8.t)
  requires
    pts_to target 't ** pts_to out 'o **
    pure (Seq.length 't == SZ.v target_len /\ W.space_free 't /\
          U32.v len < W.max_len8 /\
          SZ.v target_len + 40 < pow2 32 /\
          Seq.length 'o == 36 + SZ.v target_len + CL.dec_width (U32.v len))
  returns _:unit
  ensures
    pts_to target 't **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 36 + SZ.v target_len + CL.dec_width (U32.v len) /\
             U32.v len < W.max_len8 /\
             (W.space_free 't ==>
                (exists (tk:W.token). (tk <: Seq.seq U8.t) == 't /\
                   o' == ser_request_post tk (U32.v len)))))
{
  CL.lemma_enc_dec_var_len (U32.v len);         (* length ee == dec_width len == d *)
  W.lemma_enc_dec_var_roundtrip (U32.v len);    (* all_dec ee /\ dec_dec_var ee == len *)
  let dcount = CL.dec_width_u32 len;            (* SZ.v dcount == dec_width (U32.v len) == d *)
  CL.lemma_dec_width_mono (U32.v len) 99999999; (* d <= dec_width 99999999 == 8 *)
  assert_norm (CL.dec_width 99999999 == 8);
  (* Ghost token binding (space_free is available in the body). *)
  let tok : Ghost.erased W.token = Ghost.hide (Ghost.reveal 't <: W.token);
  lemma_post_index (Ghost.reveal tok) (U32.v len);

  (* Phase 1: literal "POST " into [0,5). *)
  let mut a = 0sz;
  while (SZ.lt !a 5sz)
  invariant exists* (va:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to a va ** pts_to target 't ** pts_to out sv **
    pure (
      SZ.v va <= 5 /\
      Seq.length 't == SZ.v target_len /\ Ghost.reveal tok == Ghost.reveal 't /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == 36 + SZ.v target_len + SZ.v dcount /\
      (forall (m:nat). m < SZ.v va ==>
         Seq.index sv m == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) m))
  decreases (Prims.op_Minus (SZ.v 5sz) (SZ.v (!a)))
  {
    let va = !a;
    lemma_lit_post_byte va;
    let bt = lit_post_byte va;
    out.(va) <- bt;
    a := SZ.add va 1sz;
  };

  (* Phase 2: variable target token into [5, 5+tl). *)
  let mut i = 0sz;
  while (SZ.lt !i target_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi ** pts_to target 't ** pts_to out sv **
    pure (
      SZ.v vi <= SZ.v target_len /\
      Seq.length 't == SZ.v target_len /\ Ghost.reveal tok == Ghost.reveal 't /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == 36 + SZ.v target_len + SZ.v dcount /\
      (forall (m:nat). m < 5 + SZ.v vi ==>
         Seq.index sv m == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) m))
  decreases (Prims.op_Minus (SZ.v target_len) (SZ.v (!i)))
  {
    let vi = !i;
    CL.lemma_fits32 (5 + SZ.v vi);
    let dv = target.(vi);
    out.(SZ.add 5sz vi) <- dv;
    i := SZ.add vi 1sz;
  };

  (* Phase 3: literal " HTTP/1.1\r\nContent-Length: " into [5+tl, 5+tl+27). *)
  let mut b = 0sz;
  while (SZ.lt !b 27sz)
  invariant exists* (vb:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to b vb ** pts_to target 't ** pts_to out sv **
    pure (
      SZ.v vb <= 27 /\
      Seq.length 't == SZ.v target_len /\ Ghost.reveal tok == Ghost.reveal 't /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == 36 + SZ.v target_len + SZ.v dcount /\
      (forall (m:nat). m < 5 + SZ.v target_len + SZ.v vb ==>
         Seq.index sv m == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) m))
  decreases (Prims.op_Minus (SZ.v 27sz) (SZ.v (!b)))
  {
    let vb = !b;
    assert_norm (Seq.length mid27 == 27);
    lemma_req_post_mid_byte vb;
    CL.lemma_fits32 (5 + SZ.v target_len + SZ.v vb);
    let bt = req_post_mid_byte vb;
    out.(SZ.add (SZ.add 5sz target_len) vb) <- bt;
    b := SZ.add vb 1sz;
  };

  (* dbase = 5 + tl + 27 = 32 + tl (start of the digit region). *)
  CL.lemma_fits32 (5 + SZ.v target_len);
  CL.lemma_fits32 (32 + SZ.v target_len);
  let dbase = SZ.add (SZ.add 5sz target_len) 27sz;
  CL.lemma_fits32 (32 + SZ.v target_len + SZ.v dcount);
  let base = SZ.add dbase dcount;               (* = 32 + tl + d = end of digit region *)

  (* Phase 4: digits [dbase, dbase+d) — right-to-left, peeling low digits off rem. *)
  let mut pos = base;
  let mut rem = len;
  CL.lemma_all_dec_prefix (W.enc_dec_var (U32.v len)) (SZ.v dcount);
  while (SZ.lt dbase !pos)
  invariant exists* (vpos:SZ.t) (vrem:U32.t) (sv:Seq.seq U8.t).
    R.pts_to pos vpos ** R.pts_to rem vrem ** pts_to target 't ** pts_to out sv **
    pure (
      SZ.v dbase <= SZ.v vpos /\ SZ.v vpos <= SZ.v dbase + SZ.v dcount /\
      SZ.v dbase == 32 + SZ.v target_len /\
      Seq.length 't == SZ.v target_len /\ Ghost.reveal tok == Ghost.reveal 't /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == 36 + SZ.v target_len + SZ.v dcount /\
      (forall (m:nat). m < SZ.v dbase ==>
         Seq.index sv m == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) m) /\
      (forall (jj:nat).
         (SZ.v vpos - SZ.v dbase <= jj /\ jj < SZ.v dcount) ==>
         Seq.index sv (SZ.v dbase + jj)
           == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) (SZ.v dbase + jj)) /\
      W.all_dec (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v vpos - SZ.v dbase)) /\
      Prims.op_Equals #Prims.nat (U32.v vrem)
        (W.dec_dec_var (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v vpos - SZ.v dbase))))
  decreases (SZ.v (!pos))
  {
    let vpos = !pos;
    let vrem = !rem;
    let pos' = SZ.sub vpos 1sz;                 (* absolute position to write, in [dbase, base) *)
    let jpos = SZ.sub pos' dbase;               (* SZ.v jpos == SZ.v pos' - SZ.v dbase *)
    CL.lemma_all_dec_prefix (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    CL.lemma_all_dec_index  (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    CL.lemma_slice_snoc     (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    W.lemma_dec_dec_snoc (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v jpos))
                         (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos));
    CL.lemma_divmod10
      (W.dec_dec_var (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v jpos)))
      (W.undig (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos)));
    CL.lemma_mod10_32 vrem;
    let r10 = U32.rem vrem 10ul;
    let bt = CL.u32_digit r10;
    CL.lemma_dig_undig_inv (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos));
    out.(pos') <- bt;
    rem := U32.div vrem 10ul;
    pos := pos';
  };

  (* Phase 5: literal "\r\n\r\n" into [base, base+4). *)
  let mut c = 0sz;
  while (SZ.lt !c 4sz)
  invariant exists* (vc:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to c vc ** pts_to target 't ** pts_to out sv **
    pure (
      SZ.v vc <= 4 /\
      SZ.v dbase == 32 + SZ.v target_len /\
      SZ.v base == SZ.v dbase + SZ.v dcount /\
      Seq.length 't == SZ.v target_len /\ Ghost.reveal tok == Ghost.reveal 't /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == 36 + SZ.v target_len + SZ.v dcount /\
      (forall (m:nat). m < SZ.v dbase ==>
         Seq.index sv m == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) m) /\
      (forall (jj:nat). jj < SZ.v dcount ==>
         Seq.index sv (SZ.v dbase + jj)
           == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) (SZ.v dbase + jj)) /\
      (forall (kk:nat). kk < SZ.v vc ==>
         Seq.index sv (SZ.v base + kk)
           == Seq.index (postbytes (Ghost.reveal tok) (U32.v len)) (SZ.v base + kk)))
  decreases (Prims.op_Minus (SZ.v 4sz) (SZ.v (!c)))
  {
    let vc = !c;
    CL.lemma_cl_post_byte vc;
    let bt = CL.cl_post_byte vc;
    pts_to_len out;
    out.(SZ.add base vc) <- bt;
    c := SZ.add vc 1sz;
  };

  with sf. assert (pts_to out sf);
  lemma_post_final (Ghost.reveal tok) (U32.v len) sf;
  ()
}
#pop-options
