module HTTP.Impl.Codec.Request

#lang-pulse

(**
  Verified Pulse emitter for a *real* origin-server HTTP/1.1 GET request line
  carrying a `Host:` header (mandatory in HTTP/1.1) and `Connection: close`:

    "GET " target " HTTP/1.1\r\nHost: " host "\r\nConnection: close\r\n\r\n"

  proved byte-exact against `HTTP.Wire.Length.ser_request_host`.  This is what a
  client sends to talk to an actual web server (e.g. GET http://example.com/),
  unlike the fixed `http_emit_request` used by the internal verified<->verified
  loops (which omits Host, so real servers answer 400).
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ  = FStar.SizeT
module Seq = FStar.Seq
module U8  = FStar.UInt8
module R   = Pulse.Lib.Reference
module W   = HTTP.Wire.Common
module CL  = HTTP.Impl.Codec.Length

open HTTP.Wire.Length

(* Length-refined aliases: seq_of_list length reduction gets stuck for the
   17/23-byte literals during subtyping, so carry the length in the type.  The
   direct `assert_norm (Seq.length lit == N)` reduction stalls for N>~17, so we
   route through `seq_of_list`, whose return type exposes the length. *)
let req_host_mid_list0 : list U8.t =
  [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;0x48uy;0x6Fuy;0x73uy;0x74uy;0x3Auy;0x20uy]
let req_host_tail_list0 : list U8.t =
  [0x0Duy;0x0Auy;0x43uy;0x6Fuy;0x6Euy;0x6Euy;0x65uy;0x63uy;0x74uy;0x69uy;0x6Fuy;0x6Euy;0x3Auy;0x20uy;0x63uy;0x6Cuy;0x6Fuy;0x73uy;0x65uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]
let mid17 : (x:Seq.seq U8.t{Seq.length x == 17}) =
  assert_norm (req_host_mid == Seq.seq_of_list req_host_mid_list0);
  assert_norm (List.Tot.length req_host_mid_list0 == 17); req_host_mid
let tail23 : (x:Seq.seq U8.t{Seq.length x == 23}) =
  assert_norm (req_host_tail == Seq.seq_of_list req_host_tail_list0);
  assert_norm (List.Tot.length req_host_tail_list0 == 23); req_host_tail

(* ── Executable literal bytes ──────────────────────────────────────────────── *)

inline_for_extraction
let req_host_mid_byte (k:SZ.t{SZ.v k < 17}) : U8.t =
  if      SZ.eq k 0sz then 0x20uy
  else if SZ.eq k 1sz then 0x48uy
  else if SZ.eq k 2sz then 0x54uy
  else if SZ.eq k 3sz then 0x54uy
  else if SZ.eq k 4sz then 0x50uy
  else if SZ.eq k 5sz then 0x2Fuy
  else if SZ.eq k 6sz then 0x31uy
  else if SZ.eq k 7sz then 0x2Euy
  else if SZ.eq k 8sz then 0x31uy
  else if SZ.eq k 9sz then 0x0Duy
  else if SZ.eq k 10sz then 0x0Auy
  else if SZ.eq k 11sz then 0x48uy
  else if SZ.eq k 12sz then 0x6Fuy
  else if SZ.eq k 13sz then 0x73uy
  else if SZ.eq k 14sz then 0x74uy
  else if SZ.eq k 15sz then 0x3Auy
  else                     0x20uy

let req_host_mid_list : list U8.t =
  [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;0x48uy;0x6Fuy;0x73uy;0x74uy;0x3Auy;0x20uy]

let lemma_req_host_mid_byte (k:SZ.t{SZ.v k < 17})
  : Lemma (requires Seq.length mid17 == 17)
          (ensures req_host_mid_byte k == Seq.index mid17 (SZ.v k))
= assert_norm (mid17 == Seq.seq_of_list req_host_mid_list);
  assert_norm (List.Tot.length req_host_mid_list == 17);
  FStar.Seq.Properties.lemma_seq_of_list_index req_host_mid_list (SZ.v k);
  assert_norm (List.Tot.index req_host_mid_list 0 == 0x20uy);
  assert_norm (List.Tot.index req_host_mid_list 1 == 0x48uy);
  assert_norm (List.Tot.index req_host_mid_list 2 == 0x54uy);
  assert_norm (List.Tot.index req_host_mid_list 3 == 0x54uy);
  assert_norm (List.Tot.index req_host_mid_list 4 == 0x50uy);
  assert_norm (List.Tot.index req_host_mid_list 5 == 0x2Fuy);
  assert_norm (List.Tot.index req_host_mid_list 6 == 0x31uy);
  assert_norm (List.Tot.index req_host_mid_list 7 == 0x2Euy);
  assert_norm (List.Tot.index req_host_mid_list 8 == 0x31uy);
  assert_norm (List.Tot.index req_host_mid_list 9 == 0x0Duy);
  assert_norm (List.Tot.index req_host_mid_list 10 == 0x0Auy);
  assert_norm (List.Tot.index req_host_mid_list 11 == 0x48uy);
  assert_norm (List.Tot.index req_host_mid_list 12 == 0x6Fuy);
  assert_norm (List.Tot.index req_host_mid_list 13 == 0x73uy);
  assert_norm (List.Tot.index req_host_mid_list 14 == 0x74uy);
  assert_norm (List.Tot.index req_host_mid_list 15 == 0x3Auy);
  assert_norm (List.Tot.index req_host_mid_list 16 == 0x20uy)

inline_for_extraction
let req_host_tail_byte (k:SZ.t{SZ.v k < 23}) : U8.t =
  if      SZ.eq k 0sz then 0x0Duy
  else if SZ.eq k 1sz then 0x0Auy
  else if SZ.eq k 2sz then 0x43uy
  else if SZ.eq k 3sz then 0x6Fuy
  else if SZ.eq k 4sz then 0x6Euy
  else if SZ.eq k 5sz then 0x6Euy
  else if SZ.eq k 6sz then 0x65uy
  else if SZ.eq k 7sz then 0x63uy
  else if SZ.eq k 8sz then 0x74uy
  else if SZ.eq k 9sz then 0x69uy
  else if SZ.eq k 10sz then 0x6Fuy
  else if SZ.eq k 11sz then 0x6Euy
  else if SZ.eq k 12sz then 0x3Auy
  else if SZ.eq k 13sz then 0x20uy
  else if SZ.eq k 14sz then 0x63uy
  else if SZ.eq k 15sz then 0x6Cuy
  else if SZ.eq k 16sz then 0x6Fuy
  else if SZ.eq k 17sz then 0x73uy
  else if SZ.eq k 18sz then 0x65uy
  else if SZ.eq k 19sz then 0x0Duy
  else if SZ.eq k 20sz then 0x0Auy
  else if SZ.eq k 21sz then 0x0Duy
  else                     0x0Auy

let req_host_tail_list : list U8.t =
  [0x0Duy;0x0Auy;0x43uy;0x6Fuy;0x6Euy;0x6Euy;0x65uy;0x63uy;0x74uy;0x69uy;0x6Fuy;0x6Euy;0x3Auy;0x20uy;0x63uy;0x6Cuy;0x6Fuy;0x73uy;0x65uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let lemma_req_host_tail_byte (k:SZ.t{SZ.v k < 23})
  : Lemma (requires Seq.length tail23 == 23)
          (ensures req_host_tail_byte k == Seq.index tail23 (SZ.v k))
= assert_norm (tail23 == Seq.seq_of_list req_host_tail_list);
  assert_norm (List.Tot.length req_host_tail_list == 23);
  FStar.Seq.Properties.lemma_seq_of_list_index req_host_tail_list (SZ.v k);
  assert_norm (List.Tot.index req_host_tail_list 0 == 0x0Duy);
  assert_norm (List.Tot.index req_host_tail_list 1 == 0x0Auy);
  assert_norm (List.Tot.index req_host_tail_list 2 == 0x43uy);
  assert_norm (List.Tot.index req_host_tail_list 3 == 0x6Fuy);
  assert_norm (List.Tot.index req_host_tail_list 4 == 0x6Euy);
  assert_norm (List.Tot.index req_host_tail_list 5 == 0x6Euy);
  assert_norm (List.Tot.index req_host_tail_list 6 == 0x65uy);
  assert_norm (List.Tot.index req_host_tail_list 7 == 0x63uy);
  assert_norm (List.Tot.index req_host_tail_list 8 == 0x74uy);
  assert_norm (List.Tot.index req_host_tail_list 9 == 0x69uy);
  assert_norm (List.Tot.index req_host_tail_list 10 == 0x6Fuy);
  assert_norm (List.Tot.index req_host_tail_list 11 == 0x6Euy);
  assert_norm (List.Tot.index req_host_tail_list 12 == 0x3Auy);
  assert_norm (List.Tot.index req_host_tail_list 13 == 0x20uy);
  assert_norm (List.Tot.index req_host_tail_list 14 == 0x63uy);
  assert_norm (List.Tot.index req_host_tail_list 15 == 0x6Cuy);
  assert_norm (List.Tot.index req_host_tail_list 16 == 0x6Fuy);
  assert_norm (List.Tot.index req_host_tail_list 17 == 0x73uy);
  assert_norm (List.Tot.index req_host_tail_list 18 == 0x65uy);
  assert_norm (List.Tot.index req_host_tail_list 19 == 0x0Duy);
  assert_norm (List.Tot.index req_host_tail_list 20 == 0x0Auy);
  assert_norm (List.Tot.index req_host_tail_list 21 == 0x0Duy);
  assert_norm (List.Tot.index req_host_tail_list 22 == 0x0Auy)
#pop-options

(* ── Serialize reconstruction ──────────────────────────────────────────────── *)

(* A buffer filled with the five request-line regions equals ser_request_host. *)
#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"
let emit_request_host_serialize (target host:W.token) (s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length s == 4 + Seq.length target + 17 + Seq.length host + 23 /\
       (forall (k:nat). k < 4 ==> Seq.index s k == Seq.index lit_get k) /\
       (forall (j:nat). j < Seq.length target ==>
          Seq.index s (4 + j) == Seq.index target j) /\
       (forall (k:nat). k < 17 ==>
          Seq.index s (4 + Seq.length target + k) == Seq.index mid17 k) /\
       (forall (j:nat). j < Seq.length host ==>
          Seq.index s (4 + Seq.length target + 17 + j) == Seq.index host j) /\
       (forall (k:nat). k < 23 ==>
          Seq.index s (4 + Seq.length target + 17 + Seq.length host + k)
            == Seq.index tail23 k))
    (ensures s == ser_request_host target host)
= let tlen = Seq.length target in
  let hlen = Seq.length host in
  assert_norm (Seq.length lit_get == 4);
  assert_norm (Seq.length mid17 == 17);
  assert_norm (Seq.length tail23 == 23);
  Seq.lemma_eq_intro (Seq.slice s 0 4) lit_get;
  Seq.lemma_eq_intro (Seq.slice s 4 (4 + tlen)) target;
  Seq.lemma_eq_intro (Seq.slice s (4 + tlen) (4 + tlen + 17)) mid17;
  Seq.lemma_eq_intro (Seq.slice s (4 + tlen + 17) (4 + tlen + 17 + hlen)) host;
  Seq.lemma_eq_intro
    (Seq.slice s (4 + tlen + 17 + hlen) (4 + tlen + 17 + hlen + 23)) tail23;
  Seq.lemma_eq_intro s (ser_request_host target host)
#pop-options

(* Package as a token existential (mirrors CL.emit_request_exists). *)
let emit_request_host_exists (t h s:Seq.seq U8.t)
  : Lemma
    (requires
       W.space_free t /\ W.space_free h /\
       Seq.length s == 4 + Seq.length t + 17 + Seq.length h + 23 /\
       (forall (k:nat). k < 4 ==> Seq.index s k == Seq.index lit_get k) /\
       (forall (j:nat). j < Seq.length t ==> Seq.index s (4 + j) == Seq.index t j) /\
       (forall (k:nat). k < 17 ==>
          Seq.index s (4 + Seq.length t + k) == Seq.index mid17 k) /\
       (forall (j:nat). j < Seq.length h ==>
          Seq.index s (4 + Seq.length t + 17 + j) == Seq.index h j) /\
       (forall (k:nat). k < 23 ==>
          Seq.index s (4 + Seq.length t + 17 + Seq.length h + k)
            == Seq.index tail23 k))
    (ensures (exists (tk hk:W.token).
                (tk <: Seq.seq U8.t) == t /\ (hk <: Seq.seq U8.t) == h /\
                s == ser_request_host tk hk))
= emit_request_host_serialize (t <: W.token) (h <: W.token) s;
  introduce exists (tk hk:W.token).
     (tk <: Seq.seq U8.t) == t /\ (hk <: Seq.seq U8.t) == h /\
     s == ser_request_host tk hk
  with (t <: W.token) (h <: W.token) and ()

(* ── The verified emitter ──────────────────────────────────────────────────── *)

#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"
fn http_emit_request_host
  (target: array U8.t) (target_len: SZ.t)
  (host: array U8.t) (host_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to target 't ** pts_to host 'hst ** pts_to out 'o **
    pure (Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
          W.space_free 't /\ W.space_free 'hst /\
          SZ.v target_len + SZ.v host_len + 44 < pow2 32 /\
          Seq.length 'o == 4 + SZ.v target_len + 17 + SZ.v host_len + 23)
  ensures
    pts_to target 't ** pts_to host 'hst **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
             (W.space_free 't /\ W.space_free 'hst ==>
                (exists (tk hk:W.token).
                   (tk <: Seq.seq U8.t) == 't /\ (hk <: Seq.seq U8.t) == 'hst /\
                   o' == ser_request_host tk hk))))
{
  (* head literal "GET " *)
  let mut a = 0sz;
  while (SZ.lt !a 4sz)
  invariant exists* (va:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to a va ** pts_to target 't ** pts_to host 'hst ** pts_to out sv **
    pure (
      SZ.v va <= 4 /\
      Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
      Seq.length sv == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
      (forall (k:nat). k < SZ.v va ==> Seq.index sv k == Seq.index lit_get k))
  {
    let va = !a;
    CL.lemma_lit_get_byte va;
    let bt = (if SZ.eq va 0sz then 0x47uy else if SZ.eq va 1sz then 0x45uy
              else if SZ.eq va 2sz then 0x54uy else 0x20uy);
    out.(va) <- bt;
    a := SZ.add va 1sz;
  };
  (* variable target token *)
  let mut i = 0sz;
  while (SZ.lt !i target_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi ** pts_to target 't ** pts_to host 'hst ** pts_to out sv **
    pure (
      SZ.v vi <= SZ.v target_len /\
      Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
      Seq.length sv == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (4 + j) == Seq.index 't j))
  {
    let vi = !i;
    CL.lemma_fits32 (4 + SZ.v vi);
    let dv = target.(vi);
    out.(SZ.add 4sz vi) <- dv;
    i := SZ.add vi 1sz;
  };
  (* mid literal " HTTP/1.1\r\nHost: " *)
  let mut b = 0sz;
  while (SZ.lt !b 17sz)
  invariant exists* (vb:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to b vb ** pts_to target 't ** pts_to host 'hst ** pts_to out sv **
    pure (
      SZ.v vb <= 17 /\
      Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
      Seq.length sv == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j:nat). j < SZ.v target_len ==> Seq.index sv (4 + j) == Seq.index 't j) /\
      (forall (k:nat). k < SZ.v vb ==>
         Seq.index sv (4 + SZ.v target_len + k) == Seq.index mid17 k))
  {
    let vb = !b;
    assert_norm (Seq.length mid17 == 17);
    lemma_req_host_mid_byte vb;
    CL.lemma_fits32 (4 + SZ.v target_len + SZ.v vb);
    let bt = req_host_mid_byte vb;
    out.(SZ.add (SZ.add 4sz target_len) vb) <- bt;
    b := SZ.add vb 1sz;
  };
  (* variable host token *)
  let mut j = 0sz;
  while (SZ.lt !j host_len)
  invariant exists* (vj:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to j vj ** pts_to target 't ** pts_to host 'hst ** pts_to out sv **
    pure (
      SZ.v vj <= SZ.v host_len /\
      Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
      Seq.length sv == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j0:nat). j0 < SZ.v target_len ==> Seq.index sv (4 + j0) == Seq.index 't j0) /\
      (forall (k:nat). k < 17 ==>
         Seq.index sv (4 + SZ.v target_len + k) == Seq.index mid17 k) /\
      (forall (j0:nat). j0 < SZ.v vj ==>
         Seq.index sv (4 + SZ.v target_len + 17 + j0) == Seq.index 'hst j0))
  {
    let vj = !j;
    CL.lemma_fits32 (4 + SZ.v target_len + 17 + SZ.v vj);
    let dv = host.(vj);
    out.(SZ.add (SZ.add (SZ.add 4sz target_len) 17sz) vj) <- dv;
    j := SZ.add vj 1sz;
  };
  (* tail literal "\r\nConnection: close\r\n\r\n" *)
  let mut c = 0sz;
  while (SZ.lt !c 23sz)
  invariant exists* (vc:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to c vc ** pts_to target 't ** pts_to host 'hst ** pts_to out sv **
    pure (
      SZ.v vc <= 23 /\
      Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
      Seq.length sv == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j0:nat). j0 < SZ.v target_len ==> Seq.index sv (4 + j0) == Seq.index 't j0) /\
      (forall (k:nat). k < 17 ==>
         Seq.index sv (4 + SZ.v target_len + k) == Seq.index mid17 k) /\
      (forall (j0:nat). j0 < SZ.v host_len ==>
         Seq.index sv (4 + SZ.v target_len + 17 + j0) == Seq.index 'hst j0) /\
      (forall (k:nat). k < SZ.v vc ==>
         Seq.index sv (4 + SZ.v target_len + 17 + SZ.v host_len + k)
           == Seq.index tail23 k))
  {
    let vc = !c;
    assert_norm (Seq.length tail23 == 23);
    lemma_req_host_tail_byte vc;
    CL.lemma_fits32 (4 + SZ.v target_len + 17 + SZ.v host_len + SZ.v vc);
    let bt = req_host_tail_byte vc;
    out.(SZ.add (SZ.add (SZ.add (SZ.add 4sz target_len) 17sz) host_len) vc) <- bt;
    c := SZ.add vc 1sz;
  };
  with sf. assert (pts_to out sf);
  emit_request_host_exists 't 'hst sf;
  ()
}
#pop-options
