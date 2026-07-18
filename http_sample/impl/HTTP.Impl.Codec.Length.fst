module HTTP.Impl.Codec.Length

#lang-pulse

(**
  Verified Pulse implementation of the HTTP/1.1 *Content-Length delimited* body
  codec leaves, proved against the hand-written wire format `HTTP.Wire.Length`.

  Companion of `HTTP.Impl.Codec.Chunked`.  Unlike a chunk, a Content-Length body
  segment carries NO on-wire length marker — its length is supplied out of band
  by the head's `Content-Length` field.  So the body codec is a pure byte copy
  (the direct analog of TFTP's DATA payload):

    * `http_emit_body` — copy a `len`-byte payload into `out`; `out` then equals
      `ser_body payload` (serialization is the identity on a body segment).
    * `http_recv_body` — copy the `len` body bytes off the stream into `out` and
      report whether the result is `body_ok` (its first byte, if any, is neither
      'G' nor 'H'); when it is, `http_parse out` decodes to exactly the
      `Msg_body` carrying it, with no residual.

  The `body_ok` refinement is the modeling restriction that lets a stateless
  parser tell a bare body segment from a request/response line — see
  `HTTP.Wire.Length` for the rationale.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Seq = FStar.Seq
module R = Pulse.Lib.Reference

module W = HTTP.Wire.Common
open HTTP.Wire.Length

(* Reconstruct `ser_request target` from the three regions of a filled buffer,
   exactly as `emit_chunk_serialize` does for a chunk: the head literal "GET ",
   the variable token, and the 13-byte tail " HTTP/1.1\r\n\r\n". *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let emit_request_serialize (target:W.token) (s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length s == 4 + Seq.length target + 13 /\
       (forall (k:nat). k < 4 ==> Seq.index s k == Seq.index lit_get k) /\
       (forall (j:nat). j < Seq.length target ==>
          Seq.index s (4 + j) == Seq.index target j) /\
       (forall (k:nat). k < 13 ==>
          Seq.index s (4 + Seq.length target + k)
            == Seq.index (Seq.cons W.bSP req_tail) k))
    (ensures s == ser_request target)
= let tlen = Seq.length target in
  let tail = Seq.cons W.bSP req_tail in
  assert_norm (Seq.length lit_get == 4);
  assert_norm (Seq.length tail == 13);
  Seq.lemma_eq_intro (Seq.slice s 0 4) lit_get;
  Seq.lemma_eq_intro (Seq.slice s 4 (4 + tlen)) target;
  Seq.lemma_eq_intro (Seq.slice s (4 + tlen) (4 + tlen + 13)) tail;
  Seq.lemma_eq_intro s (ser_request target)
#pop-options

(* Package the request-line correspondence as a token existential (so the Pulse
   fn's ensures needn't carry the refined `W.token` coercion), analogous to
   `emit_chunk_exists`. *)
let emit_request_exists (t s:Seq.seq U8.t)
  : Lemma
    (requires
       W.space_free t /\
       Seq.length s == 4 + Seq.length t + 13 /\
       (forall (k:nat). k < 4 ==> Seq.index s k == Seq.index lit_get k) /\
       (forall (j:nat). j < Seq.length t ==> Seq.index s (4 + j) == Seq.index t j) /\
       (forall (k:nat). k < 13 ==>
          Seq.index s (4 + Seq.length t + k) == Seq.index (Seq.cons W.bSP req_tail) k))
    (ensures (exists (tk:W.token). (tk <: Seq.seq U8.t) == t /\ s == ser_request tk))
= emit_request_serialize (t <: W.token) s;
  introduce exists (tk:W.token). (tk <: Seq.seq U8.t) == t /\ s == ser_request tk
  with (t <: W.token) and ()

(* Runtime k-th byte of the tail " HTTP/1.1\r\n\r\n" (= cons bSP req_tail). *)
inline_for_extraction
let req_tail_byte (k:SZ.t{SZ.v k < 13}) : U8.t =
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
  else if SZ.eq k 11sz then 0x0Duy
  else                      0x0Auy

let lemma_req_tail_byte (k:SZ.t{SZ.v k < 13})
  : Lemma (req_tail_byte k == Seq.index (Seq.cons W.bSP req_tail) (SZ.v k))
= assert_norm (Seq.index (Seq.cons W.bSP req_tail) 0  == 0x20uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 1  == 0x48uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 2  == 0x54uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 3  == 0x54uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 4  == 0x50uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 5  == 0x2Fuy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 6  == 0x31uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 7  == 0x2Euy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 8  == 0x31uy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 9  == 0x0Duy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 10 == 0x0Auy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 11 == 0x0Duy);
  assert_norm (Seq.index (Seq.cons W.bSP req_tail) 12 == 0x0Auy)

let lemma_lit_get_byte (k:SZ.t{SZ.v k < 4})
  : Lemma ((if SZ.eq k 0sz then 0x47uy else if SZ.eq k 1sz then 0x45uy
            else if SZ.eq k 2sz then 0x54uy else 0x20uy)
           == Seq.index lit_get (SZ.v k))
= assert_norm (Seq.index lit_get 0 == 0x47uy);
  assert_norm (Seq.index lit_get 1 == 0x45uy);
  assert_norm (Seq.index lit_get 2 == 0x54uy);
  assert_norm (Seq.index lit_get 3 == 0x20uy)

open Pulse.Lib.BoundedIntegers

(* size_t is at least 32 bits on every real target; HTTP head buffers can exceed
   F*'s SizeT 2^16 auto-`fits` line, so discharge sub-2^32 `fits` explicitly
   (the same open assumption as the chunked codec). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x


(* Introduce the body_payload existential witnessing the serialize-correspondence
   (ser_body is the identity), analogous to `emit_chunk_exists` in Chunked. *)
let emit_body_exists (d s:Seq.seq U8.t)
  : Lemma (requires body_ok d /\ s == d)
          (ensures (exists (pl:body_payload). (pl <: Seq.seq U8.t) == d /\ s == ser_body pl))
= introduce exists (pl:body_payload). (pl <: Seq.seq U8.t) == d /\ s == ser_body pl
  with (d <: body_payload) and ()

(* ------------------------------------------------------------------------ *)
(* Emit: copy a body payload verbatim (serialization is the identity).       *)
(* ------------------------------------------------------------------------ *)

(* Copy the `len`-byte body payload `data` into `out`; because `ser_body p = p`,
   `out` afterwards equals `ser_body` of the copied payload. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
fn http_emit_body
  (data: array U8.t)
  (data_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to data 'd **
    pts_to out 'o **
    pure (Seq.length 'd == SZ.v data_len /\ Seq.length 'o == SZ.v data_len /\
          body_ok 'd)
  ensures
    pts_to data 'd **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == SZ.v data_len /\ o' == 'd /\
             (body_ok 'd ==>
                (exists (pl:body_payload).
                   (pl <: Seq.seq U8.t) == 'd /\ o' == ser_body pl))))
{
  let mut i = 0sz;
  while (SZ.lt !i data_len)
  invariant exists* (vi:SZ.t) (ov:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to data 'd ** pts_to out ov **
    pure (
      SZ.v vi <= SZ.v data_len /\
      Seq.length 'd == SZ.v data_len /\
      Seq.length ov == SZ.v data_len /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index ov j == Seq.index 'd j))
  {
    let vi = !i;
    let dv = data.(vi);
    out.(vi) <- dv;
    i := SZ.add vi 1sz;
  };
  with ov. assert (pts_to out ov);
  Seq.lemma_eq_intro ov ('d <: Seq.seq U8.t);
  emit_body_exists 'd ov;
  ()
}
#pop-options

(* ------------------------------------------------------------------------ *)
(* Recv: copy the body bytes off the stream, report body_ok, prove the parse. *)
(* ------------------------------------------------------------------------ *)

(* Copy the `len`-byte body segment `body` into `out` and check `body_ok`
   (first byte, if any, is neither 'G' nor 'H').  When `ok`, `http_parse out`
   decodes to exactly the `Msg_body` carrying the copied bytes, no residual. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_recv_body (body: array U8.t) (out: array U8.t) (n: SZ.t)
  requires
    pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 'b == SZ.v n /\ Seq.length 'o == SZ.v n)
  returns ok: bool
  ensures
    pts_to body 'b **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == SZ.v n /\ o' == 'b /\
             (ok == true ==>
                (body_ok o' /\
                 http_parse o' == Some (Msg_body o', Seq.empty #U8.t)))))
{
  let mut i = 0sz;
  while (SZ.lt !i n)
  invariant exists* (vi:SZ.t) (ov:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to body 'b ** pts_to out ov **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length 'b == SZ.v n /\
      Seq.length ov == SZ.v n /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index ov j == Seq.index 'b j))
  {
    let vi = !i;
    let dv = body.(vi);
    out.(vi) <- dv;
    i := SZ.add vi 1sz;
  };
  with ov. assert (pts_to out ov);
  Seq.lemma_eq_intro ov ('b <: Seq.seq U8.t);
  let ok =
    if SZ.lt 0sz n {
      let c0 = out.(0sz);
      not (U8.eq c0 0x47uy) && not (U8.eq c0 0x48uy)
    } else {
      true
    };
  if ok {
    lemma_parse_body_exact ov;
    ok
  } else {
    ok
  }
}
#pop-options

(* ------------------------------------------------------------------------ *)
(* Emit: the request line  "GET " target " HTTP/1.1" CRLF CRLF.               *)
(* ------------------------------------------------------------------------ *)


(* Build the HTTP request line  "GET " target " HTTP/1.1" CRLF CRLF  into `out`
   (length 4 + tlen + 13), proved equal to `ser_request target`.  The two fixed
   literal regions are written by short copy loops from `req_tail_byte` /
   `lit_get`, keeping each verification condition small (cf. the head-emitter
   fix path: per-index byte function + copy loop, not straight-line Seq.upd). *)
#push-options "--z3rlimit 300 --fuel 2 --ifuel 2"
fn http_emit_request
  (target: array U8.t)
  (target_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to target 't **
    pts_to out 'o **
    pure (Seq.length 't == SZ.v target_len /\ W.space_free 't /\
          SZ.v target_len + 17 < pow2 32 /\
          Seq.length 'o == 4 + SZ.v target_len + 13)
  ensures
    pts_to target 't **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 4 + SZ.v target_len + 13 /\
             (W.space_free 't ==>
                (exists (tk:W.token).
                   (tk <: Seq.seq U8.t) == 't /\ o' == ser_request tk))))
{
  (* head literal "GET " *)
  let mut a = 0sz;
  while (SZ.lt !a 4sz)
  invariant exists* (va:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to a va **
    pts_to target 't ** pts_to out sv **
    pure (
      SZ.v va <= 4 /\
      Seq.length 't == SZ.v target_len /\
      Seq.length sv == 4 + SZ.v target_len + 13 /\
      (forall (k:nat). k < SZ.v va ==> Seq.index sv k == Seq.index lit_get k))
  {
    let va = !a;
    lemma_lit_get_byte va;
    let bt = (if SZ.eq va 0sz then 0x47uy else if SZ.eq va 1sz then 0x45uy
              else if SZ.eq va 2sz then 0x54uy else 0x20uy);
    out.(va) <- bt;
    a := SZ.add va 1sz;
  };
  (* variable token *)
  let mut i = 0sz;
  while (SZ.lt !i target_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to target 't ** pts_to out sv **
    pure (
      SZ.v vi <= SZ.v target_len /\
      Seq.length 't == SZ.v target_len /\
      Seq.length sv == 4 + SZ.v target_len + 13 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (4 + j) == Seq.index 't j))
  {
    let vi = !i;
    lemma_fits32 (4 + SZ.v vi);
    let dv = target.(vi);
    out.(SZ.add 4sz vi) <- dv;
    i := SZ.add vi 1sz;
  };
  (* tail literal " HTTP/1.1\r\n\r\n" *)
  let mut b = 0sz;
  while (SZ.lt !b 13sz)
  invariant exists* (vb:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to b vb **
    pts_to target 't ** pts_to out sv **
    pure (
      SZ.v vb <= 13 /\
      Seq.length 't == SZ.v target_len /\
      Seq.length sv == 4 + SZ.v target_len + 13 /\
      (forall (k:nat). k < 4 ==> Seq.index sv k == Seq.index lit_get k) /\
      (forall (j:nat). j < SZ.v target_len ==> Seq.index sv (4 + j) == Seq.index 't j) /\
      (forall (k:nat). k < SZ.v vb ==>
         Seq.index sv (4 + SZ.v target_len + k) == Seq.index (Seq.cons W.bSP req_tail) k))
  {
    let vb = !b;
    lemma_req_tail_byte vb;
    lemma_fits32 (4 + SZ.v target_len + SZ.v vb);
    let bt = req_tail_byte vb;
    out.(SZ.add (SZ.add 4sz target_len) vb) <- bt;
    b := SZ.add vb 1sz;
  };
  with sf. assert (pts_to out sf);
  emit_request_exists 't sf;
  ()
}
#pop-options
