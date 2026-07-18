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

open Pulse.Lib.BoundedIntegers

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
