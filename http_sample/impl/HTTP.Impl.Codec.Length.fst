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
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
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

(* Runtime k-th byte of the request-line version token "HTTP/1.1\r\n" (req_ver),
   used by the headers-tolerant request-head parser. *)
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
  : Lemma (req_ver_byte k == Seq.index req_ver (SZ.v k))
= assert_norm (Seq.index req_ver 0 == 0x48uy);
  assert_norm (Seq.index req_ver 1 == 0x54uy);
  assert_norm (Seq.index req_ver 2 == 0x54uy);
  assert_norm (Seq.index req_ver 3 == 0x50uy);
  assert_norm (Seq.index req_ver 4 == 0x2Fuy);
  assert_norm (Seq.index req_ver 5 == 0x31uy);
  assert_norm (Seq.index req_ver 6 == 0x2Euy);
  assert_norm (Seq.index req_ver 7 == 0x31uy);
  assert_norm (Seq.index req_ver 8 == 0x0Duy);
  assert_norm (Seq.index req_ver 9 == 0x0Auy)

let lemma_lit_get_byte (k:SZ.t{SZ.v k < 4})
  : Lemma ((if SZ.eq k 0sz then 0x47uy else if SZ.eq k 1sz then 0x45uy
            else if SZ.eq k 2sz then 0x54uy else 0x20uy)
           == Seq.index lit_get (SZ.v k))
= assert_norm (Seq.index lit_get 0 == 0x47uy);
  assert_norm (Seq.index lit_get 1 == 0x45uy);
  assert_norm (Seq.index lit_get 2 == 0x54uy);
  assert_norm (Seq.index lit_get 3 == 0x20uy)

(* ======================================================================== *)
(* Response head  "HTTP/1.1 " ddd " \r\nContent-Length: " dddddddd "\r\n\r\n"  *)
(* ======================================================================== *)

(* Executable single decimal digit byte (0..9 -> '0'..'9'). *)
let dig_byte (d:U8.t{U8.v d < 10}) : U8.t = U8.add 0x30uy d
let lemma_dig_byte (d:U8.t{U8.v d < 10}) : Lemma (dig_byte d == W.dig (U8.v d)) = ()

(* Extract a decimal digit (already < 10) from a U16 / U32 as its ASCII byte,
   carrying the spec correspondence in the refined return type. *)
let u16_digit (x:U16.t{U16.v x < 10}) : (b:U8.t{b == W.dig (U16.v x)})
= let d = Cast.uint16_to_uint8 x in lemma_dig_byte d; dig_byte d

let u32_digit (x:U32.t{U32.v x < 10}) : (b:U8.t{b == W.dig (U32.v x)})
= let d = Cast.uint32_to_uint8 x in lemma_dig_byte d; dig_byte d

(* Per-position bytes of the response-head fixed literals. *)
let lemma_enc_dec3_index (c:nat{c<1000})
  : Lemma (Seq.index (W.enc_dec3 c) 0 == W.dig (c/100) /\
           Seq.index (W.enc_dec3 c) 1 == W.dig ((c/10)%10) /\
           Seq.index (W.enc_dec3 c) 2 == W.dig (c%10))
= ()

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let lemma_enc_dec8_index (n:nat{n < W.max_len8})
  : Lemma
    (let hi = n/10000 in let lo = n%10000 in
     Seq.index (W.enc_dec8 n) 0 == W.dig ((hi/1000)%10) /\
     Seq.index (W.enc_dec8 n) 1 == W.dig ((hi/100)%10) /\
     Seq.index (W.enc_dec8 n) 2 == W.dig ((hi/10)%10) /\
     Seq.index (W.enc_dec8 n) 3 == W.dig (hi%10) /\
     Seq.index (W.enc_dec8 n) 4 == W.dig ((lo/1000)%10) /\
     Seq.index (W.enc_dec8 n) 5 == W.dig ((lo/100)%10) /\
     Seq.index (W.enc_dec8 n) 6 == W.dig ((lo/10)%10) /\
     Seq.index (W.enc_dec8 n) 7 == W.dig (lo%10))
= SP.append_slices (W.enc_dec4 (n/10000)) (W.enc_dec4 (n%10000))
#pop-options

(* Runtime k-th byte of resp_prefix "HTTP/1.1 ". *)
inline_for_extraction
let resp_prefix_byte (k:SZ.t{SZ.v k < 9}) : U8.t =
  if      SZ.eq k 0sz then 0x48uy else if SZ.eq k 1sz then 0x54uy
  else if SZ.eq k 2sz then 0x54uy else if SZ.eq k 3sz then 0x50uy
  else if SZ.eq k 4sz then 0x2Fuy else if SZ.eq k 5sz then 0x31uy
  else if SZ.eq k 6sz then 0x2Euy else if SZ.eq k 7sz then 0x31uy
  else                     0x20uy

let lemma_resp_prefix_byte (k:SZ.t{SZ.v k < 9})
  : Lemma (resp_prefix_byte k == Seq.index resp_prefix (SZ.v k))
= assert_norm (Seq.index resp_prefix 0 == 0x48uy);
  assert_norm (Seq.index resp_prefix 1 == 0x54uy);
  assert_norm (Seq.index resp_prefix 2 == 0x54uy);
  assert_norm (Seq.index resp_prefix 3 == 0x50uy);
  assert_norm (Seq.index resp_prefix 4 == 0x2Fuy);
  assert_norm (Seq.index resp_prefix 5 == 0x31uy);
  assert_norm (Seq.index resp_prefix 6 == 0x2Euy);
  assert_norm (Seq.index resp_prefix 7 == 0x31uy);
  assert_norm (Seq.index resp_prefix 8 == 0x20uy)

(* Runtime k-th byte of cl_tail_pre " \r\nContent-Length: ". *)
inline_for_extraction
let cl_pre_byte (k:SZ.t{SZ.v k < 19}) : U8.t =
  if      SZ.eq k 0sz  then 0x20uy else if SZ.eq k 1sz  then 0x0Duy
  else if SZ.eq k 2sz  then 0x0Auy else if SZ.eq k 3sz  then 0x43uy
  else if SZ.eq k 4sz  then 0x6Fuy else if SZ.eq k 5sz  then 0x6Euy
  else if SZ.eq k 6sz  then 0x74uy else if SZ.eq k 7sz  then 0x65uy
  else if SZ.eq k 8sz  then 0x6Euy else if SZ.eq k 9sz  then 0x74uy
  else if SZ.eq k 10sz then 0x2Duy else if SZ.eq k 11sz then 0x4Cuy
  else if SZ.eq k 12sz then 0x65uy else if SZ.eq k 13sz then 0x6Euy
  else if SZ.eq k 14sz then 0x67uy else if SZ.eq k 15sz then 0x74uy
  else if SZ.eq k 16sz then 0x68uy else if SZ.eq k 17sz then 0x3Auy
  else                      0x20uy

(* seq_of_list index reduction gets stuck for deep indices (>~12) into a long
   literal; route through List.Tot.index (which does reduce) via
   lemma_seq_of_list_index over the underlying list. *)
let cl_pre_list : list U8.t =
  [0x20uy;0x0Duy;0x0Auy;0x43uy;0x6Fuy;0x6Euy;0x74uy;0x65uy;0x6Euy;0x74uy;
   0x2Duy;0x4Cuy;0x65uy;0x6Euy;0x67uy;0x74uy;0x68uy;0x3Auy;0x20uy]

#push-options "--z3rlimit 200"
let lemma_cl_pre_byte (k:SZ.t{SZ.v k < 19})
  : Lemma (requires Seq.length cl_tail_pre == 19)
          (ensures cl_pre_byte k == Seq.index cl_tail_pre (SZ.v k))
= assert_norm (cl_tail_pre == Seq.seq_of_list cl_pre_list);
  assert_norm (List.Tot.length cl_pre_list == 19);
  FStar.Seq.Properties.lemma_seq_of_list_index cl_pre_list (SZ.v k);
  assert_norm (List.Tot.index cl_pre_list 0  == 0x20uy);
  assert_norm (List.Tot.index cl_pre_list 1  == 0x0Duy);
  assert_norm (List.Tot.index cl_pre_list 2  == 0x0Auy);
  assert_norm (List.Tot.index cl_pre_list 3  == 0x43uy);
  assert_norm (List.Tot.index cl_pre_list 4  == 0x6Fuy);
  assert_norm (List.Tot.index cl_pre_list 5  == 0x6Euy);
  assert_norm (List.Tot.index cl_pre_list 6  == 0x74uy);
  assert_norm (List.Tot.index cl_pre_list 7  == 0x65uy);
  assert_norm (List.Tot.index cl_pre_list 8  == 0x6Euy);
  assert_norm (List.Tot.index cl_pre_list 9  == 0x74uy);
  assert_norm (List.Tot.index cl_pre_list 10 == 0x2Duy);
  assert_norm (List.Tot.index cl_pre_list 11 == 0x4Cuy);
  assert_norm (List.Tot.index cl_pre_list 12 == 0x65uy);
  assert_norm (List.Tot.index cl_pre_list 13 == 0x6Euy);
  assert_norm (List.Tot.index cl_pre_list 14 == 0x67uy);
  assert_norm (List.Tot.index cl_pre_list 15 == 0x74uy);
  assert_norm (List.Tot.index cl_pre_list 16 == 0x68uy);
  assert_norm (List.Tot.index cl_pre_list 17 == 0x3Auy);
  assert_norm (List.Tot.index cl_pre_list 18 == 0x20uy)

(* Runtime k-th byte of cl_tail_post "\r\n\r\n". *)
#pop-options
inline_for_extraction
let cl_post_byte (k:SZ.t{SZ.v k < 4}) : U8.t =
  if      SZ.eq k 0sz then 0x0Duy else if SZ.eq k 1sz then 0x0Auy
  else if SZ.eq k 2sz then 0x0Duy else 0x0Auy

let lemma_cl_post_byte (k:SZ.t{SZ.v k < 4})
  : Lemma (cl_post_byte k == Seq.index cl_tail_post (SZ.v k))
= assert_norm (Seq.index cl_tail_post 0 == 0x0Duy);
  assert_norm (Seq.index cl_tail_post 1 == 0x0Auy);
  assert_norm (Seq.index cl_tail_post 2 == 0x0Duy);
  assert_norm (Seq.index cl_tail_post 3 == 0x0Auy)


(* Bridge FStar.UInt.mod (= a - (a/b)*b) to Prims % so U16.rem / U32.rem digit
   values connect to the enc_dec3 / enc_dec8 spec (which use Prims / and %). *)
let lemma_uint_mod (n:nat) (a:nat{a < pow2 n}) (b:pos{b < pow2 n})
  : Lemma (FStar.UInt.mod #n a b == a % b)
= FStar.Math.Lemmas.euclidean_division_definition a b

(* Opaque view of the whole response head, so z3 does not unfold ser_response
   (and its enc_dec3 / enc_dec8 arithmetic) while `Seq.index (respbytes ..) j`
   is carried unchanged through the copy-loop invariants.  All the byte-level
   facts we ever need are exposed once, up front, by `lemma_respbytes_index`. *)
[@@ "opaque_to_smt"]
let respbytes (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
              (len:U32.t{U32.v len < W.max_len8}) : Seq.seq U8.t
= ser_response (code <: status_code) (U32.v len <: content_len)

let lemma_respbytes_reveal
      (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
      (len:U32.t{U32.v len < W.max_len8})
  : Lemma (respbytes code len == ser_response (code <: status_code) (U32.v len <: content_len))
= reveal_opaque (`%respbytes) (respbytes code len)

(* The full per-position byte inventory of the response head, exposed once.
   The five append segments give the literal facts (SMT-patterned index-append
   lemmas fire on the revealed ser_response), and enc_dec3 / enc_dec8 index
   lemmas turn the two digit runs into explicit W.dig terms. *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
let lemma_respbytes_index
      (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
      (len:U32.t{U32.v len < W.max_len8})
  : Lemma
    (ensures (
       let s = respbytes code len in
       let c = U16.v code in let n = U32.v len in
       let hi = n / 10000 in let lo = n % 10000 in
       Seq.length s == 43 /\
       (forall (k:nat). k < 9  ==> Seq.index s k == Seq.index resp_prefix k) /\
       Seq.index s 9  == W.dig (c / 100) /\
       Seq.index s 10 == W.dig ((c / 10) % 10) /\
       Seq.index s 11 == W.dig (c % 10) /\
       (forall (k:nat). k < 19 ==> Seq.index s (12 + k) == Seq.index cl_tail_pre k) /\
       Seq.index s 31 == W.dig ((hi / 1000) % 10) /\
       Seq.index s 32 == W.dig ((hi / 100) % 10) /\
       Seq.index s 33 == W.dig ((hi / 10) % 10) /\
       Seq.index s 34 == W.dig (hi % 10) /\
       Seq.index s 35 == W.dig ((lo / 1000) % 10) /\
       Seq.index s 36 == W.dig ((lo / 100) % 10) /\
       Seq.index s 37 == W.dig ((lo / 10) % 10) /\
       Seq.index s 38 == W.dig (lo % 10) /\
       (forall (k:nat). k < 4  ==> Seq.index s (39 + k) == Seq.index cl_tail_post k)))
= reveal_opaque (`%respbytes) (respbytes code len);
  assert_norm (Seq.length resp_prefix == 9);
  assert (Seq.length cl_tail_pre == 19);
  assert_norm (Seq.length cl_tail_post == 4);
  lemma_enc_dec3_index (U16.v code);
  lemma_enc_dec8_index (U32.v len)
#pop-options

(* Lightweight per-region literal facts, carrying NO digit arithmetic, used to
   discharge the copy-loop invariants without dragging enc_dec3 / enc_dec8 into
   the (per-iteration) preservation queries. *)
let lemma_respbytes_len
      (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
      (len:U32.t{U32.v len < W.max_len8})
  : Lemma (Seq.length (respbytes code len) == 43)
= lemma_respbytes_reveal code len;
  assert_norm (Seq.length resp_prefix == 9);
  assert (Seq.length cl_tail_pre == 19);
  assert_norm (Seq.length cl_tail_post == 4)

(* rem-by-10 bridge for U32. *)
let lemma_mod10_32 (x:U32.t) : Lemma (U32.v (U32.rem x 10ul) == (U32.v x) % 10)
= assert_norm (U32.v 10ul == 10);
  lemma_uint_mod 32 (U32.v x) (U32.v 10ul)

(* Finalize: a fully-filled buffer equal to `respbytes code len` is
   `ser_response` of the (coerced) code/len, packaged as the existential the
   Pulse fn advertises. *)
let lemma_emit_response_final
      (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
      (len:U32.t{U32.v len < W.max_len8})
      (s:Seq.seq U8.t)
  : Lemma
    (requires s == respbytes code len)
    (ensures (exists (co:status_code) (ln:content_len).
                U16.v co == U16.v code /\ ln == U32.v len /\ s == ser_response co ln))
= lemma_respbytes_reveal code len;
  introduce exists (co:status_code) (ln:content_len).
    U16.v co == U16.v code /\ ln == U32.v len /\ s == ser_response co ln
  with (code <: status_code) (U32.v len <: content_len) and ()


(* A byte sequence with no embedded space (0x20) is `space_free` (a W.token).
   Induction over the recursive `space_free`, which peels one byte at a time. *)
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

(* Parse-inversion for the request head.  Given a buffer `inp` whose bytes match
   the request-line layout "GET " target " HTTP/1.1\r\n\r\n" with the FIRST space
   at position `sp` (so target = inp[4..sp] is space-free) and the 12-byte tail
   `req_tail` filling inp[sp+1..], `inp == ser_request target`, so the spec's
   forward round-trip law certifies `http_parse inp == Some (Msg_request target,
   empty)`.  Reuses `emit_request_serialize`. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_recv_request_ok (inp:Seq.seq U8.t) (sp:nat)
  : Lemma
    (requires
       4 <= sp /\ sp + 13 == Seq.length inp /\
       (forall (k:nat). k < 4 ==> Seq.index inp k == Seq.index lit_get k) /\
       (forall (j:nat). 4 <= j /\ j < sp ==> Seq.index inp j =!= W.bSP) /\
       Seq.index inp sp == W.bSP /\
       (forall (k:nat). k < 12 ==>
          Seq.index inp (sp + 1 + k) == Seq.index (Seq.cons W.bSP req_tail) (k + 1)))
    (ensures (exists (tk:W.token).
       (tk <: Seq.seq U8.t) == Seq.slice inp 4 sp /\
       http_parse inp == Some (Msg_request tk, Seq.empty #U8.t)))
= let target = Seq.slice inp 4 sp in
  assert (Seq.length target == sp - 4);
  assert (forall (m:nat). m < Seq.length target ==> Seq.index target m == Seq.index inp (4 + m));
  lemma_space_free_no_space target;
  let tail = Seq.cons W.bSP req_tail in
  assert_norm (Seq.length tail == 13);
  assert (Seq.index tail 0 == W.bSP);
  assert (forall (k:nat). k < 13 ==>
            Seq.index inp (4 + Seq.length target + k) == Seq.index tail k);
  emit_request_serialize (target <: W.token) inp;
  lemma_http_parse_serialize_exact (Msg_request (target <: W.token));
  introduce exists (tk:W.token).
      (tk <: Seq.seq U8.t) == Seq.slice inp 4 sp /\
      http_parse inp == Some (Msg_request tk, Seq.empty #U8.t)
  with (target <: W.token) and ()
#pop-options

(* Headers-tolerant parse-inversion for a REAL client's request head.  Given a
   buffer `inp` whose first bytes are "GET ", whose FIRST space (at position `sp`)
   bounds a space-free target = inp[4..sp], and whose 10 bytes after that space
   are the version token req_ver = "HTTP/1.1\r\n", `parse_request_line inp` returns
   exactly that target -- IGNORING every byte after req_ver (all header lines and
   the terminating CRLFCRLF).  Unlike `lemma_recv_request_ok`, `inp` is NOT fully
   reconstructed: only its request-line prefix is constrained, so curl's headers
   are accepted.  Proof: rebuild inp[4..] as  target ++ (SP :: inp[sp+1..])  so
   `split_sp` cuts at the first space, then match the "GET " prefix and req_ver. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let lemma_parse_request_line_ok (inp:Seq.seq U8.t) (sp:nat)
  : Lemma
    (requires
       4 <= sp /\ sp + 11 <= Seq.length inp /\
       (forall (k:nat). k < 4 ==> Seq.index inp k == Seq.index lit_get k) /\
       (forall (j:nat). 4 <= j /\ j < sp ==> Seq.index inp j =!= W.bSP) /\
       Seq.index inp sp == W.bSP /\
       (forall (k:nat). k < 10 ==>
          Seq.index inp (sp + 1 + k) == Seq.index req_ver k))
    (ensures (exists (tk:W.token).
       (tk <: Seq.seq U8.t) == Seq.slice inp 4 sp /\
       parse_request_line inp == Some tk))
= let n = Seq.length inp in
  (* "GET " prefix matches *)
  Seq.lemma_eq_intro (Seq.slice inp 0 4) lit_get;
  W.lemma_bseq_eq (Seq.slice inp 0 4) lit_get;
  let rest0 = Seq.slice inp 4 n in
  let target = Seq.slice inp 4 sp in
  lemma_space_free_no_space target;
  let tlrest = Seq.slice inp (sp + 1) n in
  let mid = Seq.cons W.bSP tlrest in
  let apnd = Seq.append target mid in
  assert (Seq.length mid == n - sp);
  assert (Seq.length apnd == n - 4);
  (* rest0 == target ++ (SP :: inp[sp+1..]) *)
  introduce forall (j:nat{j < Seq.length rest0}).
      Seq.index rest0 j == Seq.index apnd j
  with (
    let tlen = sp - 4 in
    if j < tlen then Seq.lemma_index_app1 target mid j
    else begin
      Seq.lemma_index_app2 target mid j;
      (if j > tlen then () else ())   (* j == tlen: mid.[0] == bSP == inp.[sp] *)
    end
  );
  Seq.lemma_eq_intro rest0 apnd;
  (* split_sp cuts at the first space, recovering (target, tlrest) *)
  W.split_sp_append (target <: W.token) tlrest;
  assert (W.split_sp rest0 == Some (target, tlrest));
  (* the 10 bytes after the space are the version token "HTTP/1.1\r\n" *)
  Seq.lemma_eq_intro (Seq.slice tlrest 0 10) req_ver;
  W.lemma_bseq_eq (Seq.slice tlrest 0 10) req_ver;
  introduce exists (tk:W.token).
      (tk <: Seq.seq U8.t) == Seq.slice inp 4 sp /\
      parse_request_line inp == Some tk
  with (target <: W.token) and ()
#pop-options

(* ======================================================================== *)
(* Variable-width Content-Length response head  (RFC 9112 §6.2)              *)
(* "HTTP/1.1 " ddd " \r\nContent-Length: " D..D "\r\n\r\n"  (minimal decimal) *)
(* ======================================================================== *)

(* Number of decimal digits `enc_dec_var n` emits (minimal width, "0" -> 1). *)
noextract
let rec dec_width (n:nat) : Tot (d:pos) (decreases n) =
  if n < 10 then 1 else 1 + dec_width (n / 10)

(* Loose bound used only to discharge SizeT `fits` for the digit count. *)
let rec lemma_dec_width_le (n:nat)
  : Lemma (ensures dec_width n <= n + 1) (decreases n)
= if n < 10 then () else lemma_dec_width_le (n / 10)

(* `dec_width` is monotone; used to cap a 32-bit length's digit count at 10. *)
let rec lemma_dec_width_mono (a:nat) (b:nat)
  : Lemma (requires a <= b) (ensures dec_width a <= dec_width b) (decreases b)
= if b < 10 then ()
  else if a < 10 then ()
  else lemma_dec_width_mono (a / 10) (b / 10)

(* A 32-bit value has at most 10 decimal digits. *)
let lemma_dec_width_u32_le10 (n:U32.t)
  : Lemma (dec_width (U32.v n) <= 10)
= lemma_dec_width_mono (U32.v n) 4294967295;
  assert_norm (dec_width 4294967295 == 10)

(* `enc_dec_var n` has exactly `dec_width n` bytes. *)
let rec lemma_enc_dec_var_len (n:nat)
  : Lemma (ensures Seq.length (W.enc_dec_var n) == dec_width n) (decreases n)
= if n < 10 then () else lemma_enc_dec_var_len (n / 10)

(* `dig` is a section of `undig` on decimal-digit bytes. *)
let lemma_dig_undig_inv (b:U8.t)
  : Lemma (requires W.is_dec b) (ensures W.dig (W.undig b) == b) = ()

(* Every byte of a decimal run is a decimal digit. *)
let rec lemma_all_dec_index (h:Seq.seq U8.t) (i:nat)
  : Lemma (requires W.all_dec h /\ i < Seq.length h)
          (ensures W.is_dec (Seq.index h i)) (decreases i)
= W.lemma_all_dec_tail h;
  if i = 0 then ()
  else lemma_all_dec_index (Seq.slice h 1 (Seq.length h)) (i - 1)

(* A prefix of a decimal run is a decimal run. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec lemma_all_dec_prefix (h:Seq.seq U8.t) (m:nat)
  : Lemma (requires W.all_dec h /\ m <= Seq.length h)
          (ensures W.all_dec (Seq.slice h 0 m)) (decreases m)
= if m = 0 then Seq.lemma_eq_intro (Seq.slice h 0 m) (Seq.empty #U8.t)
  else begin
    W.lemma_all_dec_tail h;
    let tl = Seq.slice h 1 (Seq.length h) in
    lemma_all_dec_prefix tl (m - 1);
    let p = Seq.slice h 0 m in
    Seq.lemma_eq_intro (Seq.slice p 1 m) (Seq.slice tl 0 (m - 1))
  end
#pop-options

(* Split the (j+1)-prefix of `h` into its j-prefix and the singleton at j. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_slice_snoc (h:Seq.seq U8.t) (j:nat)
  : Lemma (requires j + 1 <= Seq.length h)
          (ensures Seq.slice h 0 (j + 1)
                   == Seq.append (Seq.slice h 0 j) (Seq.create 1 (Seq.index h j)))
= Seq.lemma_eq_intro (Seq.slice h 0 (j + 1))
                     (Seq.append (Seq.slice h 0 j) (Seq.create 1 (Seq.index h j)))
#pop-options

(* Euclidean split of `p*10 + r` (0 <= r < 10). *)
let lemma_divmod10 (p:nat) (r:nat{r < 10})
  : Lemma ((p * 10 + r) % 10 == r /\ (p * 10 + r) / 10 == p)
= FStar.Math.Lemmas.lemma_mod_plus r p 10;
  FStar.Math.Lemmas.lemma_div_plus r p 10

(* Opaque view of the whole variable-width response head — the analog of
   `respbytes` for the fixed head.  Keeps z3 from unfolding ser_response_var
   (and enc_dec_var's recursion) while `Seq.index (srv_bytes ..) m` rides the
   copy-loop invariants; all byte facts are exposed once by `lemma_srv_index`. *)
[@@ "opaque_to_smt"]
noextract
let srv_bytes (code:U16.t{100 <= U16.v code /\ U16.v code < 1000}) (len:U32.t)
  : Seq.seq U8.t
= ser_response_var (code <: status_code) (U32.v len)

let lemma_srv_reveal (code:U16.t{100 <= U16.v code /\ U16.v code < 1000}) (len:U32.t)
  : Lemma (srv_bytes code len == ser_response_var (code <: status_code) (U32.v len))
= reveal_opaque (`%srv_bytes) (srv_bytes code len)

(* Per-position byte inventory of the variable-width head, exposed once.  The
   five append segments (prefix, 3 status digits, cl-pre, D decimal digits,
   cl-post) resolve via the SMT-patterned index-append lemmas on the revealed
   ser_response_var; the digit run stays abstract as `Seq.index ee (m-31)`. *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
let lemma_srv_index (code:U16.t{100 <= U16.v code /\ U16.v code < 1000}) (len:U32.t)
  : Lemma
    (ensures (
       let s = srv_bytes code len in
       let ee = W.enc_dec_var (U32.v len) in
       let d = Seq.length ee in
       let c = U16.v code in
       Seq.length resp_prefix == 9 /\
       Seq.length cl_tail_pre == 19 /\
       Seq.length cl_tail_post == 4 /\
       Seq.length s == 35 + d /\
       (forall (k:nat{k < 9}).  Seq.index s k == Seq.index resp_prefix k) /\
       Seq.index s 9  == Seq.index (W.enc_dec3 c) 0 /\
       Seq.index s 10 == Seq.index (W.enc_dec3 c) 1 /\
       Seq.index s 11 == Seq.index (W.enc_dec3 c) 2 /\
       (forall (k:nat{k < 19}). Seq.index s (12 + k) == Seq.index cl_tail_pre k) /\
       (forall (k:nat{k < d}).  Seq.index s (31 + k) == Seq.index ee k) /\
       (forall (k:nat{k < 4}).  Seq.index s (31 + d + k) == Seq.index cl_tail_post k)))
= reveal_opaque (`%srv_bytes) (srv_bytes code len);
  assert_norm (Seq.length resp_prefix == 9);
  assert (Seq.length cl_tail_pre == 19);
  assert_norm (Seq.length cl_tail_post == 4)
#pop-options

(* Merge the three region correspondences (prefix [0,31), digits [31,31+d),
   tail [31+d,35+d)) into whole-buffer equality — the finalizer for the emit. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let lemma_combine3 (sf srv:Seq.seq U8.t) (d:nat)
  : Lemma
    (requires
       Seq.length sf == 35 + d /\ Seq.length srv == 35 + d /\
       (forall (k:nat).  k < 31 ==> Seq.index sf k == Seq.index srv k) /\
       (forall (jj:nat). jj < d ==> Seq.index sf (31 + jj) == Seq.index srv (31 + jj)) /\
       (forall (kk:nat). kk < 4 ==> Seq.index sf (31 + d + kk) == Seq.index srv (31 + d + kk)))
    (ensures sf == srv)
= introduce forall (i:nat{i < Seq.length sf}). Seq.index sf i == Seq.index srv i
  with (
    if i < 31 then ()
    else if i < 31 + d then
      assert (Seq.index sf (31 + (i - 31)) == Seq.index srv (31 + (i - 31)))
    else
      assert (Seq.index sf (31 + d + (i - 31 - d)) == Seq.index srv (31 + d + (i - 31 - d)))
  );
  Seq.lemma_eq_intro sf srv
#pop-options

(* Finalize: a fully-filled buffer equal to `srv_bytes code len` is
   `ser_response_var` of the (coerced) code/len, packaged as the guarded
   existential the variable-width emitter advertises. *)
let lemma_emit_response_var_final
      (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
      (len:U32.t)
      (s:Seq.seq U8.t)
  : Lemma
    (requires s == srv_bytes code len)
    (ensures (exists (co:status_code).
                U16.v co == U16.v code /\ s == ser_response_var co (U32.v len)))
= lemma_srv_reveal code len;
  introduce exists (co:status_code).
    U16.v co == U16.v code /\ s == ser_response_var co (U32.v len)
  with (code <: status_code) and ()

open Pulse.Lib.BoundedIntegers

(* size_t is at least 32 bits on every real target; HTTP head buffers can exceed
   F*'s SizeT 2^16 auto-`fits` line, so discharge sub-2^32 `fits` explicitly
   (the same open assumption as the chunked codec). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x

(* Executable decimal digit count, carrying its spec correspondence in the
   refined return type (used to size/scan the D-digit region at runtime). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec dec_width_u32 (n:U32.t)
  : Tot (d:SZ.t{SZ.v d == dec_width (U32.v n)}) (decreases (U32.v n))
= if U32.lt n 10ul then 1sz
  else begin
    let r = dec_width_u32 (U32.div n 10ul) in
    lemma_dec_width_le (U32.v n / 10);
    lemma_fits32 (1 + SZ.v r);
    SZ.add 1sz r
  end
#pop-options

(* Executable k-th byte of the head PREFIX region [0,31): the 9-byte literal
   "HTTP/1.1 ", the 3 status digits, and the 19-byte " \r\nContent-Length: ". *)
inline_for_extraction
let head_pre (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
             (k:SZ.t{SZ.v k < 31}) : U8.t =
  if SZ.lt k 9sz then resp_prefix_byte k
  else if SZ.lt k 12sz then
    (if SZ.eq k 9sz then u16_digit (U16.div code 100us)
     else if SZ.eq k 10sz then u16_digit (U16.rem (U16.div code 10us) 10us)
     else u16_digit (U16.rem code 10us))
  else cl_pre_byte (SZ.sub k 12sz)

(* head_pre agrees with `srv_bytes code len` at every prefix position (k<31). *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
let lemma_head_pre (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
                   (len:U32.t) (k:SZ.t{SZ.v k < 31})
  : Lemma (Seq.length (srv_bytes code len) == 35 + Seq.length (W.enc_dec_var (U32.v len)) /\
           head_pre code k == Seq.index (srv_bytes code len) (SZ.v k))
= lemma_srv_index code len;
  assert_norm (Seq.length resp_prefix == 9);
  assert (Seq.length cl_tail_pre == 19);
  assert_norm (U16.v 100us == 100);
  assert_norm (U16.v 10us == 10);
  if SZ.lt k 9sz then lemma_resp_prefix_byte k
  else if SZ.lt k 12sz then begin
    lemma_uint_mod 16 (U16.v (U16.div code 10us)) (U16.v 10us);
    lemma_uint_mod 16 (U16.v code) (U16.v 10us);
    lemma_enc_dec3_index (U16.v code)
  end
  else lemma_cl_pre_byte (SZ.sub k 12sz)
#pop-options


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
  decreases (Prims.op_Subtraction (SZ.v data_len) (SZ.v (!i)))
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
  decreases (Prims.op_Subtraction (SZ.v n) (SZ.v (!i)))
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
  decreases (Prims.op_Subtraction (SZ.v 4sz) (SZ.v (!a)))
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
  decreases (Prims.op_Subtraction (SZ.v target_len) (SZ.v (!i)))
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
  decreases (Prims.op_Subtraction (SZ.v 13sz) (SZ.v (!b)))
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

(* Executable k-th byte of the whole response head.  A single straight-line
   dispatch: literal regions via the per-index literal helpers, the 3 status
   digits and 8 Content-Length digits via u16_digit / u32_digit. *)
inline_for_extraction
let head_byte (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
              (len:U32.t{U32.v len < W.max_len8})
              (k:SZ.t{SZ.v k < 43}) : U8.t =
  if SZ.lt k 9sz then resp_prefix_byte k
  else if SZ.lt k 12sz then
    (if SZ.eq k 9sz then u16_digit (U16.div code 100us)
     else if SZ.eq k 10sz then u16_digit (U16.rem (U16.div code 10us) 10us)
     else u16_digit (U16.rem code 10us))
  else if SZ.lt k 31sz then cl_pre_byte (SZ.sub k 12sz)
  else if SZ.lt k 39sz then
    (let hi = U32.div len 10000ul in
     let lo = U32.rem len 10000ul in
     if SZ.eq k 31sz then u32_digit (U32.rem (U32.div hi 1000ul) 10ul)
     else if SZ.eq k 32sz then u32_digit (U32.rem (U32.div hi 100ul) 10ul)
     else if SZ.eq k 33sz then u32_digit (U32.rem (U32.div hi 10ul) 10ul)
     else if SZ.eq k 34sz then u32_digit (U32.rem hi 10ul)
     else if SZ.eq k 35sz then u32_digit (U32.rem (U32.div lo 1000ul) 10ul)
     else if SZ.eq k 36sz then u32_digit (U32.rem (U32.div lo 100ul) 10ul)
     else if SZ.eq k 37sz then u32_digit (U32.rem (U32.div lo 10ul) 10ul)
     else u32_digit (U32.rem lo 10ul))
  else cl_post_byte (SZ.sub k 39sz)

(* head_byte agrees with `respbytes code len` at every position.  All the
   digit arithmetic (UInt.mod -> % bridges) lives here; the caller loop stays
   trivial.  Split up front so each range/case is a small, cheap query. *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 2"
let lemma_head_byte (code:U16.t{100 <= U16.v code /\ U16.v code < 1000})
                    (len:U32.t{U32.v len < W.max_len8})
                    (k:SZ.t{SZ.v k < 43})
  : Lemma (Seq.length (respbytes code len) == 43 /\
           head_byte code len k == Seq.index (respbytes code len) (SZ.v k))
= lemma_respbytes_index code len;
  assert_norm (Seq.length resp_prefix == 9);
  assert (Seq.length cl_tail_pre == 19);
  assert_norm (Seq.length cl_tail_post == 4);
  assert_norm (U16.v 100us == 100);
  assert_norm (U16.v 10us == 10);
  assert_norm (U32.v 10000ul == 10000);
  assert_norm (U32.v 1000ul == 1000);
  assert_norm (U32.v 100ul == 100);
  assert_norm (U32.v 10ul == 10);
  if SZ.lt k 9sz then lemma_resp_prefix_byte k
  else if SZ.lt k 12sz then begin
    lemma_uint_mod 16 (U16.v (U16.div code 10us)) (U16.v 10us);
    lemma_uint_mod 16 (U16.v code) (U16.v 10us);
    lemma_enc_dec3_index (U16.v code)
  end
  else if SZ.lt k 31sz then lemma_cl_pre_byte (SZ.sub k 12sz)
  else if SZ.lt k 39sz then begin
    let hi = U32.div len 10000ul in
    let lo = U32.rem len 10000ul in
    lemma_mod10_32 (U32.div hi 1000ul);
    lemma_mod10_32 (U32.div hi 100ul);
    lemma_mod10_32 (U32.div hi 10ul);
    lemma_mod10_32 hi;
    lemma_mod10_32 (U32.div lo 1000ul);
    lemma_mod10_32 (U32.div lo 100ul);
    lemma_mod10_32 (U32.div lo 10ul);
    lemma_mod10_32 lo;
    lemma_enc_dec8_index (U32.v len)
  end
  else lemma_cl_post_byte (SZ.sub k 39sz)
#pop-options

(* Build the HTTP response head  "HTTP/1.1 " ddd " \r\nContent-Length: " dddddddd
   "\r\n\r\n"  into `out` (length 43), proved equal to `ser_response code len`.
   One copy loop drives the whole head from `head_byte`, carrying a single
   correspondence invariant `out == respbytes code len` up to the filled index. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_emit_response
  (code: U16.t)
  (len: U32.t)
  (out: array U8.t)
  requires
    pts_to out 'o **
    pure (Prims.op_LessThanOrEqual 100 (U16.v code) /\
          Prims.op_LessThan (U16.v code) 1000 /\
          Prims.op_LessThan (U32.v len) W.max_len8 /\
          Seq.length 'o == 43)
  ensures
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 43 /\
             ((Prims.op_LessThanOrEqual 100 (U16.v code) /\
               Prims.op_LessThan (U16.v code) 1000 /\
               Prims.op_LessThan (U32.v len) W.max_len8) ==>
              (exists (co:status_code) (ln:content_len).
                 U16.v co == U16.v code /\ ln == U32.v len /\
                 o' == ser_response co ln))))
{
  lemma_respbytes_len code len;
  let mut i = 0sz;
  while (SZ.lt !i 43sz)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi ** pts_to out sv **
    pure (SZ.v vi <= 43 /\ Seq.length sv == 43 /\ Seq.length (respbytes code len) == 43 /\
      (forall (k:nat). k < SZ.v vi ==> Seq.index sv k == Seq.index (respbytes code len) k))
  decreases (Prims.op_Subtraction (SZ.v 43sz) (SZ.v (!i)))
  {
    let vi = !i;
    lemma_head_byte code len vi;
    let bt = head_byte code len vi;
    out.(vi) <- bt;
    i := SZ.add vi 1sz;
  };
  with sf. assert (pts_to out sf);
  lemma_respbytes_len code len;
  Seq.lemma_eq_intro sf (respbytes code len);
  lemma_emit_response_final code len sf;
  ()
}
#pop-options

(* Build the variable-width HTTP response head
   "HTTP/1.1 " ddd " \r\nContent-Length: " D..D "\r\n\r\n"  into `out`
   (length 35 + dec_width len), proved equal to `ser_response_var code len`.
   Three phases over one `out == srv_bytes code len` correspondence: the 31-byte
   prefix (left-to-right copy loop from head_pre), the D decimal digits filled
   RIGHT-TO-LEFT off `rem := rem/10` (each digit `= enc_dec_var len` at that pos
   via the dec_dec_var snoc law), then the 4-byte "\r\n\r\n" tail. *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
fn http_emit_response_var (code: U16.t) (len: U32.t) (out: array U8.t)
  requires
    pts_to out 'o **
    pure (Prims.op_LessThanOrEqual 100 (U16.v code) /\
          Prims.op_LessThan (U16.v code) 1000 /\
          Seq.length 'o == Prims.op_Addition 35 (dec_width (U32.v len)))
  ensures
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == Prims.op_Addition 35 (dec_width (U32.v len)) /\
             ((Prims.op_LessThanOrEqual 100 (U16.v code) /\
               Prims.op_LessThan (U16.v code) 1000) ==>
              (exists (co:status_code).
                 U16.v co == U16.v code /\
                 o' == ser_response_var co (U32.v len)))))
{
  lemma_enc_dec_var_len (U32.v len);        (* length ee == dec_width len == d *)
  W.lemma_enc_dec_var_roundtrip (U32.v len); (* all_dec ee /\ dec_dec_var ee == len *)
  lemma_srv_index code len;                 (* length srv == 35 + d *)
  let dcount = dec_width_u32 len;           (* SZ.v dcount == d *)
  lemma_dec_width_u32_le10 len;             (* d <= 10, so 31+d, 35+d fit SizeT *)

  (* Phase 1: prefix [0,31) — left-to-right copy from head_pre. *)
  let mut a = 0sz;
  while (SZ.lt !a 31sz)
  invariant exists* (va:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to a va ** pts_to out sv **
    pure (
      SZ.v va <= 31 /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == Prims.op_Addition 35 (SZ.v dcount) /\
      Seq.length (srv_bytes code len) == Prims.op_Addition 35 (SZ.v dcount) /\
      (forall (k:nat). k < SZ.v va ==> Seq.index sv k == Seq.index (srv_bytes code len) k))
  decreases (Prims.op_Subtraction (SZ.v 31sz) (SZ.v (!a)))
  {
    let va = !a;
    lemma_head_pre code len va;
    let bt = head_pre code va;
    out.(va) <- bt;
    a := SZ.add va 1sz;
  };

  (* Phase 2: digits [31, 31+d) — right-to-left, peeling low digits off rem. *)
  let mut pos = SZ.add 31sz dcount;
  let mut rem = len;
  lemma_all_dec_prefix (W.enc_dec_var (U32.v len)) (SZ.v dcount);
  while (SZ.lt 31sz !pos)
  invariant exists* (vpos:SZ.t) (vrem:U32.t) (sv:Seq.seq U8.t).
    R.pts_to pos vpos ** R.pts_to rem vrem ** pts_to out sv **
    pure (
      31 <= SZ.v vpos /\ SZ.v vpos <= Prims.op_Addition 31 (SZ.v dcount) /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == Prims.op_Addition 35 (SZ.v dcount) /\
      Seq.length (srv_bytes code len) == Prims.op_Addition 35 (SZ.v dcount) /\
      (forall (k:nat). k < 31 ==> Seq.index sv k == Seq.index (srv_bytes code len) k) /\
      (forall (jj:nat).
         (Prims.op_Subtraction (SZ.v vpos) 31 <= jj /\ jj < SZ.v dcount) ==>
         Seq.index sv (Prims.op_Addition 31 jj) == Seq.index (srv_bytes code len) (Prims.op_Addition 31 jj)) /\
      W.all_dec (Seq.slice (W.enc_dec_var (U32.v len)) 0 (Prims.op_Subtraction (SZ.v vpos) 31)) /\
      Prims.op_Equality #Prims.nat (U32.v vrem)
        (W.dec_dec_var (Seq.slice (W.enc_dec_var (U32.v len)) 0 (Prims.op_Subtraction (SZ.v vpos) 31))))
  decreases (SZ.v (!pos))
  {
    let vpos = !pos;
    let vrem = !rem;
    let pos' = SZ.sub vpos 1sz;              (* absolute position to write, in [31,31+d) *)
    let jpos = SZ.sub pos' 31sz;             (* SZ.v jpos == SZ.v pos' - 31 == q-1 *)
    lemma_srv_index code len;
    lemma_all_dec_prefix (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    lemma_all_dec_index (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    lemma_slice_snoc (W.enc_dec_var (U32.v len)) (SZ.v jpos);
    W.lemma_dec_dec_snoc (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v jpos))
                         (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos));
    lemma_divmod10 (W.dec_dec_var (Seq.slice (W.enc_dec_var (U32.v len)) 0 (SZ.v jpos)))
                   (W.undig (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos)));
    lemma_mod10_32 vrem;
    let r10 = U32.rem vrem 10ul;
    let bt = u32_digit r10;
    lemma_dig_undig_inv (Seq.index (W.enc_dec_var (U32.v len)) (SZ.v jpos));
    out.(pos') <- bt;
    rem := U32.div vrem 10ul;
    pos := pos';
  };

  (* Phase 3: tail [31+d, 35+d) — left-to-right copy of "\r\n\r\n". *)
  let base = SZ.add 31sz dcount;
  let mut b = 0sz;
  while (SZ.lt !b 4sz)
  invariant exists* (vb:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to b vb ** pts_to out sv **
    pure (
      SZ.v vb <= 4 /\
      SZ.v dcount == Seq.length (W.enc_dec_var (U32.v len)) /\
      Seq.length sv == Prims.op_Addition 35 (SZ.v dcount) /\
      Seq.length (srv_bytes code len) == Prims.op_Addition 35 (SZ.v dcount) /\
      (forall (k:nat). k < 31 ==> Seq.index sv k == Seq.index (srv_bytes code len) k) /\
      (forall (jj:nat). jj < SZ.v dcount ==>
         Seq.index sv (Prims.op_Addition 31 jj) == Seq.index (srv_bytes code len) (Prims.op_Addition 31 jj)) /\
      (forall (kk:nat). kk < SZ.v vb ==>
         Seq.index sv (Prims.op_Addition (Prims.op_Addition 31 (SZ.v dcount)) kk)
           == Seq.index (srv_bytes code len) (Prims.op_Addition (Prims.op_Addition 31 (SZ.v dcount)) kk)))
  decreases (Prims.op_Subtraction (SZ.v 4sz) (SZ.v (!b)))
  {
    let vb = !b;
    lemma_srv_index code len;
    lemma_cl_post_byte vb;
    let bt = cl_post_byte vb;
    out.(SZ.add base vb) <- bt;
    b := SZ.add vb 1sz;
  };

  with sf. assert (pts_to out sf);
  lemma_srv_index code len;                 (* length srv == 35 + length ee *)
  lemma_enc_dec_var_len (U32.v len);        (* length ee == dec_width len *)
  lemma_combine3 sf (srv_bytes code len) (SZ.v dcount);
  lemma_emit_response_var_final code len sf;
  ()
}
#pop-options

(* Parse a 43-byte response head `inp` back into a status code and Content-Length.
   Returns `ok`; when `ok`, `pcode`/`plen` hold values that `http_parse inp`
   decodes to exactly `Msg_response` of, with no residual.  Strategy: decode the
   11 digit positions to a candidate (code,len), then verify the WHOLE 43-byte
   buffer equals `head_byte code len` at every index in one compare loop.  A full
   match means `inp == respbytes code len == ser_response code (v len)`, so the
   spec's forward round-trip law (`lemma_http_parse_serialize_exact`) certifies
   the decode -- no separate parse-inversion proof is needed. *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
fn http_recv_response (inp: array U8.t) (pcode: R.ref U16.t) (plen: R.ref U32.t)
  requires
    pts_to inp 'i ** R.pts_to pcode 'c0 ** R.pts_to plen 'l0 **
    pure (Seq.length 'i == 43)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (cv:U16.t) (lv:U32.t).
       R.pts_to pcode cv ** R.pts_to plen lv **
       pure (ok == true ==>
         (Prims.op_LessThanOrEqual 100 (U16.v cv) /\
          Prims.op_LessThan (U16.v cv) 1000 /\
          Prims.op_LessThan (U32.v lv) W.max_len8 /\
          http_parse 'i == Some (Msg_response cv (U32.v lv), Seq.empty #U8.t))))
{
  (* decode the 11 digit positions to a candidate (code,len) *)
  let b9  = inp.(9sz);  let b10 = inp.(10sz); let b11 = inp.(11sz);
  let b31 = inp.(31sz); let b32 = inp.(32sz); let b33 = inp.(33sz); let b34 = inp.(34sz);
  let b35 = inp.(35sz); let b36 = inp.(36sz); let b37 = inp.(37sz); let b38 = inp.(38sz);
  let dok = W.is_dec b9 && W.is_dec b10 && W.is_dec b11 &&
            W.is_dec b31 && W.is_dec b32 && W.is_dec b33 && W.is_dec b34 &&
            W.is_dec b35 && W.is_dec b36 && W.is_dec b37 && W.is_dec b38;
  if dok {
    let c9  = Cast.uint8_to_uint16 (U8.sub b9  0x30uy);
    let c10 = Cast.uint8_to_uint16 (U8.sub b10 0x30uy);
    let c11 = Cast.uint8_to_uint16 (U8.sub b11 0x30uy);
    let code = U16.add (U16.add (U16.mul 100us c9) (U16.mul 10us c10)) c11;
    let e31 = Cast.uint8_to_uint32 (U8.sub b31 0x30uy);
    let e32 = Cast.uint8_to_uint32 (U8.sub b32 0x30uy);
    let e33 = Cast.uint8_to_uint32 (U8.sub b33 0x30uy);
    let e34 = Cast.uint8_to_uint32 (U8.sub b34 0x30uy);
    let e35 = Cast.uint8_to_uint32 (U8.sub b35 0x30uy);
    let e36 = Cast.uint8_to_uint32 (U8.sub b36 0x30uy);
    let e37 = Cast.uint8_to_uint32 (U8.sub b37 0x30uy);
    let e38 = Cast.uint8_to_uint32 (U8.sub b38 0x30uy);
    let hi4 = U32.add (U32.add (U32.add (U32.mul 1000ul e31) (U32.mul 100ul e32)) (U32.mul 10ul e33)) e34;
    let lo4 = U32.add (U32.add (U32.add (U32.mul 1000ul e35) (U32.mul 100ul e36)) (U32.mul 10ul e37)) e38;
    let len = U32.add (U32.mul 10000ul hi4) lo4;
    if (U16.lte 100us code && U16.lt code 1000us && U32.lt len 100000000ul) {
      (* verify the whole head equals head_byte code len at every position *)
      lemma_respbytes_len code len;
      let mut ok = true;
      let mut i = 0sz;
      while (SZ.lt !i 43sz)
      invariant exists* (vi:SZ.t) (okv:bool).
        R.pts_to i vi ** R.pts_to ok okv ** pts_to inp 'i **
        pure (SZ.v vi <= 43 /\ Seq.length 'i == 43 /\
          Seq.length (respbytes code len) == 43 /\
          (okv == true ==> (forall (k:nat). k < SZ.v vi ==>
             Seq.index 'i k == Seq.index (respbytes code len) k)))
      decreases (Prims.op_Subtraction (SZ.v 43sz) (SZ.v (!i)))
      {
        let vi = !i;
        let bv = inp.(vi);
        lemma_head_byte code len vi;
        let ev = head_byte code len vi;
        let eq = U8.eq bv ev;
        ok := (!ok) && eq;
        i := SZ.add vi 1sz;
      };
      let okv = !ok;
      if okv {
        lemma_respbytes_len code len;
        Seq.lemma_eq_intro ('i <: Seq.seq U8.t) (respbytes code len);
        lemma_respbytes_reveal code len;
        lemma_http_parse_serialize_exact (Msg_response code (U32.v len));
        pcode := code;
        plen  := len;
        true
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}
#pop-options

(* Parse a request head  "GET " target " HTTP/1.1\r\n\r\n"  in `inp` (logical
   length `n`).  Returns `ok`; when `ok`, `ptlen` holds the target length `tl`,
   the recovered space-free target is `Seq.slice inp 4 (4 + tl)`, and
   `http_parse inp == Some (Msg_request target, empty)`.  Mirrors the recv-head
   strategy: locate the FIRST space (which bounds the target and makes it
   space-free), verify the "GET " prefix and the 12-byte tail, then let the
   spec's forward round-trip law -- via lemma_recv_request_ok -- certify it. *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
fn http_recv_request (inp: array U8.t) (n: SZ.t) (ptlen: R.ref SZ.t)
  requires
    pts_to inp 'i ** R.pts_to ptlen 't0 **
    pure (Seq.length 'i == SZ.v n)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (tl:SZ.t).
       R.pts_to ptlen tl **
       pure (ok == true ==>
         (exists (tk:W.token).
            Seq.length 'i == SZ.v n /\
            Prims.op_LessThanOrEqual (Prims.op_Addition 4 (SZ.v tl)) (SZ.v n) /\
            (tk <: Seq.seq U8.t) == Seq.slice 'i 4 (Prims.op_Addition 4 (SZ.v tl)) /\
            http_parse 'i == Some (Msg_request tk, Seq.empty #U8.t))))
{
  if SZ.lt n 17sz {
    false
  } else {
    (* literal prefix "GET " *)
    let p0 = inp.(0sz); let p1 = inp.(1sz); let p2 = inp.(2sz); let p3 = inp.(3sz);
    let lit_ok = U8.eq p0 0x47uy && U8.eq p1 0x45uy && U8.eq p2 0x54uy && U8.eq p3 0x20uy;
    (* scan for the first space at or after index 4 *)
    let mut i = 4sz;
    let mut fnd = false;
    while (SZ.lt !i n && not !fnd)
    invariant exists* (vi:SZ.t) (vf:bool).
      R.pts_to i vi ** R.pts_to fnd vf ** pts_to inp 'i **
      pure (4 <= SZ.v vi /\ SZ.v vi <= SZ.v n /\ Seq.length 'i == SZ.v n /\
        (forall (j:nat). 4 <= j /\ j < SZ.v vi ==> Seq.index 'i j =!= W.bSP) /\
        (vf == true ==> (SZ.v vi < SZ.v n /\ Seq.index 'i (SZ.v vi) == W.bSP)))
    decreases %[(if !fnd then 0 else 1); Prims.op_Subtraction (SZ.v n) (SZ.v (!i))]
    {
      let vi = !i;
      let c = inp.(vi);
      if U8.eq c 0x20uy {
        fnd := true;
      } else {
        i := SZ.add vi 1sz;
      }
    };
    let sp = !i;
    let vfnd = !fnd;
    if (vfnd && lit_ok && SZ.eq (SZ.sub n sp) 13sz) {
      (* verify the 12-byte tail  "HTTP/1.1\r\n\r\n"  after the space *)
      let mut k = 0sz;
      let mut tok = true;
      while (SZ.lt !k 12sz)
      invariant exists* (vk:SZ.t) (vt:bool).
        R.pts_to k vk ** R.pts_to tok vt ** pts_to inp 'i **
        pure (SZ.v vk <= 12 /\ Seq.length 'i == SZ.v n /\
          4 <= SZ.v sp /\ Prims.op_Addition (SZ.v sp) 13 == SZ.v n /\
          Seq.index 'i (SZ.v sp) == W.bSP /\
          (vt == true ==> (forall (kk:nat). kk < SZ.v vk ==>
             Seq.index 'i (Prims.op_Addition (Prims.op_Addition (SZ.v sp) 1) kk)
               == Seq.index (Seq.cons W.bSP req_tail) (Prims.op_Addition kk 1))))
      decreases (Prims.op_Subtraction (SZ.v 12sz) (SZ.v (!k)))
      {
        let vk = !k;
        let bv = inp.(SZ.add (SZ.add sp 1sz) vk);
        lemma_req_tail_byte (SZ.add vk 1sz);
        let ev = req_tail_byte (SZ.add vk 1sz);
        let eq = U8.eq bv ev;
        tok := (!tok) && eq;
        k := SZ.add vk 1sz;
      };
      let vtok = !tok;
      if vtok {
        lemma_recv_request_ok ('i <: Seq.seq U8.t) (SZ.v sp);
        ptlen := SZ.sub sp 4sz;
        true
      } else {
        ptlen := 0sz;
        false
      }
    } else {
      ptlen := 0sz;
      false
    }
  }
}
#pop-options

(* Parse a REAL client's request head  "GET " target " HTTP/1.1\r\n" headers* "\r\n"
   in `inp` (logical length `n`), tolerating arbitrary header lines.  Returns
   `ok`; when `ok`, `ptlen` holds the target length `tl`, the recovered space-free
   target is `Seq.slice inp 4 (4 + tl)`, and `parse_request_line inp == Some tk`.
   Unlike `http_recv_request` it does NOT require an exact known length or a
   header-less request: it locates the FIRST space (bounding the space-free
   target), verifies the "GET " prefix and the 10-byte version token
   "HTTP/1.1\r\n" right after it, and ignores every following byte (the headers).
   `lemma_parse_request_line_ok` certifies the recovered target. *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
fn http_recv_request_head (inp: array U8.t) (n: SZ.t) (ptlen: R.ref SZ.t)
  requires
    pts_to inp 'i ** R.pts_to ptlen 't0 **
    pure (Seq.length 'i == SZ.v n)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (tl:SZ.t).
       R.pts_to ptlen tl **
       pure (ok == true ==>
         (exists (tk:W.token).
            Seq.length 'i == SZ.v n /\
            Prims.op_LessThanOrEqual (Prims.op_Addition 4 (SZ.v tl)) (SZ.v n) /\
            (tk <: Seq.seq U8.t) == Seq.slice 'i 4 (Prims.op_Addition 4 (SZ.v tl)) /\
            parse_request_line 'i == Some tk)))
{
  if SZ.lt n 15sz {
    false
  } else {
    (* literal prefix "GET " *)
    let p0 = inp.(0sz); let p1 = inp.(1sz); let p2 = inp.(2sz); let p3 = inp.(3sz);
    let lit_ok = U8.eq p0 0x47uy && U8.eq p1 0x45uy && U8.eq p2 0x54uy && U8.eq p3 0x20uy;
    (* scan for the first space at or after index 4 *)
    let mut i = 4sz;
    let mut fnd = false;
    while (SZ.lt !i n && not !fnd)
    invariant exists* (vi:SZ.t) (vf:bool).
      R.pts_to i vi ** R.pts_to fnd vf ** pts_to inp 'i **
      pure (4 <= SZ.v vi /\ SZ.v vi <= SZ.v n /\ Seq.length 'i == SZ.v n /\
        (forall (j:nat). 4 <= j /\ j < SZ.v vi ==> Seq.index 'i j =!= W.bSP) /\
        (vf == true ==> (SZ.v vi < SZ.v n /\ Seq.index 'i (SZ.v vi) == W.bSP)))
    decreases %[(if !fnd then 0 else 1); Prims.op_Subtraction (SZ.v n) (SZ.v (!i))]
    {
      let vi = !i;
      let c = inp.(vi);
      if U8.eq c 0x20uy {
        fnd := true;
      } else {
        i := SZ.add vi 1sz;
      }
    };
    let sp = !i;
    let vfnd = !fnd;
    (* require the 10-byte version token to fit after the space (sp + 11 <= n) *)
    if (vfnd && lit_ok && SZ.lte 11sz (SZ.sub n sp)) {
      (* verify the 10-byte version token  "HTTP/1.1\r\n"  right after the space *)
      let mut k = 0sz;
      let mut tok = true;
      while (SZ.lt !k 10sz)
      invariant exists* (vk:SZ.t) (vt:bool).
        R.pts_to k vk ** R.pts_to tok vt ** pts_to inp 'i **
        pure (SZ.v vk <= 10 /\ Seq.length 'i == SZ.v n /\
          4 <= SZ.v sp /\ Prims.op_Addition (SZ.v sp) 11 <= SZ.v n /\
          (vt == true ==> (forall (kk:nat). kk < SZ.v vk ==>
             Seq.index 'i (Prims.op_Addition (Prims.op_Addition (SZ.v sp) 1) kk)
               == Seq.index req_ver kk)))
      decreases (Prims.op_Subtraction (SZ.v 10sz) (SZ.v (!k)))
      {
        let vk = !k;
        let bv = inp.(SZ.add (SZ.add sp 1sz) vk);
        lemma_req_ver_byte vk;
        let ev = req_ver_byte vk;
        let eq = U8.eq bv ev;
        tok := (!tok) && eq;
        k := SZ.add vk 1sz;
      };
      let vtok = !tok;
      if vtok {
        lemma_parse_request_line_ok ('i <: Seq.seq U8.t) (SZ.v sp);
        ptlen := SZ.sub sp 4sz;
        true
      } else {
        ptlen := 0sz;
        false
      }
    } else {
      ptlen := 0sz;
      false
    }
  }
}
#pop-options
