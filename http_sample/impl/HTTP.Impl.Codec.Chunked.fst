module HTTP.Impl.Codec.Chunked

#lang-pulse

(**
  Verified Pulse implementation of the HTTP/1.1 *chunked* codec leaves, proved
  against the hand-written wire format `HTTP.Wire.Chunked` (the `http_message`
  union).

  Like the TFTP codec (and unlike YMODEM), this leaf does NOT `friend` any
  generated module: the HTTP wire format is written by hand over `FStar.Seq`, so
  `http_serialize` / `http_parse` are ordinary transparent definitions and the
  correspondence proofs are direct.  The only real proof machinery is the ASCII
  digit <-> value correspondence for the fixed-width decimal (status) and hex
  (chunk-size) fields.

  These are the executable leaves the driver loops (and the interop wrappers)
  link against; they take/return plain `array U8.t` buffers and extract to clean
  C.  A chunk carries a variable-length (0..65535) payload whose length is
  written as a 4-hex-digit size prefix, so `http_emit_chunk` / `http_recv_chunk`
  are parameterized by the payload length.
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
module ML = FStar.Math.Lemmas

module W = HTTP.Wire.Common
open HTTP.Wire.Chunked

(* ------------------------------------------------------------------------ *)
(* ASCII digit <-> value correspondence (executable).                        *)
(* ------------------------------------------------------------------------ *)

(* Executable single decimal digit: byte '0'..'9' for a value 0..9. *)
let dig_byte (d:U8.t{U8.v d < 10}) : U8.t = U8.add 0x30uy d

let lemma_dig_byte (d:U8.t{U8.v d < 10})
  : Lemma (dig_byte d == W.dig (U8.v d))
= ()

(* Executable single lowercase hex digit: byte '0'..'9'/'a'..'f' for 0..15. *)
let hexdig_byte (d:U8.t{U8.v d < 16}) : U8.t =
  if U8.lt d 10uy then U8.add 0x30uy d else U8.add 0x61uy (U8.sub d 10uy)

let lemma_hexdig_byte (d:U8.t{U8.v d < 16})
  : Lemma (hexdig_byte d == W.hexdig (U8.v d))
= ()

(* Executable inverse of `hexdig`: decode a hex-digit byte to its value 0..15,
   returned as a U16 refined to equal the spec `unhex`. *)
let unhex_byte (b:U8.t{W.is_hex b}) : (x:U16.t{U16.v x == W.unhex b}) =
  if U8.lte b 0x39uy
  then Cast.uint8_to_uint16 (U8.sub b 0x30uy)
  else Cast.uint8_to_uint16 (U8.add (U8.sub b 0x61uy) 10uy)

(* The four hex digits of a chunk size (executable), as U8 values 0..15. *)
let hx (n:SZ.t) (p:SZ.t{SZ.v p > 0}) : U8.t =
  Cast.uint32_to_uint8 (Cast.uint64_to_uint32 (SZ.sizet_to_uint64 (SZ.rem (SZ.div n p) 16sz)))

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let lemma_hx (n:SZ.t) (p:SZ.t)
  : Lemma (requires SZ.v n < 65536 /\ SZ.v p > 0)
          (ensures U8.v (hx n p) == (SZ.v n / SZ.v p) % 16 /\ U8.v (hx n p) < 16)
= let q = (SZ.v n / SZ.v p) % 16 in
  ML.lemma_mod_lt (SZ.v n / SZ.v p) 16;
  ML.small_mod q (pow2 32);
  ML.small_mod q (pow2 8)
#pop-options

let lemma_szlits ()
  : Lemma (SZ.v 4096sz == 4096 /\ SZ.v 256sz == 256 /\ SZ.v 16sz == 16 /\ SZ.v 1sz == 1 /\
           SZ.v 6sz == 6 /\ SZ.v 7sz == 7 /\ SZ.v 8sz == 8)
= assert_norm (SZ.v 4096sz == 4096);
  assert_norm (SZ.v 256sz == 256);
  assert_norm (SZ.v 16sz == 16);
  assert_norm (SZ.v 1sz == 1);
  assert_norm (SZ.v 6sz == 6);
  assert_norm (SZ.v 7sz == 7);
  assert_norm (SZ.v 8sz == 8)

(* size_t is at least 32 bits on every target we extract to (ISO C only mandates
   >= 16, and F*'s SizeT only auto-proves `fits` below 2^16).  A chunk buffer can
   be up to 8 + 65535 = 65543 bytes, which crosses the 16-bit line, so we localize
   the (universally true) "size_t has >= 32 bits" assumption to this one lemma. *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures SZ.fits x)
= assume (FStar.SizeT.fits_u32);
  FStar.SizeT.fits_u32_implies_fits x


#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let lemma_enc_hex4_index (n:nat{n < 65536}) (i:nat{i < 4})
  : Lemma (Seq.index (W.enc_hex4 n) i ==
           W.hexdig ((n / (match i with 0 -> 4096 | 1 -> 256 | 2 -> 16 | _ -> 1)) % 16))
= ()
#pop-options

(* ------------------------------------------------------------------------ *)
(* CRLF as two explicit bytes.                                               *)
(* ------------------------------------------------------------------------ *)

let lemma_crlf_index (i:nat{i < 2})
  : Lemma (Seq.index W.crlf i == (if i = 0 then W.bCR else W.bLF))
= ()

(* ------------------------------------------------------------------------ *)
(* Chunk-layout <-> serialization correspondence.                            *)
(* ------------------------------------------------------------------------ *)

(* A concrete 8+len byte buffer that carries the chunk layout
     hex4(len) | CRLF | payload | CRLF
   equals the serialization of the corresponding Msg_chunk. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let emit_chunk_serialize (p:chunk_payload) (s:Seq.seq U8.t)
  : Lemma
    (requires
       (let n = Seq.length (p <: Seq.seq U8.t) in
        n <= 65535 /\
        Seq.length s == 8 + n /\
        Seq.index s 0 == W.hexdig ((n / 4096) % 16) /\
        Seq.index s 1 == W.hexdig ((n / 256) % 16) /\
        Seq.index s 2 == W.hexdig ((n / 16) % 16) /\
        Seq.index s 3 == W.hexdig (n % 16) /\
        Seq.index s 4 == W.bCR /\
        Seq.index s 5 == W.bLF /\
        (forall (j:nat). j < n ==> Seq.index s (6 + j) == Seq.index (p <: Seq.seq U8.t) j) /\
        Seq.index s (6 + n) == W.bCR /\
        Seq.index s (7 + n) == W.bLF))
    (ensures s == ser_chunk p)
=
  let n = Seq.length (p <: Seq.seq U8.t) in
  let szb = W.enc_hex4 n in
  let pb  = (p <: Seq.seq U8.t) in
  (* the four regions of s equal the four serialization components *)
  Seq.lemma_eq_intro (Seq.slice s 0 4) szb;
  Seq.lemma_eq_intro (Seq.slice s 4 6) W.crlf;
  Seq.lemma_eq_intro (Seq.slice s 6 (6 + n)) pb;
  Seq.lemma_eq_intro (Seq.slice s (6 + n) (8 + n)) W.crlf;
  (* rebuild s from its four regions and match ser_chunk's append structure *)
  Seq.lemma_eq_intro s (ser_chunk p)
#pop-options

let emit_chunk_exists (d s:Seq.seq U8.t)
  : Lemma
    (requires
       Seq.length d <= 65535 /\
       Seq.length s == 8 + Seq.length d /\
       Seq.index s 0 == W.hexdig ((Seq.length d / 4096) % 16) /\
       Seq.index s 1 == W.hexdig ((Seq.length d / 256) % 16) /\
       Seq.index s 2 == W.hexdig ((Seq.length d / 16) % 16) /\
       Seq.index s 3 == W.hexdig (Seq.length d % 16) /\
       Seq.index s 4 == W.bCR /\
       Seq.index s 5 == W.bLF /\
       (forall (j:nat). j < Seq.length d ==> Seq.index s (6 + j) == Seq.index d j) /\
       Seq.index s (6 + Seq.length d) == W.bCR /\
       Seq.index s (7 + Seq.length d) == W.bLF)
    (ensures
       (exists (pl:chunk_payload).
          (pl <: Seq.seq U8.t) == d /\ s == ser_chunk pl))
=
  let pl : chunk_payload = d in
  emit_chunk_serialize pl s;
  introduce exists (pl':chunk_payload).
     (pl' <: Seq.seq U8.t) == d /\ s == ser_chunk pl'
  with pl and ()

(* ------------------------------------------------------------------------ *)
(* The verified emit leaf.                                                   *)
(* ------------------------------------------------------------------------ *)

open Pulse.Lib.BoundedIntegers

(* Build an HTTP chunk  hex4(len) | CRLF | payload(len) | CRLF  from a `len`-byte
   body chunk; `out` (length 8+len) receives the whole chunk, proved equal to
   `ser_chunk payload`. *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
fn http_emit_chunk
  (data: array U8.t)
  (data_len: SZ.t)
  (out: array U8.t)
  requires
    pts_to data 'd **
    pts_to out 'o **
    pure (Seq.length 'd == SZ.v data_len /\ SZ.v data_len <= 65535 /\
          Seq.length 'o == 8 + SZ.v data_len)
  ensures
    pts_to data 'd **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 8 + SZ.v data_len /\
             (exists (pl:chunk_payload).
                (pl <: Seq.seq U8.t) == 'd /\
                o' == ser_chunk pl)))
{
  lemma_szlits ();
  lemma_hx data_len 4096sz;
  lemma_hx data_len 256sz;
  lemma_hx data_len 16sz;
  lemma_hx data_len 1sz;
  lemma_hexdig_byte (hx data_len 4096sz);
  lemma_hexdig_byte (hx data_len 256sz);
  lemma_hexdig_byte (hx data_len 16sz);
  lemma_hexdig_byte (hx data_len 1sz);
  out.(0sz) <- hexdig_byte (hx data_len 4096sz);
  out.(1sz) <- hexdig_byte (hx data_len 256sz);
  out.(2sz) <- hexdig_byte (hx data_len 16sz);
  out.(3sz) <- hexdig_byte (hx data_len 1sz);
  out.(4sz) <- W.bCR;
  out.(5sz) <- W.bLF;
  let mut i = 0sz;
  while (!i < data_len)
  invariant exists* (vi:SZ.t) (sv:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to data 'd **
    pts_to out sv **
    pure (
      SZ.v vi <= SZ.v data_len /\
      SZ.v data_len <= 65535 /\
      Seq.length 'd == SZ.v data_len /\
      Seq.length sv == 8 + SZ.v data_len /\
      Seq.index sv 0 == W.hexdig ((SZ.v data_len / 4096) % 16) /\
      Seq.index sv 1 == W.hexdig ((SZ.v data_len / 256) % 16) /\
      Seq.index sv 2 == W.hexdig ((SZ.v data_len / 16) % 16) /\
      Seq.index sv 3 == W.hexdig (SZ.v data_len % 16) /\
      Seq.index sv 4 == W.bCR /\
      Seq.index sv 5 == W.bLF /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index sv (6 + j) == Seq.index 'd j))
  {
    lemma_szlits ();
    let vi = !i;
    lemma_fits32 (6 + SZ.v vi);
    let dv = data.(vi);
    out.(6sz + vi) <- dv;
    i := vi + 1sz;
  };
  lemma_fits32 (6 + SZ.v data_len);
  lemma_fits32 (7 + SZ.v data_len);
  out.(6sz + data_len) <- W.bCR;
  out.(7sz + data_len) <- W.bLF;
  with sf. assert (pts_to out sf);
  emit_chunk_exists 'd sf;
  ()
}
#pop-options

(* The RFC last-chunk  "0000" CRLF CRLF  (an empty chunk).  Its bytes coincide
   with `ser_chunk` of the empty payload, so it terminates a chunked body. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
fn http_emit_empty_chunk
  (out: array U8.t)
  requires
    pts_to out 'o **
    pure (Seq.length 'o == 8)
  ensures
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == 8 /\
             (exists (pl:chunk_payload).
                (pl <: Seq.seq U8.t) == Seq.empty #U8.t /\
                o' == ser_chunk pl)))
{
  out.(0sz) <- 0x30uy;
  out.(1sz) <- 0x30uy;
  out.(2sz) <- 0x30uy;
  out.(3sz) <- 0x30uy;
  out.(4sz) <- W.bCR;
  out.(5sz) <- W.bLF;
  out.(6sz) <- W.bCR;
  out.(7sz) <- W.bLF;
  with sf. assert (pts_to out sf);
  assert_norm (W.hexdig 0 == 0x30uy);
  emit_chunk_exists (Seq.empty #U8.t) sf;
  ()
}
#pop-options


(* ------------------------------------------------------------------------ *)
(* The verified receive leaves.                                              *)
(* ------------------------------------------------------------------------ *)

(* Decode a 6-byte chunk header  hex4 | CRLF  read off the stream: returns
   (ok, n) where `ok` certifies the header is well-formed and `n` is the decoded
   payload length (so the caller knows how many more bytes -- n payload + 2 CRLF
   -- to read). *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_peek_chunk_size (hdr: array U8.t)
  requires
    pts_to hdr 'h **
    pure (Seq.length 'h == 6)
  returns r: (bool & U16.t)
  ensures
    pts_to hdr 'h **
    pure (fst r == true ==>
            (Seq.length 'h == 6 /\
             W.hex4_ok (Seq.slice 'h 0 4) /\
             Seq.equal (Seq.slice 'h 4 6) W.crlf /\
             W.dec_hex4 (Seq.slice 'h 0 4) == U16.v (snd r)))
{
  let c0 = hdr.(0sz);
  let c1 = hdr.(1sz);
  let c2 = hdr.(2sz);
  let c3 = hdr.(3sz);
  let c4 = hdr.(4sz);
  let c5 = hdr.(5sz);
  let okhex = W.is_hex c0 && W.is_hex c1 && W.is_hex c2 && W.is_hex c3;
  let okcrlf = U8.eq c4 W.bCR && U8.eq c5 W.bLF;
  if (okhex && okcrlf) {
    Seq.lemma_index_slice 'h 0 4 0;
    Seq.lemma_index_slice 'h 0 4 1;
    Seq.lemma_index_slice 'h 0 4 2;
    Seq.lemma_index_slice 'h 0 4 3;
    let n = U16.add (U16.add (U16.add
              (U16.mul (unhex_byte c0) 4096us)
              (U16.mul (unhex_byte c1) 256us))
              (U16.mul (unhex_byte c2) 16us))
              (unhex_byte c3);
    Seq.lemma_eq_intro (Seq.slice 'h 4 6) W.crlf;
    (true, n)
  } else {
    (false, 0us)
  }
}
#pop-options

(* Given a well-formed header `hdr` (already validated to decode to `n` by
   http_peek_chunk_size) and a `body` buffer holding the n payload bytes plus the
   trailing CRLF, copy the payload into `out` and validate the trailing CRLF.
   When the CRLF checks out, the whole frame `hdr ++ body` parses (per the spec
   `http_parse`) to exactly the chunk carrying the copied payload. *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
fn http_recv_chunk (hdr: array U8.t) (body: array U8.t) (out: array U8.t) (n: SZ.t)
  requires
    pts_to hdr 'h ** pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 'h == 6 /\ Seq.length 'b == SZ.v n + 2 /\ Seq.length 'o == SZ.v n /\
          SZ.v n <= 65535 /\
          W.hex4_ok (Seq.slice 'h 0 4) /\ Seq.equal (Seq.slice 'h 4 6) W.crlf /\
          W.dec_hex4 (Seq.slice 'h 0 4) == SZ.v n)
  returns crlf_ok: bool
  ensures
    pts_to hdr 'h ** pts_to body 'b **
    (exists* (o':Seq.seq U8.t).
       pts_to out o' **
       pure (Seq.length o' == SZ.v n /\
             (crlf_ok == true ==>
                (SZ.v n <= 65535 /\
                 http_parse (Seq.append 'h 'b) ==
                   Some (Msg_chunk o', Seq.empty #U8.t)))))
{
  let mut i = 0sz;
  while (SZ.lt !i n)
  invariant exists* (vi:SZ.t) (ov:Seq.seq U8.t).
    R.pts_to i vi **
    pts_to hdr 'h ** pts_to body 'b ** pts_to out ov **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length 'b == SZ.v n + 2 /\
      Seq.length ov == SZ.v n /\
      (forall (j:nat). j < SZ.v vi ==> Seq.index ov j == Seq.index 'b j))
  {
    let vi = !i;
    let dv = body.(vi);
    out.(vi) <- dv;
    i := SZ.add vi 1sz;
  };
  lemma_fits32 (SZ.v n + 1);
  let e0 = body.(n);
  let e1 = body.(SZ.add n 1sz);
  let crlf_ok = U8.eq e0 W.bCR && U8.eq e1 W.bLF;
  with ov. assert (pts_to out ov);
  Seq.lemma_eq_intro ov (Seq.slice 'b 0 (SZ.v n));
  if crlf_ok {
    Seq.lemma_eq_intro (Seq.slice 'b (SZ.v n) (SZ.v n + 2)) W.crlf;
    lemma_parse_chunk_parts 'h 'b (SZ.v n);
    crlf_ok
  } else {
    crlf_ok
  }
}
#pop-options
