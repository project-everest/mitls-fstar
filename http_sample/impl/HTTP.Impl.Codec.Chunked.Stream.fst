module HTTP.Impl.Codec.Chunked.Stream

#lang-pulse

(**
  Verified in-buffer *streaming reassembly* decoder for the HTTP/1.1 chunked
  transfer-encoding, proved against `HTTP.Wire.Chunked.Stream.parse_chunks`.

  `http_decode_chunks` walks ONE input buffer holding a sequence of chunk frames
  (each `hhhh CRLF payload CRLF`, ending with the size-0 last chunk), decoding
  INLINE — with a cursor `pos` over the input and an offset `off` into the output
  buffer — and concatenating the payloads into `out`.  The loop maintains the
  invariant

    parse_chunks (slice inp 0 inlen) ==
      recon (slice out 0 off) (parse_chunks (slice inp pos inlen))

  (decoded-so-far `recon`ned onto the reassembly of the rest), so on success the
  first `off` bytes of `out` are exactly the reassembled body per the spec.
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
module CC = HTTP.Impl.Codec.Chunked
module S = HTTP.Wire.Chunked.Stream
open HTTP.Wire.Chunked

(* size_t is at least 64 bits on every target we extract to; index sums here stay
   below pow2 32 + 2^17, comfortably inside size_t.  Localize the (universally
   true) "size_t has >= 64 bits" assumption to this one lemma. *)
let lemma_fits_small (x:nat)
  : Lemma (requires x < pow2 32 + 131072) (ensures SZ.fits x)
= assume (FStar.SizeT.fits_u64);
  assert_norm (pow2 32 + 131072 < pow2 64);
  FStar.SizeT.fits_u64_implies_fits x

(* recon of an empty decoded prefix is the identity. *)
let lemma_recon_empty (r:option (Seq.seq U8.t & Seq.seq U8.t))
  : Lemma (S.recon (Seq.empty #U8.t) r == r)
= match r with
  | Some (body, rest) -> Seq.append_empty_l body
  | None -> ()

(* ------------------------------------------------------------------------ *)
(* Pure plumbing lemmas relating slices of the single input buffer to the    *)
(* h / b / suffix shape the parse_chunks step/end lemmas expect.             *)
(* ------------------------------------------------------------------------ *)

(* slice i pos len splits into the header, body and suffix of one frame. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let lemma_slice3 (i:Seq.seq U8.t) (a m1 m2 e:nat)
  : Lemma (requires a <= m1 /\ m1 <= m2 /\ m2 <= e /\ e <= Seq.length i)
          (ensures Seq.slice i a e ==
             Seq.append (Seq.append (Seq.slice i a m1) (Seq.slice i m1 m2))
                        (Seq.slice i m2 e))
= Seq.lemma_eq_intro (Seq.slice i a e)
    (Seq.append (Seq.append (Seq.slice i a m1) (Seq.slice i m1 m2))
                (Seq.slice i m2 e))
#pop-options

(* Header well-formedness at offset `pos`, derived from the six header bytes. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_hdr_wf (i:Seq.seq U8.t) (pos:nat) (c0 c1 c2 c3:U8.t) (n:nat)
  : Lemma
    (requires
      pos + 6 <= Seq.length i /\
      Seq.index i pos == c0 /\ Seq.index i (pos + 1) == c1 /\
      Seq.index i (pos + 2) == c2 /\ Seq.index i (pos + 3) == c3 /\
      Seq.index i (pos + 4) == W.bCR /\ Seq.index i (pos + 5) == W.bLF /\
      W.is_hex c0 /\ W.is_hex c1 /\ W.is_hex c2 /\ W.is_hex c3 /\
      n == W.unhex c0 * 4096 + W.unhex c1 * 256 + W.unhex c2 * 16 + W.unhex c3)
    (ensures
      (let h = Seq.slice i pos (pos + 6) in
       Seq.length h == 6 /\ W.hex4_ok (Seq.slice h 0 4) /\
       Seq.equal (Seq.slice h 4 6) W.crlf /\ W.dec_hex4 (Seq.slice h 0 4) == n))
= let h = Seq.slice i pos (pos + 6) in
  (* index h k == index i (pos+k) *)
  Seq.lemma_index_slice i pos (pos + 6) 0;
  Seq.lemma_index_slice i pos (pos + 6) 1;
  Seq.lemma_index_slice i pos (pos + 6) 2;
  Seq.lemma_index_slice i pos (pos + 6) 3;
  Seq.lemma_index_slice i pos (pos + 6) 4;
  Seq.lemma_index_slice i pos (pos + 6) 5;
  (* index (slice h 0 4) k == index h k *)
  Seq.lemma_index_slice h 0 4 0;
  Seq.lemma_index_slice h 0 4 1;
  Seq.lemma_index_slice h 0 4 2;
  Seq.lemma_index_slice h 0 4 3;
  Seq.lemma_eq_intro (Seq.slice h 4 6) W.crlf
#pop-options

(* Trailing-CRLF of the body at offset `pos+6`, derived from two bytes. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let lemma_body_crlf (i:Seq.seq U8.t) (pos n:nat)
  : Lemma
    (requires
      pos + 8 + n <= Seq.length i /\
      Seq.index i (pos + 6 + n) == W.bCR /\ Seq.index i (pos + 7 + n) == W.bLF)
    (ensures
      (let b = Seq.slice i (pos + 6) (pos + 8 + n) in
       Seq.length b == n + 2 /\ Seq.equal (Seq.slice b n (n + 2)) W.crlf))
= let b = Seq.slice i (pos + 6) (pos + 8 + n) in
  Seq.lemma_index_slice i (pos + 6) (pos + 8 + n) n;
  Seq.lemma_index_slice i (pos + 6) (pos + 8 + n) (n + 1);
  Seq.lemma_eq_intro (Seq.slice b n (n + 2)) W.crlf
#pop-options

(* slice out 0 (off+n), after copying the n payload bytes past off, equals the
   old prefix concatenated with the payload. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let lemma_prefix_extend (oldv newv:Seq.seq U8.t) (off n:nat)
  : Lemma
    (requires
      off + n <= Seq.length oldv /\ Seq.length oldv == Seq.length newv /\
      (forall (j:nat). j < off ==> Seq.index newv j == Seq.index oldv j))
    (ensures
      Seq.slice newv 0 (off + n) ==
        Seq.append (Seq.slice oldv 0 off) (Seq.slice newv off (off + n)))
= Seq.lemma_eq_intro (Seq.slice newv 0 (off + n))
    (Seq.append (Seq.slice oldv 0 off) (Seq.slice newv off (off + n)))
#pop-options

(* ------------------------------------------------------------------------ *)
(* The verified decoder.                                                      *)
(* ------------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300 --split_queries always"
fn http_decode_chunks
    (inp: array U8.t) (inlen: SZ.t)
    (out: array U8.t) (outcap: SZ.t)
    (poff: R.ref SZ.t)
  requires
    pts_to inp 'i ** pts_to out 'o ** R.pts_to poff 'po **
    pure (SZ.v inlen <= Seq.length 'i /\ Seq.length 'o == SZ.v outcap /\
          SZ.v inlen < pow2 32 /\ SZ.v outcap < pow2 32)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (ov:Seq.seq U8.t) (vo:SZ.t).
       pts_to out ov ** R.pts_to poff vo **
       pure (Seq.length ov == SZ.v outcap /\ SZ.v inlen <= Seq.length 'i /\
             (ok == true ==>
                (SZ.v vo <= SZ.v outcap /\
                 (exists (rest:Seq.seq U8.t).
                    S.parse_chunks (Seq.slice 'i 0 (SZ.v inlen)) ==
                      Some (Seq.slice ov 0 (SZ.v vo), rest))))))
{
  let mut pos = 0sz;
  let mut off = 0sz;
  let mut err = false;
  let mut done = false;
  Seq.lemma_eq_intro (Seq.slice 'o 0 0) (Seq.empty #U8.t);
  lemma_recon_empty (S.parse_chunks (Seq.slice 'i 0 (SZ.v inlen)));
  while (not !done && not !err)
  invariant exists* (vpos:SZ.t) (voff:SZ.t) (verr:bool) (vdone:bool) (ov:Seq.seq U8.t).
    R.pts_to pos vpos ** R.pts_to off voff ** R.pts_to err verr ** R.pts_to done vdone **
    pts_to inp 'i ** pts_to out ov **
    pure (
      Seq.length ov == SZ.v outcap /\ SZ.v inlen <= Seq.length 'i /\
      SZ.v vpos <= SZ.v inlen /\ SZ.v voff <= SZ.v outcap /\
      (vdone == true ==> verr == false) /\
      (verr == false ==>
        ((vdone == false ==>
            S.parse_chunks (Seq.slice 'i 0 (SZ.v inlen)) ==
              S.recon (Seq.slice ov 0 (SZ.v voff))
                      (S.parse_chunks (Seq.slice 'i (SZ.v vpos) (SZ.v inlen)))) /\
         (vdone == true ==>
            (exists (rest:Seq.seq U8.t).
               S.parse_chunks (Seq.slice 'i 0 (SZ.v inlen)) ==
                 Some (Seq.slice ov 0 (SZ.v voff), rest))))))
  {
    let vpos = !pos;
    (* need at least a 6-byte header + 2-byte CRLF = 8 bytes for any frame *)
    lemma_fits_small (SZ.v vpos + 8);
    if (SZ.gt (SZ.add vpos 8sz) inlen) {
      err := true;
    } else {
      lemma_fits_small (SZ.v vpos + 1);
      lemma_fits_small (SZ.v vpos + 2);
      lemma_fits_small (SZ.v vpos + 3);
      lemma_fits_small (SZ.v vpos + 4);
      lemma_fits_small (SZ.v vpos + 5);
      let c0 = inp.(vpos);
      let c1 = inp.(SZ.add vpos 1sz);
      let c2 = inp.(SZ.add vpos 2sz);
      let c3 = inp.(SZ.add vpos 3sz);
      let c4 = inp.(SZ.add vpos 4sz);
      let c5 = inp.(SZ.add vpos 5sz);
      let okhex = W.is_hex c0 && W.is_hex c1 && W.is_hex c2 && W.is_hex c3;
      let okcrlf = U8.eq c4 W.bCR && U8.eq c5 W.bLF;
      if (not (okhex && okcrlf)) {
        err := true;
      } else {
        let n16 = U16.add (U16.add (U16.add
                    (U16.mul (CC.unhex_byte c0) 4096us)
                    (U16.mul (CC.unhex_byte c1) 256us))
                    (U16.mul (CC.unhex_byte c2) 16us))
                    (CC.unhex_byte c3);
        let n = SZ.uint16_to_sizet n16;
        (* header well-formedness at offset vpos *)
        lemma_hdr_wf 'i (SZ.v vpos) c0 c1 c2 c3 (SZ.v n);
        lemma_fits_small (SZ.v vpos + 8 + SZ.v n);
        if (SZ.gt (SZ.add (SZ.add vpos 8sz) n) inlen) {
          err := true;
        } else {
          (* read the trailing CRLF of this frame's body *)
          lemma_fits_small (SZ.v vpos + 6 + SZ.v n);
          lemma_fits_small (SZ.v vpos + 7 + SZ.v n);
          let e0 = inp.(SZ.add (SZ.add vpos 6sz) n);
          let e1 = inp.(SZ.add (SZ.add vpos 7sz) n);
          let bodycrlf = U8.eq e0 W.bCR && U8.eq e1 W.bLF;
          if (not bodycrlf) {
            err := true;
          } else {
            lemma_body_crlf 'i (SZ.v vpos) (SZ.v n);
            if (SZ.eq n 0sz) {
              (* last chunk: terminate. *)
              let voff0 = !off;
              lemma_slice3 'i (SZ.v vpos) (SZ.v vpos + 6) (SZ.v vpos + 8) (SZ.v inlen);
              S.lemma_parse_chunks_end
                (Seq.slice 'i (SZ.v vpos) (SZ.v vpos + 6))
                (Seq.slice 'i (SZ.v vpos + 6) (SZ.v vpos + 8))
                (Seq.slice 'i (SZ.v vpos + 8) (SZ.v inlen));
              with ov. assert (pts_to out ov);
              Seq.append_empty_r (Seq.slice ov 0 (SZ.v voff0));
              done := true;
            } else {
              (* non-empty chunk: copy n payload bytes into out at offset off. *)
              let voff = !off;
              lemma_fits_small (SZ.v voff + SZ.v n);
              if (SZ.gt (SZ.add voff n) outcap) {
                err := true;
              } else {
                with ovold. assert (pts_to out ovold);
                let mut k = 0sz;
                while (SZ.lt !k n)
                invariant exists* (vk:SZ.t) (ov:Seq.seq U8.t).
                  R.pts_to k vk ** pts_to out ov ** pts_to inp 'i **
                  pure (
                    SZ.v vk <= SZ.v n /\
                    Seq.length ov == SZ.v outcap /\
                    SZ.v vpos + 8 + SZ.v n <= SZ.v inlen /\
                    SZ.v inlen <= Seq.length 'i /\
                    SZ.v voff + SZ.v n <= SZ.v outcap /\
                    (forall (j:nat). j < SZ.v voff ==> Seq.index ov j == Seq.index ovold j) /\
                    (forall (j:nat). j < SZ.v vk ==>
                       Seq.index ov (SZ.v voff + j) ==
                         Seq.index 'i (SZ.v vpos + 6 + j)))
                {
                  let vk = !k;
                  lemma_fits_small (SZ.v vpos + 6 + SZ.v vk);
                  lemma_fits_small (SZ.v voff + SZ.v vk);
                  let dv = inp.(SZ.add (SZ.add vpos 6sz) vk);
                  out.(SZ.add voff vk) <- dv;
                  lemma_fits_small (SZ.v vk + 1);
                  k := SZ.add vk 1sz;
                };
                with ovnew. assert (pts_to out ovnew);
                (* payload copied: slice ovnew off (off+n) == slice i (pos+6) (pos+6+n) *)
                Seq.lemma_eq_intro
                  (Seq.slice ovnew (SZ.v voff) (SZ.v voff + SZ.v n))
                  (Seq.slice 'i (SZ.v vpos + 6) (SZ.v vpos + 6 + SZ.v n));
                (* slice b 0 n == slice i (pos+6) (pos+6+n) *)
                Seq.slice_slice 'i (SZ.v vpos + 6) (SZ.v vpos + 8 + SZ.v n) 0 (SZ.v n);
                (* frame algebra: whole slice at pos == append(append h b) suffix *)
                lemma_slice3 'i (SZ.v vpos) (SZ.v vpos + 6) (SZ.v vpos + 8 + SZ.v n) (SZ.v inlen);
                S.lemma_parse_chunks_step
                  (Seq.slice 'i (SZ.v vpos) (SZ.v vpos + 6))
                  (Seq.slice 'i (SZ.v vpos + 6) (SZ.v vpos + 8 + SZ.v n))
                  (Seq.slice 'i (SZ.v vpos + 8 + SZ.v n) (SZ.v inlen))
                  (SZ.v n);
                (* new prefix == old prefix ++ payload *)
                lemma_prefix_extend ovold ovnew (SZ.v voff) (SZ.v n);
                S.lemma_recon_compose
                  (Seq.slice ovold 0 (SZ.v voff))
                  (Seq.slice ovnew (SZ.v voff) (SZ.v voff + SZ.v n))
                  (S.parse_chunks (Seq.slice 'i (SZ.v vpos + 8 + SZ.v n) (SZ.v inlen)));
                (* slice ovold 0 off is preserved in ovnew *)
                Seq.lemma_eq_intro (Seq.slice ovnew 0 (SZ.v voff)) (Seq.slice ovold 0 (SZ.v voff));
                lemma_fits_small (SZ.v vpos + 8 + SZ.v n);
                pos := SZ.add (SZ.add vpos 8sz) n;
                off := SZ.add voff n;
              }
            }
          }
        }
      }
    }
  };
  let vdone = !done;
  let voff = !off;
  poff := voff;
  if vdone {
    true
  } else {
    false
  }
}
#pop-options

(* ------------------------------------------------------------------------ *)
(* Variable-width (RFC 9112) chunk-size decoder.                              *)
(*                                                                            *)
(* Unlike http_decode_chunks above — which assumes the fixed 4-hex-digit size *)
(* header emitted by our own encoder — real origin servers write a           *)
(* minimal-width hex chunk size (e.g. "1cf\r\n").  This decoder parses a      *)
(* size of ANY number of hex digits followed by CRLF, then `size` payload     *)
(* bytes and a trailing CRLF, repeating until the size-0 last chunk.  It      *)
(* deliberately carries only a MEMORY-SAFETY contract (every array access is  *)
(* proved in-bounds and the output length stays <= outcap) — not the full     *)
(* parse_chunks spec relation, which is defined only for the fixed-width      *)
(* header — matching the client-leaf philosophy of parsing untrusted server   *)
(* output safely.  (Chunk extensions after the size and a trailing-header     *)
(* section after the last chunk are not interpreted; a size line with a ';'   *)
(* extension or a non-CRLF terminator is rejected as malformed.)             *)

(* size_t is >= 64 bits; the size accumulator stays <= inlen < pow2 32, so the
   intermediate s*16 (+ a hex digit) stays below pow2 40, comfortably inside. *)
let lemma_fits_wide (x:nat)
  : Lemma (requires x < pow2 40) (ensures SZ.fits x)
= assume (FStar.SizeT.fits_u64);
  assert_norm (pow2 40 < pow2 64);
  FStar.SizeT.fits_u64_implies_fits x

(* s <= inl < pow2 32  ==>  s*16 and s*16+16 stay below pow2 40. *)
let lemma_size_mul (s inl:nat)
  : Lemma (requires s <= inl /\ inl < pow2 32)
          (ensures s * 16 + 16 < pow2 40)
= ML.lemma_mult_le_right 16 s inl;
  ML.lemma_mult_lt_right 16 inl (pow2 32);
  assert_norm (pow2 32 * 16 == pow2 36);
  assert_norm (pow2 36 + 16 < pow2 40)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
fn http_decode_chunks_var
    (inp: array U8.t) (inlen: SZ.t)
    (out: array U8.t) (outcap: SZ.t)
    (poff: R.ref SZ.t)
  requires
    pts_to inp 'i ** pts_to out 'o ** R.pts_to poff 'po **
    pure (SZ.v inlen <= Seq.length 'i /\ Seq.length 'o == SZ.v outcap /\
          SZ.v inlen < pow2 32 /\ SZ.v outcap < pow2 32)
  returns ok: bool
  ensures
    pts_to inp 'i **
    (exists* (ov:Seq.seq U8.t) (vo:SZ.t).
       pts_to out ov ** R.pts_to poff vo **
       pure (Seq.length ov == SZ.v outcap /\
             (ok == true ==> SZ.v vo <= SZ.v outcap)))
{
  let mut pos = 0sz;
  let mut off = 0sz;
  let mut err = false;
  let mut done = false;
  while (not !done && not !err)
  invariant exists* (vpos voff:SZ.t) (verr vdone:bool) (ov:Seq.seq U8.t).
    R.pts_to pos vpos ** R.pts_to off voff ** R.pts_to err verr ** R.pts_to done vdone **
    pts_to inp 'i ** pts_to out ov **
    pure (Seq.length ov == SZ.v outcap /\
          SZ.v vpos <= SZ.v inlen /\ SZ.v voff <= SZ.v outcap /\
          SZ.v inlen < pow2 32 /\ SZ.v outcap < pow2 32)
  {
    let vpos = !pos;
    (* ── parse the variable-width hex size line starting at vpos ─────────── *)
    let mut np = vpos;
    let mut size = 0sz;
    let mut hexcount = 0sz;
    let mut scanning = true;
    while (!scanning)
    invariant exists* (vnp vsize vhc:SZ.t) (vsc:bool).
      R.pts_to np vnp ** R.pts_to size vsize ** R.pts_to hexcount vhc **
      R.pts_to scanning vsc ** pts_to inp 'i **
      pure (SZ.v vnp <= SZ.v inlen /\ SZ.v vsize <= SZ.v inlen /\
            SZ.v vhc <= SZ.v vnp /\ SZ.v inlen < pow2 32)
    {
      let vnp = !np;
      if SZ.lt vnp inlen {
        let c = inp.(vnp);
        if W.is_hex c {
          let d = SZ.uint16_to_sizet (CC.unhex_byte c);
          let s = !size;
          lemma_size_mul (SZ.v s) (SZ.v inlen);
          lemma_fits_wide (SZ.v s * 16);
          let s16 = SZ.mul s 16sz;
          lemma_fits_wide (SZ.v s16 + SZ.v d);
          let s' = SZ.add s16 d;
          if SZ.gt s' inlen {
            (* a chunk larger than the whole input is malformed; stop *)
            scanning := false;
          } else {
            let vhc = !hexcount;
            lemma_fits_small (SZ.v vhc + 1);
            size := s';
            hexcount := SZ.add vhc 1sz;
            np := SZ.add vnp 1sz;
          }
        } else {
          scanning := false;
        }
      } else {
        scanning := false;
      }
    };
    (* ── validate the size line and consume the frame ───────────────────── *)
    let vnp = !np;
    let vhc = !hexcount;
    if SZ.eq vhc 0sz {
      err := true;                       (* no hex digits: malformed *)
    } else {
      lemma_fits_small (SZ.v vnp + 1);
      if SZ.gte (SZ.add vnp 1sz) inlen {
        err := true;                     (* no room for the size-line CRLF *)
      } else {
        let h0 = inp.(vnp);
        let h1 = inp.(SZ.add vnp 1sz);
        if not (U8.eq h0 W.bCR && U8.eq h1 W.bLF) {
          err := true;                   (* size not terminated by CRLF *)
        } else {
          let vsize = !size;
          let datastart = SZ.add vnp 2sz;
          if SZ.eq vsize 0sz {
            done := true;                (* last chunk: terminate *)
          } else {
            assert_norm (pow2 32 + pow2 32 + 4 < pow2 40);
            lemma_fits_wide (SZ.v datastart + SZ.v vsize + 2);
            let vposn = !pos;
            let voff = !off;
            if SZ.gt (SZ.add (SZ.add datastart vsize) 2sz) inlen {
              err := true;               (* frame body overruns input *)
            } else {
              assert_norm (pow2 32 + pow2 32 < pow2 40);
              lemma_fits_wide (SZ.v voff + SZ.v vsize);
              if SZ.gt (SZ.add voff vsize) outcap {
                err := true;             (* reassembly overruns output *)
              } else {
                (* copy vsize payload bytes inp[datastart..) -> out[voff..) *)
                let mut k = 0sz;
                while (SZ.lt !k vsize)
                invariant exists* (vk:SZ.t) (ov:Seq.seq U8.t).
                  R.pts_to k vk ** pts_to out ov ** pts_to inp 'i **
                  pure (SZ.v vk <= SZ.v vsize /\ Seq.length ov == SZ.v outcap /\
                        SZ.v voff + SZ.v vsize <= SZ.v outcap /\
                        SZ.v datastart + SZ.v vsize + 2 <= SZ.v inlen /\
                        SZ.v inlen <= Seq.length 'i)
                {
                  let vk = !k;
                  lemma_fits_small (SZ.v datastart + SZ.v vk);
                  lemma_fits_small (SZ.v voff + SZ.v vk);
                  let dv = inp.(SZ.add datastart vk);
                  out.(SZ.add voff vk) <- dv;
                  lemma_fits_small (SZ.v vk + 1);
                  k := SZ.add vk 1sz;
                };
                (* trailing CRLF of the frame body *)
                let e0 = inp.(SZ.add datastart vsize);
                lemma_fits_small (SZ.v datastart + SZ.v vsize + 1);
                let e1 = inp.(SZ.add (SZ.add datastart vsize) 1sz);
                if not (U8.eq e0 W.bCR && U8.eq e1 W.bLF) {
                  err := true;
                } else {
                  pos := SZ.add (SZ.add datastart vsize) 2sz;
                  off := SZ.add voff vsize;
                }
              }
            }
          }
        }
      }
    }
  };
  let vdone = !done;
  let voff = !off;
  poff := voff;
  if vdone {
    true
  } else {
    false
  }
}
#pop-options
