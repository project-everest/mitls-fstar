module HTTP.Wire.Header

(**
  A verified spec model of a *single* HTTP/1.1 header field-line (RFC 9112 §5):

      field-line = field-name ":" OWS field-value OWS CRLF

  This is the foundational primitive for a general `(name, value)` header model
  (roadmap item 1): the framing scanner currently only whitelists a couple of
  known header names, whereas real peers send an arbitrary, unordered set.

  We model a header field as a pair of byte sequences `(name, value)`.  A
  *well-formed* field (`wf_field`) has a non-empty name containing no `:`/CR/LF,
  a value containing no CR/LF, and no leading optional-whitespace on the value
  (so the single serialized `SP` after the colon is unambiguous).  The canonical
  serializer emits `name ":" SP value CRLF`; the parser locates the first colon
  (the field-name delimiter), skips the leading OWS run, then reads the value up
  to the terminating CRLF.  `lemma_parse_ser_field` proves the round-trip, even
  when the serialized field is followed by an arbitrary `rest` (the remaining
  header block) — exactly what a line-by-line iterator needs.
*)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module TCP = Common.TCP
module W   = HTTP.Wire.Common

(* ── ASCII byte constants ─────────────────────────────────────────────────── *)
inline_for_extraction let bColon : U8.t = 0x3Auy  (* ':'  *)
inline_for_extraction let bSP    : U8.t = 0x20uy  (* ' '  *)
inline_for_extraction let bHT    : U8.t = 0x09uy  (* '\t' *)

(* Optional whitespace (OWS) per RFC 9110: SP / HTAB. *)
inline_for_extraction let is_ows (b:U8.t) : bool = b = bSP || b = bHT

(* A field-name byte: anything but the ':' delimiter and the CRLF terminator. *)
inline_for_extraction let name_char (b:U8.t) : bool =
  not (b = bColon) && not (b = W.bCR) && not (b = W.bLF)

(* A field-value byte: anything but the CRLF terminator. *)
inline_for_extraction let value_char (b:U8.t) : bool =
  not (b = W.bCR) && not (b = W.bLF)

let rec all_name (s:TCP.bytes) : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then true
  else name_char (Seq.index s 0) && all_name (Seq.slice s 1 (Seq.length s))

let rec all_value (s:TCP.bytes) : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then true
  else value_char (Seq.index s 0) && all_value (Seq.slice s 1 (Seq.length s))

(* A well-formed header field: non-empty name, no delimiter/terminator bytes in
   the name, no terminator bytes in the value, and no *leading* OWS on the value
   (the serialized `: ` supplies exactly one SP of separation). *)
let wf_field (nm vl:TCP.bytes) : bool =
  Seq.length nm > 0 && all_name nm && all_value vl &&
  (Seq.length vl = 0 || not (is_ows (Seq.index vl 0)))

(* ── Serializer ───────────────────────────────────────────────────────────── *)
let colon_sp : (b:TCP.bytes{Seq.length b == 2}) =
  Seq.init 2 (fun i -> if i = 0 then bColon else bSP)

let ser_field (nm vl:TCP.bytes) : TCP.bytes =
  Seq.append nm (Seq.append colon_sp (Seq.append vl W.crlf))

(* ── Scanning primitives ──────────────────────────────────────────────────── *)

(* Index of the first byte equal to `c`, or `Seq.length s` if absent. *)
let rec idx_of (s:TCP.bytes) (c:U8.t) : Tot (i:nat{i <= Seq.length s}) (decreases Seq.length s) =
  if Seq.length s = 0 then 0
  else if Seq.index s 0 = c then 0
  else 1 + idx_of (Seq.slice s 1 (Seq.length s)) c

(* Length of the leading OWS run of `s`. *)
let rec ows_prefix_len (s:TCP.bytes) : Tot (i:nat{i <= Seq.length s}) (decreases Seq.length s) =
  if Seq.length s = 0 then 0
  else if is_ows (Seq.index s 0) then 1 + ows_prefix_len (Seq.slice s 1 (Seq.length s))
  else 0

(* ── Parser ───────────────────────────────────────────────────────────────── *)

(* Parse one field-line out of `input` (which may be followed by more of the
   header block).  Returns `Some (name, value, consumed)` where `consumed` is the
   number of bytes up to and including the terminating CRLF, or `None` if the
   line is malformed (missing colon, empty name, name/value contains a stray
   terminator, or no CRLF). *)
let parse_field (input:TCP.bytes) : GTot (option (TCP.bytes & TCP.bytes & nat)) =
  let n = Seq.length input in
  let ci = idx_of input bColon in
  if ci = 0 || ci >= n then None else
  let nm = Seq.slice input 0 ci in
  if not (all_name nm) then None else
  let afterc = Seq.slice input (ci + 1) n in
  let ows = ows_prefix_len afterc in
  let vs = ci + 1 + ows in
  let fromv = Seq.slice input vs n in
  let ei = vs + idx_of fromv W.bCR in
  if ei + 1 >= n then None else
  if not (Seq.index input (ei + 1) = W.bLF) then None else
  let vl = Seq.slice input vs ei in
  if not (all_value vl) then None else
  Some (nm, vl, ei + 2)

(* ── Helper lemmas ────────────────────────────────────────────────────────── *)

(* `all_name` / `all_value` expose their per-index consequences. *)
let rec lemma_all_name_index (s:TCP.bytes)
  : Lemma (requires all_name s)
          (ensures forall (i:nat). i < Seq.length s ==> name_char (Seq.index s i))
          (decreases Seq.length s)
= if Seq.length s = 0 then ()
  else begin
    lemma_all_name_index (Seq.slice s 1 (Seq.length s));
    let tl = Seq.slice s 1 (Seq.length s) in
    assert (forall (i:nat). i < Seq.length tl ==> name_char (Seq.index tl i));
    assert (forall (i:nat). 0 < i /\ i < Seq.length s ==>
              Seq.index s i == Seq.index tl (i - 1))
  end

let rec lemma_all_value_index (s:TCP.bytes)
  : Lemma (requires all_value s)
          (ensures forall (i:nat). i < Seq.length s ==> value_char (Seq.index s i))
          (decreases Seq.length s)
= if Seq.length s = 0 then ()
  else begin
    lemma_all_value_index (Seq.slice s 1 (Seq.length s));
    let tl = Seq.slice s 1 (Seq.length s) in
    assert (forall (i:nat). i < Seq.length tl ==> value_char (Seq.index tl i));
    assert (forall (i:nat). 0 < i /\ i < Seq.length s ==>
              Seq.index s i == Seq.index tl (i - 1))
  end

(* If no byte of `pre` equals `c` and `rest` begins with `c`, the first `c` in
   `pre ++ rest` sits exactly at `Seq.length pre`. *)
let rec lemma_idx_of_run (pre:TCP.bytes) (c:U8.t) (rest:TCP.bytes)
  : Lemma (requires (forall (i:nat). i < Seq.length pre ==> Seq.index pre i <> c) /\
                    Seq.length rest > 0 /\ Seq.index rest 0 == c)
          (ensures idx_of (Seq.append pre rest) c == Seq.length pre)
          (decreases Seq.length pre)
= let s = Seq.append pre rest in
  if Seq.length pre = 0 then begin
    Seq.lemma_eq_intro s rest
  end else begin
    let pre' = Seq.slice pre 1 (Seq.length pre) in
    Seq.lemma_eq_intro (Seq.slice s 1 (Seq.length s)) (Seq.append pre' rest);
    assert (Seq.index s 0 == Seq.index pre 0);
    assert (forall (i:nat). i < Seq.length pre' ==> Seq.index pre' i == Seq.index pre (i + 1));
    lemma_idx_of_run pre' c rest
  end

(* The leading OWS run of `SP :: rest` is exactly 1 when `rest` does not itself
   begin with OWS. *)
let lemma_ows_prefix_sp (rest:TCP.bytes)
  : Lemma (requires Seq.length rest = 0 \/ not (is_ows (Seq.index rest 0)))
          (ensures ows_prefix_len (Seq.append (Seq.create 1 bSP) rest) == 1)
= let s = Seq.append (Seq.create 1 bSP) rest in
  assert (Seq.index s 0 == bSP);
  Seq.lemma_eq_intro (Seq.slice s 1 (Seq.length s)) rest

(* Head of `a ++ b` is not OWS, given `a`'s head isn't (or `a` is empty and `b`'s
   head isn't). *)
let lemma_append_head_not_ows (a b:TCP.bytes)
  : Lemma (requires (Seq.length a = 0 \/ not (is_ows (Seq.index a 0))) /\
                    Seq.length b > 0 /\ not (is_ows (Seq.index b 0)))
          (ensures Seq.length (Seq.append a b) = 0 \/
                   not (is_ows (Seq.index (Seq.append a b) 0)))
= if Seq.length a = 0 then Seq.lemma_eq_intro (Seq.append a b) b
  else SP.append_slices a b

(* Specialised: the value-plus-terminator `vl ++ (CRLF ++ rest)` never begins with
   OWS (its head is either the value's non-OWS first byte or the CR of CRLF). *)
let lemma_vl_tail_head_not_ows (vl rest:TCP.bytes)
  : Lemma (requires Seq.length vl = 0 \/ not (is_ows (Seq.index vl 0)))
          (ensures (let vt = Seq.append vl (Seq.append W.crlf rest) in
                    Seq.length vt = 0 \/ not (is_ows (Seq.index vt 0))))
= let t = Seq.append W.crlf rest in
  assert_norm (Seq.index W.crlf 0 == W.bCR);
  SP.append_slices W.crlf rest;
  assert (Seq.length t > 0 /\ not (is_ows (Seq.index t 0)));
  lemma_append_head_not_ows vl t

(* ── Round-trip ───────────────────────────────────────────────────────────── *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 200 --split_queries always"
let lemma_parse_ser_field (nm vl rest:TCP.bytes)
  : Lemma (requires wf_field nm vl)
          (ensures parse_field (Seq.append (ser_field nm vl) rest)
                   == Some (nm, vl, Seq.length (ser_field nm vl)))
= let sf = ser_field nm vl in
  let input = Seq.append sf rest in
  (* Layout: input == nm ++ colon_sp ++ vl ++ crlf ++ rest. *)
  let tail_cr  = Seq.append W.crlf rest in           (* CRLF ++ rest              *)
  let vl_tail  = Seq.append vl tail_cr in             (* vl ++ CRLF ++ rest        *)
  let cs_tail  = Seq.append colon_sp vl_tail in       (* ": " ++ vl ++ CRLF ++ rest*)
  (* Reassociate  input == nm ++ (colon_sp ++ (vl ++ (crlf ++ rest))). *)
  Seq.append_assoc vl W.crlf rest;
  Seq.append_assoc colon_sp vl tail_cr;
  Seq.append_assoc nm colon_sp vl_tail;
  Seq.lemma_eq_intro input (Seq.append nm cs_tail);

  let n = Seq.length input in

  (* 1. First colon is at |nm| (name has none; colon_sp starts with ':'). *)
  lemma_all_name_index nm;
  assert (Seq.index cs_tail 0 == bColon);
  lemma_idx_of_run nm bColon cs_tail;
  let ci = idx_of input bColon in
  assert (ci == Seq.length nm);
  assert (Seq.length nm < n);

  (* name slice recovers nm *)
  SP.append_slices nm cs_tail;
  assert (Seq.slice input 0 ci == nm);

  (* 2. afterc == SP :: (vl ++ CRLF ++ rest); OWS run == 1. *)
  let afterc = Seq.slice input (ci + 1) n in
  (* colon_sp == bColon :: bSP; drop the ':' from cs_tail. *)
  let sp_tail = Seq.append (Seq.create 1 bSP) vl_tail in
  assert (Seq.equal cs_tail (Seq.append (Seq.create 1 bColon) sp_tail));
  Seq.lemma_eq_intro afterc sp_tail;
  (* head of vl_tail is not OWS: either vl[0] (wf) or crlf[0]=CR *)
  lemma_vl_tail_head_not_ows vl rest;
  lemma_ows_prefix_sp vl_tail;
  let ows = ows_prefix_len afterc in
  assert (ows == 1);
  let vs = ci + 1 + ows in
  assert (vs == Seq.length nm + 2);

  (* 3. fromv == vl ++ (CRLF ++ rest); first CR at |vl|. *)
  let fromv = Seq.slice input vs n in
  Seq.lemma_eq_intro fromv vl_tail;
  lemma_all_value_index vl;
  assert (Seq.index tail_cr 0 == W.bCR);
  lemma_idx_of_run vl W.bCR tail_cr;
  let ei = vs + idx_of fromv W.bCR in
  assert (ei == vs + Seq.length vl);

  (* input[ei] == CR, input[ei+1] == LF *)
  SP.append_slices vl tail_cr;
  assert (Seq.index input ei == W.bCR);
  assert (Seq.index input (ei + 1) == W.bLF);
  assert (ei + 1 < n);

  (* value slice recovers vl *)
  Seq.lemma_eq_intro (Seq.slice input vs ei) vl;
  assert (Seq.length sf == Seq.length nm + 2 + Seq.length vl + 2);
  assert (ei + 2 == Seq.length sf)
#pop-options
