module HTTP.Wire.Common

(**
  Shared byte / ASCII / numeric helpers for the hand-written HTTP/1.1 wire
  formats (`HTTP.Wire.Chunked`, `HTTP.Wire.Length`).

  HTTP is a *text* protocol whose fields (request line, status line, headers,
  chunk sizes) exceed the expressive power of EverParse/QuackyDucky — exactly as
  the TFTP wire format does — so the two HTTP wire unions are written and proved
  BY HAND over `FStar.Seq`.  This module factors out the reusable pieces:

    * ASCII byte constants (SP, CR, LF, ':') and the CRLF token;
    * single decimal / hex digit encode+decode with their inversion lemmas;
    * FIXED-WIDTH numeric fields — 3-digit decimal (status code), 8-digit decimal
      (Content-Length), 4-hex-digit (chunk size) — with round-trip lemmas.  Fixed
      width keeps the inversion proofs mechanical (like TFTP's 2-byte big-endian
      fields) and is HTTP-legal: leading zeros are permitted in both chunk-size
      (RFC 7230 §4.1: `chunk-size = 1*HEXDIG`) and Content-Length (`1*DIGIT`).
**)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module ML  = FStar.Math.Lemmas
module TCP = Common.TCP

(* ─── ASCII byte constants ─────────────────────────────────────────────────── *)
inline_for_extraction let bSP    : U8.t = 0x20uy  (* ' '  *)
inline_for_extraction let bCR    : U8.t = 0x0Duy  (* '\r' *)
inline_for_extraction let bLF    : U8.t = 0x0Auy  (* '\n' *)
inline_for_extraction let bColon : U8.t = 0x3Auy  (* ':'  *)
let bZero  : U8.t = 0x30uy  (* '0'  *)

(* CRLF, the HTTP line terminator. *)
let crlf : (b:TCP.bytes{Seq.length b == 2}) =
  Seq.init 2 (fun i -> if i = 0 then bCR else bLF)

(* ─── Single decimal digit ─────────────────────────────────────────────────── *)
inline_for_extraction
let is_dec (b:U8.t) : bool = 0x30uy `U8.lte` b && b `U8.lte` 0x39uy

let dig (d:nat{d < 10}) : U8.t = U8.uint_to_t (0x30 + d)

let undig (b:U8.t{is_dec b}) : (n:nat{n < 10}) = U8.v b - 0x30

let lemma_dig_undig (d:nat{d < 10})
  : Lemma (is_dec (dig d) /\ undig (dig d) == d)
          [SMTPat (dig d)]
= ()

(* ─── Single hex digit (lowercase) ─────────────────────────────────────────── *)
inline_for_extraction
let is_hex (b:U8.t) : bool =
  (0x30uy `U8.lte` b && b `U8.lte` 0x39uy) ||   (* '0'..'9' *)
  (0x61uy `U8.lte` b && b `U8.lte` 0x66uy)      (* 'a'..'f' *)

let hexdig (d:nat{d < 16}) : U8.t =
  if d < 10 then U8.uint_to_t (0x30 + d) else U8.uint_to_t (0x61 + d - 10)

let unhex (b:U8.t{is_hex b}) : (n:nat{n < 16}) =
  if U8.v b <= 0x39 then U8.v b - 0x30 else U8.v b - 0x61 + 10

let lemma_hexdig_unhex (d:nat{d < 16})
  : Lemma (is_hex (hexdig d) /\ unhex (hexdig d) == d)
          [SMTPat (hexdig d)]
= ()

(* ─── Fixed 3-digit decimal (status code) ──────────────────────────────────── *)
let enc_dec3 (n:nat{n < 1000}) : (b:TCP.bytes{Seq.length b == 3}) =
  Seq.init 3 (fun i -> if i = 0 then dig (n / 100)
                       else if i = 1 then dig ((n / 10) % 10)
                       else dig (n % 10))

let dec3_ok (b:TCP.bytes) : bool =
  Seq.length b = 3 && is_dec (Seq.index b 0) && is_dec (Seq.index b 1) && is_dec (Seq.index b 2)

let dec_dec3 (b:TCP.bytes{dec3_ok b}) : nat =
  100 * undig (Seq.index b 0) + 10 * undig (Seq.index b 1) + undig (Seq.index b 2)

#push-options "--z3rlimit 40"
let lemma_dec3_roundtrip (n:nat{n < 1000})
  : Lemma (dec3_ok (enc_dec3 n) /\ dec_dec3 (enc_dec3 n) == n)
= ML.lemma_div_mod n 10;
  ML.lemma_div_mod n 100
#pop-options

(* ─── Fixed 4-digit decimal block (value < 10^4) ───────────────────────────── *)
let enc_dec4 (n:nat{n < 10000}) : (b:TCP.bytes{Seq.length b == 4}) =
  Seq.init 4 (fun i -> dig ((n / (match i with 0 -> 1000 | 1 -> 100 | 2 -> 10 | _ -> 1)) % 10))

let dec4_ok (b:TCP.bytes) : bool =
  Seq.length b = 4 &&
  is_dec (Seq.index b 0) && is_dec (Seq.index b 1) &&
  is_dec (Seq.index b 2) && is_dec (Seq.index b 3)

let dec_dec4 (b:TCP.bytes{dec4_ok b}) : nat =
  undig (Seq.index b 0) * 1000 +
  undig (Seq.index b 1) * 100 +
  undig (Seq.index b 2) * 10 +
  undig (Seq.index b 3)

#push-options "--z3rlimit 40"
let lemma_dec4_roundtrip (n:nat{n < 10000})
  : Lemma (dec4_ok (enc_dec4 n) /\ dec_dec4 (enc_dec4 n) == n)
= ML.lemma_div_mod n 10;
  ML.lemma_div_mod n 100;
  ML.lemma_div_mod n 1000
#pop-options

(* ─── Fixed 8-digit decimal (Content-Length, < 10^8) ─── two 4-digit blocks. ── *)
let max_len8 : nat = 100000000  (* 10^8 *)

let enc_dec8 (n:nat{n < max_len8}) : (b:TCP.bytes{Seq.length b == 8}) =
  Seq.append (enc_dec4 (n / 10000)) (enc_dec4 (n % 10000))

let dec8_ok (b:TCP.bytes) : bool =
  Seq.length b = 8 &&
  dec4_ok (Seq.slice b 0 4) && dec4_ok (Seq.slice b 4 8)

let dec_dec8 (b:TCP.bytes{dec8_ok b}) : nat =
  dec_dec4 (Seq.slice b 0 4) * 10000 + dec_dec4 (Seq.slice b 4 8)

#push-options "--z3rlimit 40"
let lemma_dec8_roundtrip (n:nat{n < max_len8})
  : Lemma (dec8_ok (enc_dec8 n) /\ dec_dec8 (enc_dec8 n) == n)
= ML.lemma_div_mod n 10000;
  let hi = n / 10000 in
  let lo = n % 10000 in
  lemma_dec4_roundtrip hi;
  lemma_dec4_roundtrip lo;
  SP.append_slices (enc_dec4 hi) (enc_dec4 lo)
#pop-options

(* ─── Fixed 4-hex-digit (chunk size, < 2^16) ───────────────────────────────── *)
let enc_hex4 (n:nat{n < 65536}) : (b:TCP.bytes{Seq.length b == 4}) =
  Seq.init 4 (fun i -> hexdig ((n / (match i with 0 -> 4096 | 1 -> 256 | 2 -> 16 | _ -> 1)) % 16))

let hex4_ok (b:TCP.bytes) : bool =
  Seq.length b = 4 &&
  is_hex (Seq.index b 0) && is_hex (Seq.index b 1) &&
  is_hex (Seq.index b 2) && is_hex (Seq.index b 3)

let dec_hex4 (b:TCP.bytes{hex4_ok b}) : nat =
  unhex (Seq.index b 0) * 4096 +
  unhex (Seq.index b 1) * 256 +
  unhex (Seq.index b 2) * 16 +
  unhex (Seq.index b 3)

#push-options "--z3rlimit 60"
let lemma_hex4_roundtrip (n:nat{n < 65536})
  : Lemma (hex4_ok (enc_hex4 n) /\ dec_hex4 (enc_hex4 n) == n)
= ML.lemma_div_mod n 16;
  ML.lemma_div_mod n 256;
  ML.lemma_div_mod n 4096
#pop-options

(* ─── Variable-width hex (RFC 9112 chunk-size = 1*HEXDIG) ───────────────────── *)
(* A byte sequence is a hex run iff every byte is a hex digit (length may be 0). *)
let rec all_hex (h:TCP.bytes) : Tot bool (decreases Seq.length h) =
  if Seq.length h = 0 then true
  else is_hex (Seq.index h 0) && all_hex (Seq.slice h 1 (Seq.length h))

(* Big-endian value of a hex run, accumulated most-significant-digit first —
   matching the impl decoder's `size := size*16 + d` left-to-right scan. *)
let rec dec_hex_acc (h:TCP.bytes{all_hex h}) (acc:nat) : Tot nat (decreases Seq.length h) =
  if Seq.length h = 0 then acc
  else dec_hex_acc (Seq.slice h 1 (Seq.length h)) (acc * 16 + unhex (Seq.index h 0))

let dec_hex_var (h:TCP.bytes{all_hex h}) : nat = dec_hex_acc h 0

(* `all_hex` peels its first byte; the tail of a hex run is a hex run. *)
let lemma_all_hex_tail (h:TCP.bytes)
  : Lemma (requires all_hex h /\ Seq.length h > 0)
          (ensures all_hex (Seq.slice h 1 (Seq.length h)) /\ is_hex (Seq.index h 0)) = ()

(* Length of the maximal hex-digit run at the front of `input` (the size token). *)
let rec hex_prefix_len (input:TCP.bytes) : Tot nat (decreases Seq.length input) =
  if Seq.length input = 0 then 0
  else if is_hex (Seq.index input 0)
       then 1 + hex_prefix_len (Seq.slice input 1 (Seq.length input))
       else 0

let rec lemma_hex_prefix_len_bound (input:TCP.bytes)
  : Lemma (ensures hex_prefix_len input <= Seq.length input) (decreases Seq.length input)
= if Seq.length input = 0 then ()
  else if is_hex (Seq.index input 0)
       then lemma_hex_prefix_len_bound (Seq.slice input 1 (Seq.length input))
       else ()

(* `dec_hex_acc` distributes over concatenation of hex runs (it folds the
   accumulator left-to-right, so the value of `xs ++ ys` is the value of `ys`
   folded onto the value of `xs`). *)
let rec lemma_dec_hex_acc_app (xs ys:TCP.bytes) (acc:nat)
  : Lemma
    (requires all_hex xs /\ all_hex ys)
    (ensures
      all_hex (Seq.append xs ys) /\
      dec_hex_acc (Seq.append xs ys) acc == dec_hex_acc ys (dec_hex_acc xs acc))
    (decreases Seq.length xs)
= let f = Seq.append xs ys in
  if Seq.length xs = 0 then
    Seq.lemma_eq_intro f ys
  else begin
    let xs' = Seq.slice xs 1 (Seq.length xs) in
    Seq.lemma_index_app1 xs ys 0;                                   (* index f 0 == index xs 0 *)
    Seq.lemma_eq_intro (Seq.slice f 1 (Seq.length f)) (Seq.append xs' ys);
    lemma_dec_hex_acc_app xs' ys (acc * 16 + unhex (Seq.index xs 0))
  end

(* Appending one hex digit multiplies the running value by 16 and adds it — the
   step law of the impl decoder's `size := size*16 + d` hex scan. *)
let lemma_dec_hex_snoc (hs:TCP.bytes) (c:U8.t)
  : Lemma
    (requires all_hex hs /\ is_hex c)
    (ensures
      all_hex (Seq.append hs (Seq.create 1 c)) /\
      dec_hex_var (Seq.append hs (Seq.create 1 c)) == dec_hex_var hs * 16 + unhex c)
= let cs = Seq.create 1 c in
  assert (all_hex cs);
  lemma_dec_hex_acc_app hs cs 0;
  (* dec_hex_acc cs a == a*16 + unhex c (single digit) *)
  Seq.lemma_eq_intro (Seq.slice cs 1 (Seq.length cs)) (Seq.empty #U8.t)

(* ─── Byte-sequence literals and boolean equality ──────────────────────────── *)
(* Build a concrete byte string from a list (for the fixed HTTP literals). *)
let lit (l:list U8.t) : TCP.bytes = Seq.seq_of_list l

(* Boolean equality on byte sequences (parse is GTot, but we branch on a Tot
   boolean so the fixed literals are checked cheaply; the reflection lemma turns
   it into structural `Seq.equal`, so the round-trip proofs never enumerate the
   literal bytes). *)
let rec bseq_eq (a b:TCP.bytes) : Tot bool (decreases Seq.length a) =
  if Seq.length a <> Seq.length b then false
  else if Seq.length a = 0 then true
  else Seq.index a 0 = Seq.index b 0 &&
       bseq_eq (Seq.slice a 1 (Seq.length a)) (Seq.slice b 1 (Seq.length b))

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec lemma_bseq_eq (a b:TCP.bytes)
  : Lemma (ensures (bseq_eq a b <==> Seq.equal a b)) (decreases Seq.length a)
= if Seq.length a <> Seq.length b then ()
  else if Seq.length a = 0 then Seq.lemma_eq_intro a b
  else begin
    let n = Seq.length a in
    let a' = Seq.slice a 1 n in
    let b' = Seq.slice b 1 n in
    lemma_bseq_eq a' b';
    SP.cons_head_tail a;
    SP.cons_head_tail b;
    (* a == cons (head a) a', b == cons (head b) b', with head = index _ 0 *)
    introduce Seq.equal a b ==> (Seq.index a 0 == Seq.index b 0 /\ Seq.equal a' b')
    with _. SP.lemma_cons_inj (Seq.head a) (Seq.head b) (Seq.tail a) (Seq.tail b)
  end
#pop-options

(* Reflexivity corollary, used pervasively in the round-trip proofs. *)
let lemma_bseq_eq_refl (a:TCP.bytes) : Lemma (bseq_eq a a) =
  lemma_bseq_eq a a

(* ─── Space-delimited tokens (the request-line target) ─────────────────────── *)
(* A field terminated on the wire by a space (0x20) contains no embedded space. *)
let rec space_free (b:TCP.bytes) : Tot bool (decreases Seq.length b) =
  if Seq.length b = 0 then true
  else Seq.index b 0 <> bSP && space_free (Seq.slice b 1 (Seq.length b))

type token = s:TCP.bytes { space_free s }

(* Split `b` at the first space into (bytes-before, bytes-after), or None. *)
let rec split_sp (b:TCP.bytes)
  : Tot (option (TCP.bytes & TCP.bytes)) (decreases Seq.length b) =
  if Seq.length b = 0 then None
  else if Seq.index b 0 = bSP then Some (Seq.empty, Seq.slice b 1 (Seq.length b))
  else
    (match split_sp (Seq.slice b 1 (Seq.length b)) with
     | None -> None
     | Some (pre, post) -> Some (Seq.cons (Seq.index b 0) pre, post))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec split_sp_append (s rest:TCP.bytes)
  : Lemma
      (requires space_free s)
      (ensures split_sp (Seq.append s (Seq.cons bSP rest)) == Some (s, rest))
      (decreases Seq.length s)
= let tr = Seq.cons bSP rest in
  let full = Seq.append s tr in
  if Seq.length s = 0 then begin
    Seq.append_empty_l tr;
    Seq.lemma_eq_elim full tr;
    SP.head_cons bSP rest;
    SP.lemma_tl bSP rest;
    Seq.lemma_eq_elim s Seq.empty;
    assert (Seq.index full 0 == bSP);
    assert (Seq.slice full 1 (Seq.length full) == rest)
  end
  else begin
    SP.lemma_slice_first_in_append s tr 1;
    Seq.lemma_index_app1 s tr 0;
    assert (Seq.index s 0 <> bSP);
    assert (space_free (Seq.slice s 1 (Seq.length s)));
    split_sp_append (Seq.slice s 1 (Seq.length s)) rest;
    SP.cons_head_tail s;
    assert (Seq.length full > 0);
    assert (Seq.index full 0 <> bSP)
  end
#pop-options
