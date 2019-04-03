module MITLS.Repr.Opaque
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open FStar.Integers
module R = MITLS.Repr
module LB = LowParse.Spec.Bytes

let index_ok (min max:Ghost.erased nat) =
    let min = Ghost.reveal min in
    let max = Ghost.reveal max in
    min <= max /\
    0 < max /\
    max < pow2 32

let repr #p #q (b:LP.slice p q) : Type =
  (min:Ghost.erased nat &
   max: (max:Ghost.erased nat{ index_ok min max }) &
   (let min = Ghost.reveal min in
    let max = Ghost.reveal max in
    R.repr_p (LB.parse_bounded_vlbytes_t min max)
             b
             (LB.parse_bounded_vlbytes min max)))

abstract
let valid #p #q (#b:LP.slice p q) (r:repr b) (h:HS.mem) =
  let (| _, _, r |) = r in
  R.valid r h

let fp #p #q (#b:LP.slice p q) (r:repr b) =
  let (| _, _, r |) = r in
  R.fp r

let frame_valid #p #q (#b:LP.slice p q) (r:repr b) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid r h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp r) l)
    (ensures
      valid r h1)
    [SMTPat (valid r h1);
     SMTPat (B.modifies l h0 h1)]
  = let (| _, _, r |) = r in
    let open R in
    R.frame_valid r l h0 h1

/// Constructors
let mk #p #q (b:LP.slice p q) (from to:R.index b) (min max:uint_32)
  : FStar.HyperStack.ST.Stack (repr b)
    (requires fun h ->
      let min = UInt32.v min in
      let max = UInt32.v max in
      index_ok (Ghost.hide min) (Ghost.hide max) /\
     (R.valid_pos b
        (LB.parse_bounded_vlbytes min max)
        from
        to
        h
      ))
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      valid r h1 /\
      True (* ... *))
 = [@inline_let]
   let min = UInt32.v min in
   [@inline_let]
   let max = UInt32.v max in
   let r = R.mk b from to (LB.parse_bounded_vlbytes min max) in
   (| Ghost.hide min,
      Ghost.hide max,
      r |)

let max_length #p #q (#b:LP.slice p q) (r:repr b) : GTot nat =
  let (| _, max, _ |) = r in
  Ghost.reveal max

let start_pos  #p #q (#b:LP.slice p q) (r:repr b) : Tot uint_32 =
  let (| _, _, r |) = r in R.(r.start_pos)

let end_pos  #p #q (#b:LP.slice p q) (r:repr b) : Tot uint_32 =
  let (| _, _, r |) = r in R.(r.end_pos)

let length #p #q (#b:LP.slice p q) (r:repr b)
  : Tot (i:uint_32{UInt32.v i <= max_length r})
  = let (| _, _, r |) = r in
    let open R in
    admit();
    r.end_pos - r.start_pos

let as_bytes #p #q (#b:LP.slice p q) (t:repr b)
  : GTot (s:Seq.seq uint_8{Seq.length s == UInt32.v (length t)})
  = let (| _, _, r |) = t in
    let s = FStar.Bytes.reveal (R.value r) in
    assert (Seq.length s <= max_length t);
    admit();
    s
