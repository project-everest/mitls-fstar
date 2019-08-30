module Model.Utils

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module HS = FStar.HyperStack
module F = Flags

// TODO: merge into Buffer.Utils?

noextract
let rec get_buffer
  (#t: Type)
  (b: B.buffer t)
  (len: U32.t)
: HST.Stack (Seq.seq t)
  (requires (fun h ->
    F.model == true /\
    B.live h b /\
    len == B.len b
  ))
  (ensures (fun h s h' ->
    B.modifies B.loc_none h h' /\
    s `Seq.equal` B.as_seq h b
  ))
  (decreases (U32.v len))
= if len = 0ul
  then Seq.empty
  else
    let x = B.index b 0ul in
    let len' = len `U32.sub` 1ul in
    let b' = B.sub b 1ul len' in
    let s = get_buffer b' len' in
    Seq.cons x s

noextract
let rec put_buffer
  (#t: Type)
  (b: B.buffer t)
  (len: U32.t)
  (s: Seq.seq t)
: HST.Stack unit
  (requires (fun h ->
    F.model == true /\
    B.live h b /\
    len == B.len b /\
    Seq.length s == B.length b
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h' /\
    B.as_seq h' b `Seq.equal` s
  ))
= if len = 0ul
  then ()
  else begin
    let b0 = B.sub b 0ul 1ul in
    B.upd b0 0ul (Seq.head s);
    let len' = len `U32.sub` 1ul in
    let b' = B.sub b 1ul len' in
    put_buffer b' len' (Seq.tail s);
    let h' = HST.get () in
    assert (B.as_seq h' b `Seq.equal` Seq.append (B.as_seq h' b0) (B.as_seq h' b'))
  end
