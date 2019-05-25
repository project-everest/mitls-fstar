module EverCrypt.CRF

module Concrete = EverCrypt.Hash.Incremental
module Hash = EverCrypt.Hash 

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open FStar.HyperStack.ST 

/// migrate these 2 functions to no_extract LowStar.Buffer?
/// 
assume val to_seq 
  (#a:Type0) 
  // (#rrel #rel:B.srel a) 
  // (b:B.mbuffer a rrel rel)
  (b: B.buffer a)
  (l:UInt32.t {UInt32.v l == B.length b})
  : 
  Stack (Seq.seq a)
    (fun h0 -> B.live h0 b)
    (fun h0 s h1 -> 
      h0 == h1 /\
      B.as_seq h0 b == s )

assume val of_seq 
  (#a:Type0) 
  // (#rrel #rel:B.srel a) 
  // (b:B.mbuffer a rrel rel)
  (b: B.buffer a)
  (s: Seq.seq a) 
  : 
  Stack unit
    (fun h0 -> 
      B.live h0 b /\ 
      B.length b = Seq.length s)
    (fun h0 _ h1 -> 
      B.modifies (B.loc_buffer b) h0 h1 /\
      B.as_seq h1 b == s)


let create_in a r = 
  if model then 
    Seq.empty <: mstate 
    // (B.malloc r (Seq.empty <: bytes) 1ul <: mstate) <: state a
  else
    Concrete.create_in a r 

let update a s prev data len = 
  if model then 
    Seq.append s (to_seq data len)
    // B.upd (s <: mstate) 0ul (Seq.append (B.index (s <: mstate) 0ul) delta)
  else
    Concrete.update a s prev data len 

let finish a s prev dst = 
  assert_norm(pow2 61 < pow2 125);
  if model then 
    let tag = Model.CRF.hash a s in
    dst `of_seq` tag
  else 
    Concrete.finish a s prev dst

let free a s = if model then () else Concrete.free a s
    
