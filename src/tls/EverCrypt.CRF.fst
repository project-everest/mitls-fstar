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
    let s = B.malloc r (Seq.empty <: bytes) 1ul in
    ((| a, s |) <: mstate a) <: state a
  else
    Concrete.create_in a r

let init a s =
  let open LowStar.BufferOps in
  if model then
    let s: B.pointer bytes = snd s in
    s *= S.empty
  else
    Concrete.init a s

let update a s data len =
  let open LowStar.BufferOps in
  if model then
    let s: B.pointer bytes = snd s in
    s *= (S.append !*s (to_seq data len))
  else
    Concrete.update a s data len

#push-options "--z3rlimit 50"
let finish a st dst =
  let open LowStar.BufferOps in
  if model then
    let a = fst #a st in
    let s: B.pointer bytes = snd st in
    (**) assert B.(loc_disjoint (B.loc_addr_of_buffer s)
      (B.loc_region_only true Mem.tls_tables_region));
    (**) let h0 = ST.get () in
    let hash = Model.CRF.hash a !*s in
    (**) let h1 = ST.get () in
    (**) assert (B.live h1 dst);
    (**) frame_invariant #a (B.loc_region_only true Mem.tls_tables_region) st h0 h1;
    dst `of_seq` hash
  else
    (**) let h0 = ST.get () in
    Model.CRF.concrete_hashed (G.reveal a) (Concrete.hashed #(G.reveal a) h0 st);
    Concrete.finish a st dst

let free a s =
  if model then
    B.free (snd s)
  else
    Concrete.free a s

