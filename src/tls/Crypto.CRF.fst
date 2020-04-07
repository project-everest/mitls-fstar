module Crypto.CRF

module Concrete = EverCrypt.Hash.Incremental
module Hash = EverCrypt.Hash
module HD = Spec.Hash.Definitions

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open FStar.HyperStack.ST

(* Debug output, shared by client and server *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("CRF| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_HS then print else (fun _ -> ())

/// Overview
/// --------
///
/// This module is not meant to be extracted. To that end, we use -bundle
/// Model.* in the arguments passed to KreMLin. Combined with elimination at
/// extraction-time of ideal code, none of the remaining declarations in this module
/// should be reachable.

/// Helpers
/// -------
///
/// migrate these 2 functions to no_extract LowStar.Buffer?
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

/// Implementing abstract types
/// ---------------------------

/// This is very finely tuned to avoid inference issues.
type mstate a = a': alg { a' == a } & p:B.pointer bytes {
  B.(loc_disjoint (loc_addr_of_buffer p) (loc_region_only true Mem.tls_tables_region))
}

inline_for_extraction
let state (a: alg) =
  if model then
    mstate a
  else
    Concrete.state a

noextract let ideal (#a:alg) (s:state a)
  : Pure (mstate a) (requires model) (ensures fun _ -> True)
  = s
noextract let gideal (#a:e_alg) (s:state (G.reveal a))
  : Pure (mstate (G.reveal a)) (requires model) (ensures fun _ -> True)
  = s

inline_for_extraction noextract let real (#a:alg) (s:state a)
  : Pure (Concrete.state a) (requires not model) (ensures fun _ -> True)
  = s
inline_for_extraction noextract let greal (#a:e_alg) (s:state (G.reveal a))
  : Pure (Concrete.state (G.reveal a)) (requires not model) (ensures fun _ -> True)
  = s

let freeable #a h (s:state a) =
  if model then
    let (| a, s |) = ideal s in
    B.freeable s
  else
    Concrete.freeable h (real s)

let footprint #a h (s: state a) =
  if model then
    B.loc_addr_of_buffer (dsnd (ideal s))
  else
    Concrete.footprint h (real s)

let invariant #a h (s: state a) =
  if model then
    let (| _, s |) = ideal s in
    B.live h s /\ S.length (B.deref h s) < pow2 61
  else
    Concrete.invariant h (real s)

let invariant_loc_in_footprint #_ _ _ = ()

let hashed #a h (s: state a) =
  if model then
    let (| _, s |) = ideal s in
    B.deref h s
  else
    Concrete.hashed h (real s)

#push-options "--max_ifuel 1"
let hash_fits #_ _ _ =
  assert_norm (pow2 61 < pow2 125);
  ()
#pop-options

let frame_invariant #_ _ _ _ _ = ()
let frame_hashed #_ _ _ _ _ = ()
let frame_freeable #_ _ _ _ _ = ()


/// Actual API
/// ----------

let create_in a r =
  if model then
    let s = B.malloc r (Seq.empty <: bytes) 1ul in
    ((| a, s |) <: mstate a) <: state a
  else
    Concrete.create_in a r

let init a s =
  let open LowStar.BufferOps in
  if model then
    dsnd (gideal s) *= S.empty
  else
    Concrete.init a (greal s)

let update a s data len =
  let open LowStar.BufferOps in
  if model then
    let (| _, s |) = gideal s in
    s *= (S.append !*s (to_seq data len))
  else
    (let h0 = get() in
    trace ("UPDATE "^(Bytes.hex_of_bytes (Bytes.of_buffer len data)));
    let h1 = get() in
    frame_invariant B.loc_none s h0 h1;
    Concrete.update a (greal s) data len)

#push-options "--z3rlimit 50"
let finish a st dst =
  let open LowStar.BufferOps in
  if model then
    let (| a, s |) = gideal st in
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
    B.free (dsnd (gideal s))
  else
    Concrete.free a s
