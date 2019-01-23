module HandshakeTranscript

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HashSpec = Hashing.Spec
module HSM = HandshakeMessages

module LP = LowParse.Low.Base
open HandshakeLog.Common
module IncHash = EverCrypt.Hash.Incremental

noeq
type state = {
  rgn:Mem.rgn;
  hash_state: B.pointer (option (a:Hash.alg & IncHash.state a));
  tx: (p:B.pointer (G.erased transcript_t){
    B.loc_disjoint (B.loc_buffer hash_state) (B.loc_buffer p)
  })
}

let region_of (s:state) = s.rgn

[@BigOps.__reduce__]
unfold
let footprint_locs (s:state) (h:HS.mem) =
  let open B in
  [loc_buffer s.hash_state;
   loc_buffer s.tx;
   (match deref h s.hash_state with
    | None -> loc_none
    | Some (| _, hash_st |) -> IncHash.footprint hash_st h)]

unfold
let footprint' (s:state) (h:HS.mem) =
  let open B in
  loc_union_l (footprint_locs s h)

let footprint s h = normalize_term (footprint' s h)

let transcript s h = G.reveal (B.deref h s.tx)

let hash_alg s h =
  match B.deref h s.hash_state with
  | None -> None
  | Some (| h, _ |) -> Some h

unfold
let invariant' s h =
  B.all_disjoint (footprint_locs s h) /\
  region_of s `region_includes` footprint s h /\
  B.live h s.hash_state /\
  B.live h s.tx /\
  (match B.deref h s.hash_state with
   | None -> transcript s h == []
   | Some (| a, hash_st |) ->
     IncHash.hashes #a h hash_st (transcript_bytes (transcript s h)))

let invariant s h = invariant' s h
open FStar.Tactics
#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --log_queries --query_stats"
#push-options "--max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3rlimit_factor 2"
module T = FStar.Tactics
let frame_inc_hashes (#a:Hash.alg) (hash_st:IncHash.state a) (h0 h1 : HS.mem) (b:hbytes) (l:B.loc)
  : Lemma
    (requires
      B.loc_disjoint l (IncHash.footprint hash_st h0) /\
      IncHash.hashes #a h0 hash_st b)
    (ensures
      IncHash.hashes #a h1 hash_st b)
  = admit()

let framing s l h0 h1 =
  assert (footprint' s h0 == footprint s h0)
    by (T.norm [delta_only [`%footprint]]);
  assert (invariant s h0 <==> invariant' s h0)
    by (T.norm [delta_only [`%invariant]]);
  match B.deref h0 s.hash_state with
    | None -> ()
    | Some (| a, hash_st |) ->
      assert (B.loc_disjoint l (IncHash.footprint hash_st h0));
      frame_inc_hashes #a hash_st h0 h1 (transcript_bytes (transcript s h0)) l

let create (r:Mem.rgn) = admit()
let set_hash_alg (s:state) = admit()
let extend_hash s b p0 p1 msg = admit()
let buf_is_hash_of_b (a:Hash.alg) (buf:Hacl.Hash.Definitions.hash_t a) (b:hbytes) : prop = admit()
let extract_hash (#a:Hash.alg) (s:state) (tag:Hacl.Hash.Definitions.hash_t a) = admit()
