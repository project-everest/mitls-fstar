module HandshakeTranscript

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module Hash = Hashing
module HSM = HandshakeMessages

open HandshakeLog.Common

module IncHash = EverCrypt.Hash.Incremental

#reset-options "--using_facts_from '* -LowParse -FStar.Tactics -FStar.Reflection' --max_fuel 0 --max_ifuel 0"

noeq
type state = {
  rgn:Mem.rgn;
  hash_state: B.pointer (option (a:Hash.alg & IncHash.state a));
  tx: (p:B.pointer (G.erased transcript_t){
    B.loc_disjoint (B.loc_buffer hash_state) (B.loc_buffer p)
  })
}

let region_of s = s.rgn

[@BigOps.__reduce__]
unfold
let footprint_locs (s:state) (h:HS.mem) =
  let open B in
  [
   (match deref h s.hash_state with
    | None -> loc_none
    | Some (| _, hash_st |) -> IncHash.footprint hash_st h);
   loc_buffer s.hash_state;
   loc_buffer s.tx;]

unfold
let footprint' (s:state) (h:HS.mem) =
  let open B in
  loc_union_l (footprint_locs s h)

let footprint s h = BigOps.normal (footprint' s h)

let transcript s h = G.reveal (B.deref h s.tx)

let hash_alg s h =
  match B.deref h s.hash_state with
  | None -> None
  | Some (| a, _ |) -> Some a

let invariant s h =
  B.all_disjoint (footprint_locs s h) /\
  region_of s `region_includes` footprint s h /\
  B.live h s.hash_state /\
  B.live h s.tx /\
  (match B.deref h s.hash_state with
   | None -> transcript s h == []
   | Some (| a, hash_st |) ->
     IncHash.hashes #a h hash_st (transcript_bytes (transcript s h)))

private
let frame_inc_hashes (#a:Hash.alg) (hash_st:IncHash.state a) (h0 h1 : HS.mem) (b:hbytes) (l:B.loc)
  : Lemma
    (requires
      B.loc_disjoint l (IncHash.footprint hash_st h0) /\
      B.modifies l h0 h1 /\
      IncHash.hashes #a h0 hash_st b)
    (ensures
      IncHash.hashes #a h1 hash_st b)
  = assert (IncHash.footprint hash_st h0 == B.(loc_union (loc_buffer (hash_st.IncHash.buf))
                                                         (EverCrypt.Hash.footprint (hash_st.IncHash.hash_state) h0)));
    IncHash.modifies_disjoint_preserves l h0 h1 hash_st

#set-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
module T = FStar.Tactics
let framing s l h0 h1 =
  assert (footprint' s h0 == footprint s h0)
    by (T.norm [delta_only [`%footprint]]);
  assert (footprint' s h1 == footprint s h1)
    by (T.norm [delta_only [`%footprint]]);
  match B.deref h0 s.hash_state with
    | None -> ()
    | Some (| a, hash_st |) ->
      assert (B.loc_disjoint l (IncHash.footprint hash_st h0));
      frame_inc_hashes #a hash_st h0 h1 (transcript_bytes (transcript s h0)) l

#set-options "--max_fuel 0 --max_ifuel 0"

let create r =
  let hash_state = B.malloc r None 1ul in
  let tx = B.malloc r (G.hide []) 1ul in
  { rgn = r; hash_state = hash_state; tx = tx }

#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"
let set_hash_alg a s =
  let h0 = ST.get () in

  let hash_st = IncHash.create_in a s.rgn in

  let h1 = ST.get () in

  B.upd s.hash_state 0ul (Some (| a, hash_st |));

  let h2 = ST.get () in

  //AR: this does not have a pattern, so need to call explicitly
  IncHash.modifies_disjoint_preserves (B.loc_buffer s.hash_state) h1 h2 hash_st;

  //AR: the postcondition in IncHash is in terms of Hash.fresh_loc, that needs fixing 
  assume (B.(fresh_loc (IncHash.footprint hash_st h2) h0 h2));  

  //AR: surprising that we can't prove it ...
  assume (B.live h2 hash_st.IncHash.buf)

let lemma_transcript_bytes (hd:HSM.hs_msg) (l:transcript_t)
  : Lemma (transcript_bytes (hd::l) ==
           Seq.append (transcript_bytes l) (format_hs_msg hd))
  = ()

#set-options "--max_fuel 0 --max_ifuel 0"
let extend_hash s b p0 p1 msg =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | None -> ()
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in
    let sub_b = B.sub b p0 (p1 - p0) in
    assume (Seq.length (G.reveal prev_bytes) + UInt32.v (p1 - p0) < pow2 61);

    let h0 = ST.get () in

    let new_hash_st = IncHash.update a hash_st prev_bytes sub_b (p1 - p0) in

    let h1 = ST.get () in

    B.upd s.hash_state 0ul (Some (| a, new_hash_st |));

    let e_tx = G.elift2 Cons msg e_tx in
    B.upd s.tx 0ul e_tx;

    let h3 = ST.get () in

    //AR: this does not have a pattern, so need to call explicitly
    IncHash.modifies_disjoint_preserves (B.loc_union (B.loc_buffer s.hash_state)
                                                     (B.loc_buffer s.tx)) h1 h3 new_hash_st;

    lemma_transcript_bytes (G.reveal msg) (transcript s h0)

let extract_hash #a s tag =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in

    let h0 = ST.get () in

    IncHash.finish a hash_st prev_bytes tag;

    let h1 = ST.get () in

    assume (Seq.length (G.reveal prev_bytes) < Spec.Hash.Definitions.max_input_length a);

    assume (B.(loc_includes (loc_union (footprint s h1) (loc_buffer tag))
                            (loc_union (IncHash.footprint hash_st h1) (loc_buffer tag))))
