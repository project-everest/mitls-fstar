module HSL.Transcript

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

open HSL.Common

module IncHash = EverCrypt.Hash.Incremental

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse'"

noeq
type state = {
  rgn: Mem.rgn;
  hash_state: B.pointer (option (a:alg & IncHash.state a));
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
   | None -> transcript s h == Transcript_nil
   | Some (| a, hash_st |) ->
     IncHash.hashes #a h hash_st (transcript_bytes (transcript s h)))

private
let frame_inc_hashes (#a:alg) (hash_st:IncHash.state a) (h0 h1 : HS.mem) (b:bytes) (l:B.loc)
  : Lemma
    (requires
      B.loc_disjoint l (IncHash.footprint hash_st h0) /\
      B.modifies l h0 h1 /\
      IncHash.hashes #a h0 hash_st b)
    (ensures
      IncHash.hashes #a h1 hash_st b)
  = IncHash.modifies_disjoint_preserves l h0 h1 hash_st

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


let create r =
  let hash_state = B.malloc r None 1ul in
  let tx = B.malloc r (G.hide Transcript_nil) 1ul in
  { rgn = r; hash_state = hash_state; tx = tx }

let set_hash_alg a s =
  let h0 = ST.get () in

  let hash_st = IncHash.create_in a s.rgn in

  let h1 = ST.get () in

  B.upd s.hash_state 0ul (Some (| a, hash_st |));

  let h2 = ST.get () in

  //AR: this does not have a pattern, so need to call explicitly
  IncHash.modifies_disjoint_preserves (B.loc_buffer s.hash_state) h1 h2 hash_st;

  //AR: the postcondition in IncHash is in terms of Hash.fresh_loc, that needs fixing 
  assume (B.(fresh_loc (IncHash.footprint hash_st h2) h0 h2))

let lemma_transcript_bytes (m:HSM.handshake) (t:transcript_t)
  : Lemma
      (requires (can_extend_with_hsm t))
      (ensures  (transcript_bytes (extend_transcript t m) ==
                 Seq.append (transcript_bytes t) (format_hs_msg m)))
  = admit ()

let lemma_transcript_bytes12 (m:HSM12.handshake12) (t:transcript_t)
  : Lemma
      (requires (can_extend_with_hsm12 t))
      (ensures  (transcript_bytes (extend_transcript12 t m) ==
                 Seq.append (transcript_bytes t) (format_hs12_msg m)))
  = admit ()

let lemma_transcript_bytes13 (m:HSM13.handshake13) (t:transcript_t)
  : Lemma
      (requires (can_extend_with_hsm13 t))
      (ensures  (transcript_bytes (extend_transcript13 t m) ==
                 Seq.append (transcript_bytes t) (format_hs13_msg m)))
  = admit ()

#set-options "--z3rlimit 40 --max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
let extend_hash s b p0 p1 msg =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in
    let sub_b = B.sub b p0 (p1 - p0) in
    assume (Seq.length (G.reveal prev_bytes) + UInt32.v (p1 - p0) < pow2 61);

    let h0 = ST.get () in

    let new_hash_st = IncHash.update a hash_st prev_bytes sub_b (p1 - p0) in

    let h1 = ST.get () in

    B.upd s.hash_state 0ul (Some (| a, new_hash_st |));

    let e_tx = G.elift2_p extend_transcript e_tx msg in
    B.upd s.tx 0ul e_tx;

    let h3 = ST.get () in

    //AR: this does not have a pattern, so need to call explicitly
    IncHash.modifies_disjoint_preserves (B.loc_union (B.loc_buffer s.hash_state)
                                                     (B.loc_buffer s.tx)) h1 h3 new_hash_st;

    lemma_transcript_bytes (G.reveal msg) (transcript s h0)

let extend_hash12 s b p0 p1 msg =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in
    let sub_b = B.sub b p0 (p1 - p0) in
    assume (Seq.length (G.reveal prev_bytes) + UInt32.v (p1 - p0) < pow2 61);

    let h0 = ST.get () in

    let new_hash_st = IncHash.update a hash_st prev_bytes sub_b (p1 - p0) in

    let h1 = ST.get () in

    B.upd s.hash_state 0ul (Some (| a, new_hash_st |));

    let e_tx = G.elift2_p extend_transcript12 e_tx msg in
    B.upd s.tx 0ul e_tx;

    let h3 = ST.get () in

    //AR: this does not have a pattern, so need to call explicitly
    IncHash.modifies_disjoint_preserves (B.loc_union (B.loc_buffer s.hash_state)
                                                     (B.loc_buffer s.tx)) h1 h3 new_hash_st;

    lemma_transcript_bytes12 (G.reveal msg) (transcript s h0)

let extend_hash13 s b p0 p1 msg =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in
    let sub_b = B.sub b p0 (p1 - p0) in
    assume (Seq.length (G.reveal prev_bytes) + UInt32.v (p1 - p0) < pow2 61);

    let h0 = ST.get () in

    let new_hash_st = IncHash.update a hash_st prev_bytes sub_b (p1 - p0) in

    let h1 = ST.get () in

    B.upd s.hash_state 0ul (Some (| a, new_hash_st |));

    let e_tx = G.elift2_p extend_transcript13 e_tx msg in
    B.upd s.tx 0ul e_tx;

    let h3 = ST.get () in

    //AR: this does not have a pattern, so need to call explicitly
    IncHash.modifies_disjoint_preserves (B.loc_union (B.loc_buffer s.hash_state)
                                                     (B.loc_buffer s.tx)) h1 h3 new_hash_st;

    lemma_transcript_bytes13 (G.reveal msg) (transcript s h0)

let extract_hash #a s tag =
  let hash_st_opt = B.index s.hash_state 0ul in
  match hash_st_opt with
  | Some (| a, hash_st |) ->
    let e_tx = B.index s.tx 0ul in
    let prev_bytes = G.elift1 transcript_bytes e_tx in

    let h0 = ST.get () in
    IncHash.finish a hash_st prev_bytes tag;

    let h1 = ST.get () in

    assume (Seq.length (G.reveal prev_bytes) < Spec.Hash.Definitions.max_input_length a)
