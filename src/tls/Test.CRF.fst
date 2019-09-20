module Test.CRF

module Hash = EverCrypt.Hash
module B = LowStar.Buffer

let a = Spec.Hash.Definitions.SHA2_512

open FStar.Integers
open FStar.HyperStack.ST
//open EverCrypt.Hash.Incremental
open Crypto.CRF

val test: unit -> ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->
    // should record modifying the ideal TLS region
    // still requires a lemma?
    // B.modifies B.loc_none h0 h1 /\
    True )

// Usability of EverCrypt.Hash.Incremental? See also the end of Test.Hash.fst
//
// * The postcondition of free seems too weak for Stack. And its
//   precondition breaks abstration.
//
// * The current incremental interface also excludes stack-based
//   allocation (not needed in mitls)
//
// * Could we make the algorithm implicit when passing the incremental
//   state? Unclear what a uniform convention would be.

// verification is dangerously slow; blame sequences? dependent maps?
#set-options "--max_fuel 0 --max_ifuel 0"
let test() =
  push_frame();
  let t = B.alloca 0uy (Hacl.Hash.Definitions.hash_len a) in
  let x = B.alloca 1uy 11ul in
  let s = create_in a HyperStack.root in
  let h0 = get() in

  (**) let v0 = Ghost.hide (Seq.empty) in
  (* Note: leave the append in place otherwise reasoning about sequence
     concatenation sends verification times off the charts! *)
  (**) let v1 = Ghost.hide (Seq.empty `Seq.append` (B.as_seq h0 x)) in

  (**) assert_norm(11 < pow2 61);
  (**) assert (B.live h0 t);

  finish (Ghost.hide a) s t;
  (**) let h1 = get () in
  (**) assert B.(loc_disjoint (loc_buffer t) (footprint h1 s));
  (**) assert (hashed h1 s `Seq.equal` (Ghost.reveal v0));

  (*  How to figure out this lemma? I just asked TR! *)
  (**) B.(modifies_liveness_insensitive_buffer
    (footprint h0 s `loc_union` (loc_region_only true Mem.tls_tables_region))
    (B.loc_buffer t) h0 h1 t);
  (**) assert (B.live h1 t);

  update (Ghost.hide a) s x 11ul;
  (**) let h2 = get () in
  (**) assert B.(modifies (footprint h1 s) h1 h2);
  (**) assert (B.live h2 t);
  (**) assert (hashed h2 s `Seq.equal` (Ghost.reveal v1));

  finish (Ghost.hide a) s t;
  free (Ghost.hide a) s;
  pop_frame();

  Model.CRF.injective a v0 v1;
  ( let v0 = Ghost.reveal v0 in
    let v1 = Ghost.reveal v1 in
    assert(~(Seq.equal v0 v1));
    assert(
      model /\ Model.CRF.crf a ==>
      ~(Seq.equal (Spec.Agile.Hash.hash a v0) (Spec.Agile.Hash.hash a v1))));
  ()


// todo check extraction
// TODO add to CI
