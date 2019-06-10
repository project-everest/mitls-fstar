module Test.CRF 

module Hash = EverCrypt.Hash 
module B = LowStar.Buffer

let a = Spec.Hash.Definitions.SHA2_512 

open FStar.Integers
open FStar.HyperStack.ST
//open EverCrypt.Hash.Incremental
open EverCrypt.CRF

val test: unit -> ST unit 
  (requires fun h0 -> True) 
  (ensures fun h0 _ h1 -> 
    // should record modifying the ideal TLS region 
    // still requires a lemma? 
    // B.modifies B.loc_none h0 h1 /\
    True )

// Usability of EverCrypt.Hash.Incremental? See also the end of Test.Hash.fst 
//
// * tighten the handling of maxLength? refinements and ghost don't
//   mix. I would prefer a precise [hashable a <: bytes]. 
//
// * The postcondition of free seems too weak for Stack. And its
//   precondition breaks abstration.
//
// * The current incremental interface also excludes stack-based
//   allocation (not needed in mitls)
//
// * Could we make the algorithm implicit when passing the incremental
//   state? Unclear what a uniform convention would be.
//
// * I miss separate creation and initialization; we should not have
//   to maintain the invariant in-between.

// verification is dangerously slow; blame sequences? dependent maps?
#set-options "--z3rlimit 1000"
let test() =
  push_frame(); 
  let t = B.alloca 0uy (Hash.hash_len a) in  
  let x = B.alloca 1uy 11ul in  
  let s = create_in a HyperStack.root in 
  let h0 = get() in 
  let v0 = Ghost.hide #bytes Seq.empty in 
  assert_norm(11 < pow2 61); 
  let v1 = Ghost.hide #bytes (B.as_seq h0 x) in 
  finish a s v0 t; 
  let s = update a s v0 x 11ul in 
  finish a s v1 t; 
  free a s;
  pop_frame();

  assert(hashed a Seq.empty); 

  assert(hashed a (Ghost.reveal v1));
  Model.CRF.injective a v0 v1; 
  ( let v0 = Ghost.reveal v0 in 
    let v1 = Ghost.reveal v1 in 
    assert(~(Seq.equal v0 v1));
    assert(
      model /\ Model.CRF.crf a ==> 
      ~(Seq.equal (Spec.Hash.hash a v0) (Spec.Hash.hash a v1)))); 
  ()


// todo check extraction
// TODO add to CI
