module KDF.Rekey

open Mem
open Pkg
open Idx
open Pkg.Tree

include AEAD.Pkg
include KDF

/// This file illustrates our use of indexes, packages, and KDF on a
/// simple recursive subset of the TLS key-schedule: late rekeying. It
/// also provides a standalone test for verification and extraction.

//17-11-15 for testing; rename to aeadAlg_of_id ?
assume val get_aeadAlg: i:id -> aeadAlg
let derive_aea
  (lbl:label) (i:id)
  (a:info{wellformed_id (Derive i lbl Expand)}):
  (a':aeadAlg{a' == get_aeadAlg (Derive i lbl Expand)})
=
  //fixme! should be extracted from a
  get_aeadAlg (Derive i lbl Expand)

let is_ae_p (p: pkg ii) =
//  let ioi = get_aeadAlg in
  let (ioi:pkg ii -> Crypto.Indexing.id) = magic() in
  let q = local_ae_pkg ii get_aeadAlg ioi in
  Pkg?.key p == key ii ioi /\ p == memoization q p.define_table
let is_kdf_p (p: pkg ii) d children = // same as ksd_subtree
  Pkg?.key p == secret d children /\ p == memoization (local_kdf_pkg d children) p.define_table

// this function should specify enough to call key derivations.
let rec is_secret (n:nat) (x:tree (idealKDF n)) =
  if n = 0 then
    match x with
    | Node p [] -> is_kdf_p p 0 []
    | _ -> False
  else
    match x with
    | Node p ["AE",Leaf ae; "RE",re ] ->
      lemma_KDF_depth n;
      is_kdf_p p n ["AE",Leaf ae; "RE", re] /\
      is_ae_p ae /\ is_secret (n-1) re
    | _ -> False

// let is_secret_shape (n:nat) (x:tree {is_secret n x}): Lemma (Node? x) =
//   if n = 0 then () else ()


assume val mk_kdf: d:nat -> u:usage d -> ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> is_kdf_p p d u)

// this function allocates all tables and (WIP) sets up the initial invariant.
val mk_secret (n:nat): ST (tree (idealKDF n))
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    is_secret n x /\
    True // tree_invariant x h1 // requires finer posts for mp pp etc
    )

let rec mk_secret n =
  if n = 0 then (
    assume(valid_children (idealKDF 0) []);
    let c : usage 0 = [] in
    let p = mk_kdf 0 c in
    Node p c
  ) else (
    let ioi = magic() in
    let ae = mp ii get_aeadAlg ioi in
    assume(is_ae_p ae);// should be in the post of mp.
    lemma_KDF_depth n;
    let re = mk_secret (n-1) in
    assert(is_secret (n-1) re);
    let children = [ "AE",Leaf ae; "RE",re ] in
    assume(valid_children (idealKDF n) children);
    let p = mk_kdf n children in
    assert(is_kdf_p p n [ "AE",Leaf ae; "RE",re ]);
    Node p children)

//#set-options "--z3rlimit 200"
#set-options "--admit_smt_queries true"
let test_rekey(): St unit
=
  let x0 = mk_secret 10 in
  let h0 = get() in
  assert(is_secret 10 x0);
  assume(tree_invariant x0 h0); // soon a post of mk_secret

  match x0 with
  | Node pkg0 ["AE",Leaf aepkg1; "RE",x1 ] -> (
    let children0 : usage 10 = ["AE",Leaf aepkg1; "RE",x1 ] in
    assert(u_of_t (x0 <: kdf_subtree 10) == children0);

    let a0 = Info Hashing.Spec.SHA1 None in
    let i0: i:id {registered i /\ a0 = get_info i} = magic() in
    assert(is_kdf_p pkg0 10 children0);

    assert(pkg0.package_invariant h0 /\ tree_invariant x1 h0);
    // create's pre; should follow from pkg0's package invariant
    assume(model /\ mem_fresh pkg0.define_table i0 h0);
    assert(Pkg?.key pkg0 == secret 10 children0);

    let s0: secret 10 children0 i0 = (Pkg?.create pkg0) i0 a0 in

    assert(is_secret 9 x1);

    match x1 with
    | Node pkg1 ["AE",Leaf aepkg2; "RE",x2] -> (
      let children1 : usage 9 = ["AE",Leaf aepkg2; "RE",x2 ] in
      let a1 = Info Hashing.Spec.SHA1 None in
      let h1 = get() in

      assume(tree_invariant x0 h0 ==> tree_invariant x0 h1); // tree_invariant_frame

      let (|_,s1|) = derive #10 #(x0 <: kdf_subtree 10) s0 a0 "RE" Expand a1 in
      let i1: regid = Derive i0 "RE" Expand in

      let s1: secret 9 children1 i1 = s1 in
      let aea = derive_aea "AE" i1 a1 in
      let h2 = get() in

      assume(tree_invariant x1 h2);

      let (|_,k1|) = derive #9 #(x1 <: kdf_subtree 9) s1 a1 "AE" Expand aea in
      let ik1: regid = Derive i1 "AE" Expand in
      let ioi = magic() in
      let k1: key ii ioi ik1 = k1 in
      let h3 = get() in
      //assume(aead_inv k1 h3); // should follow from the multi-pkg invariant

      let cipher = encrypt ii get_aeadAlg ioi k1 42 in

      // assert(tree_invariant x1);
      // assert(tree_invariant x0);
      () ))
//    | _ -> assert false) // excluded by is_secret 9
//  |  _ -> assert false // excluded by is_secret 10
// refactoring needed, e.g. define derive_secret helper function to hide access to the tree

(*
let modifies_instance
  (i: id {wellformed_id i})
  (p: localpkg ii)
  (k: key i)
  (h0 h1: mem)
  (modifies_local: modifies (p.local_footprint k) h0 h1)
  (inv0: inv_node u h0):
  Lemma (inv_node u h1) =

let rec step u j i =

// from the post of a key derivation, we should have our framing lemma.

let rec descend u j i = // j decreases
  j = i \/
  match j with
  | Derive j0 lbl ctx -> derived j0 i
  | Preshared -> False

  match j, i with
  | Preshared

  i = j \/
  exists (lbl, ctx). derived (Derive i lbl ctx)
*)
