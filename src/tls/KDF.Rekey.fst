module KDF.Rekey

open Mem
open Pkg
open Idx
open Pkg.Tree
//open KDF
//open IV

//include AEAD.Pkg
//include KDF

/// This file illustrates our use of indexes, packages, and KDF on a
/// simple recursive subset of the TLS key-schedule: late rekeying. It
/// also provides a standalone test for verification and extraction.

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("RKY| "^s^"\n"))

(*
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
*)

//let test_rekey(): St C.exit_code = C.EXIT_SUCCESS

inline_for_extraction noextract
let ivlen (i:id) : keylen = EverCrypt.Hash.tagLen Hashing.Spec.SHA256

let is_iv_p (p:pkg ii) =
  Pkg?.key p == IV.raw ii ivlen /\
  p == memoization (IV.local_raw_pkg ii ivlen) (p.define_table)

assume noextract val flagKDF': d:nat -> b:KDF.iflag{d=0 ==> b = false}
inline_for_extraction noextract let flagKDF d = if model then flagKDF' d else false
noextract let idealKDF d = b2t (flagKDF d)

assume noextract val lemma_KDF_depth: d:nat -> Lemma
  (idealKDF d == b2t (flagKDF d) /\ (match d with 0 -> idealKDF 0 == False | d -> idealKDF d ==> idealKDF (d+1)))

type is_kdf_p (p:pkg ii) (#ideal:KDF.iflag) (u:KDF.usage ideal) =
  Pkg?.key p == KDF.secret u /\
  p == memoization (KDF.local_kdf_pkg ideal u) p.define_table

private noextract let _mchildren (f:KDF.iflag) (#p:Type0) (c:children' p)
  : Pure (KDF.usage f)
  (requires model /\ b2t f == p) (ensures fun _ -> True) = c

#set-options "--z3rlimit 30"
noextract
let rec is_rekey_tree' (n:nat) (x:tree' (idealKDF (n+1)))
  : Pure Type0 (requires model) (ensures fun _ -> True) (decreases n) =
  lemma_KDF_depth n;
  if n = 0 then
    match x with
    | Node p [] ->
      Pkg?.ideal p == idealKDF 0 /\
      is_kdf_p p (_mchildren false (Node?.children x))
    | _ -> False
  else
    match x with
    | Node p ["IV", Leaf iv; "RE", re ] ->
      Pkg?.ideal p == idealKDF n /\
      is_kdf_p p (_mchildren (flagKDF n) (Node?.children x)) /\
      is_iv_p iv /\
      is_rekey_tree' (n-1) re
    | _ -> False
#reset-options

inline_for_extraction
let is_rekey_tree (n:nat) (x:tree (idealKDF (n+1))) =
  if model then is_rekey_tree' n (KDF.itree x)
  else True

noextract
val mk_rekey' (n:nat)
  : ST (tree' (idealKDF (n+1)))
  (requires fun h0 -> model)
  (ensures fun h0 x h1 ->
    is_rekey_tree' n x
    //tree_invariant x h1
  ) (decreases n)

private noextract
let lift_children' (#p:Type0) (u:children' p)
  : Pure (children p) (requires model) (ensures fun u' -> u' == u) = u

#set-options "--z3rlimit 30"
noextract
let rec mk_rekey' n =
  lemma_KDF_depth n;
  if n = 0 then (
    let u : children False = lift_children' [] in
    let p = memoization_ST (KDF.local_kdf_pkg (flagKDF 0) u) in
    Node p u
  ) else (
    let re : tree' (idealKDF n) = mk_rekey' (n-1) in
    let iv = memoization_ST (IV.local_raw_pkg ii ivlen) in
    assume(b2t Flags.flag_Raw ==> idealKDF n);
    let iv_leaf : tree' (idealKDF n) = Leaf iv in
    let u : children (idealKDF n) = lift_children' ["IV", iv_leaf; "RE",re] in
    let p = memoization_ST (KDF.local_kdf_pkg (flagKDF n) u) in
    Node p u
  )

inline_for_extraction noextract
let mk_rekey (n:nat)
  : ST (tree (idealKDF (n+1)))
  (requires fun h0 -> True)
  (ensures fun h0 t h1 ->
    is_rekey_tree n t /\
    KDF.tree_invariant t h1)
  =
  if model then
    let t' = mk_rekey' n in
    let h = get () in
    let _ = assume(KDF.tree_invariant' t' h) in
    t'
  else erased_tree

noextract inline_for_extraction let _cpkg (l:label) =
  if l = "RE" then
     [@inline_let] let u : KDF.usage false =
       if model then _mchildren false #False []
       else erased_tree in
     KDF.local_kdf_pkg false u
  else IV.local_raw_pkg ii ivlen

noextract inline_for_extraction let
concrete_pkg (#n:nat) (t:tree (idealKDF (n+1)){is_rekey_tree n t}) (l:label) =
  if model then
    [@inline_let] let t' : tree' (idealKDF (n+1)) = t in
    assert(is_rekey_tree' n t);
    [@inline_let] let Node p u = t' in
    if has_lbl #(idealKDF n) u l then
      match l with
      | "RE" -> KDF.local_kdf_pkg (flagKDF n) u
      | "IV" -> IV.local_raw_pkg ii ivlen
    else _cpkg l
  else
    _cpkg l

inline_for_extraction noextract
let fake_kdf (n:nat) (t:tree (idealKDF (n+1)){is_rekey_tree n t})
  (i:regid) (a:KDF.info0 i) (k:lbytes32 (KDF.secret_len a))
  : ST (KDF.secret #(flagKDF n)
   (if model then let t':tree' (idealKDF (n+1)) = t in
   Node?.children t' else erased_tree) i)
   (requires fun h0 -> True)
   (ensures fun h0 s h1 -> h0 == h1 /\ KDF.local_kdf_invariant s h1)
  = assume false;
  if model then
    [@inline_let] let t':tree' (idealKDF (n+1)) = t in
    [@inline_let] let Node p u = t' in
    (Pkg?.coerce p) i a k
  else KDF.coerce #(flagKDF n) erased_tree i a k

inline_for_extraction noextract
let _down (#n:nat{n>0}) (t:tree (idealKDF (n+1)){is_rekey_tree n t})
  : t':tree (idealKDF n){is_rekey_tree (n-1) t'}
  =
  if model then magic() else erased_tree

//#set-options "--z3rlimit 200"
#set-options "--admit_smt_queries true"
let test_rekey(): St C.exit_code
=
  let t2 = mk_rekey 2 in
  let h0 = get() in

  let i2:regid = if model then magic() else unit in
  let a2 : KDF.info0 i2 = KDF.Info Hashing.Spec.SHA256 None in
  let kdf2 = fake_kdf 2 t2 i2 a2 (Random.sample32 32ul) in

  let i1 = derive i2 "RE" Expand in
  let a1 : KDF.info0 i1 = KDF.Info Hashing.Spec.SHA256 None in
  [@inline_let] let cpkg' = concrete_pkg t2 "RE" in
  let (| (), kdf1 |) = KDF.derive #(flagKDF 3) #t2 #i2 kdf2 "RE" Expand cpkg' a1 in
  let t1 = _down t2 in

  let i1' = derive i2 "IV" Expand in
  let a1' = ivlen i1' in
  [@inline_let] let cpkg' = concrete_pkg t2 "IV" in
  let (| (), iv1 |) = KDF.derive #(flagKDF 2) #t #i2 kdf2 "IV" Expand cpkg' a1' in
  print ("IV1: "^(Bytes.hex_of_bytes iv1));

  let i0 = derive i1 "RE" Expand in
  let a0  : KDF.info0 i0 = KDF.Info Hashing.Spec.SHA256 None in
  [@inline_let] let cpkg' = concrete_pkg #1 t1 "RE" in
  let (| (), kdf0 |) = KDF.derive #(flagKDF 1) #t1 #i1 kdf1 "RE" Expand cpkg' a0 in

  let i0' = derive i1 "IV" Expand in
  let a0' = ivlen i0' in
  [@inline_let] let cpkg' = concrete_pkg #1 t1 "IV" in
  let (| (), iv0 |) = KDF.derive #(flagKDF 1) #t1 #i1 kdf1 "IV" Expand cpkg' a0' in
  print ("IV0: "^(Bytes.hex_of_bytes iv0));
  
  C.EXIT_SUCCESS

(*
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
*)

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
