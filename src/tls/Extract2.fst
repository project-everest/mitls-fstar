module Extract2 

open Mem
open Pkg
open Idx 
open Pkg.Tree
open KDF // avoid?

open Extract0 // for now

/// ---------------- final (useless) extraction --------------------

assume val flag_KEF2: d:nat -> b:bool{flag_KDF d ==> b /\ b ==> model}
type idealKEF2 d = b2t (flag_KEF2 d)
type safeKEF2 d i = idealKEF2 d /\ honest i

type salt2 (d:nat) (u: usage d) (i:regid) =
  ir_key (safeKEF2 d) (mref_secret d u i) (real_secret i) i

// same code as for PSKs; but extract0 and extract2 differ concretely

let real_salt2 (#d:nat) (#u: usage d) (#i:regid) (t: real_secret i{~(safeKEF2 d i)}) : salt2 d u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF2 d i <==> Ideal? s} = Real t in s)
  else t

let salt2_real (#d:nat) (#u: usage d) (#i:regid) (p:salt2 d u i {~(safeKEF2 d i)}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF2 d i <==> Ideal? s} = p in
    Real?.v t
  else p

type ext2 (d:nat) (u:usage d) (i:id{registered i}) =
  _:unit{registered (Derive i "" Extract)} & salt2 d u (Derive i "" Extract)

val coerce_salt2:
  #d: nat ->
  #u: usage d ->
  i: id {registered i /\ ~(safeKEF2 d i)} ->
  a: info {a == get_info i} ->
  raw: lbytes32 (secret_len a) ->
  ST (ext2 d u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> True)

#set-options "--admit_smt_queries true" //17-12-08 

let coerce_salt2 #d #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_salt2 #d #u #i' raw |)

let ideal_salt2 (#d:nat) (#u:usage d) (#i:regid) (t: mref_secret d u i{safeKEF2 d i}) : salt2 d u i =
  let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF2 d i <==> Ideal? s} = Ideal t in
  assert(model); t

let salt2_ideal (#d:nat) (#u:usage d) (#i:regid) (p:salt2 d u i {safeKEF2 d i}): mref_secret d u i =
  let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF2 d i <==> Ideal? s} = p in
  Ideal?.v t

val create_salt2:
  #d: nat ->
  #u: usage d ->
  i: id {registered i} ->
  a: info {a == get_info i} ->
  ST (ext2 d u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> True)

let create_salt2 #d #u i a =
  let i', honest' = register_derive i "" Extract in
  let honest = get_honesty i in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF2 d && honest' then
    let t' = secret d u i' in
    let r: mref_secret d u i' = ralloc #(option t') #(ssa #t') there None in
    (| (), ideal_salt2 #d #u #i' r |)
  else
    (| (), real_salt2 #d #u #i' (sample (secret_len a)) |)

let saltp2 (d:nat) (u:usage d): ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> True)
  =
  let p = LocalPkg
    (fun (i:id{registered i}) -> ext2 d u i)
    (fun (i:id) -> a:info{a == get_info i})
    (fun #_ a -> secret_len a)
    (idealKEF2 d)
    // local footprint
    (Set.empty <: rset)
    (fun #i (k:ext2 d u i) -> Set.empty)
    // local invariant
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #_ _ _ _ -> True) // no post-condition
    (fun #_ _ _ _ _ _ -> ())
    (create_salt2 #d #u)
    (magic())
    (coerce_salt2 #d #u) in
  memoization_ST p


/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
/// The salt is used just for extraction, hence [u] here is for the extractee.
/// Otherwise the code is similar to [derive], with different concrete details
val extract2:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  s: ext2 d u i ->
  a: info {a == get_info i} ->
  ST (secret d u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract2 #d #u #i e2 a =
  let (| _, s |) = e2 in
  let i' : regid = Derive i "" Extract in
  let honest' = get_honesty i' in
  assert(wellformed_id i');
  assert(a = get_info i');
  assume(idealKDF d ==> idealKEF2 d); // TODO
  if flag_KEF2 d && honest' then
    let k: mref_secret d u i' = salt2_ideal s in
    match !k with
    | Some extract -> extract
    | None ->
        let extract = create d u i' a in
        let mrel = ssa #(secret d u i') in
        let () =
          recall k;
          let h = get() in
          assume (sel h k == None); // TODO framing of call to create
          assume (mrel None (Some extract)); // TODO Fix the monotonic relation
          k := Some extract in
        extract
  else
    let k = salt2_real s in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
    coerce d u i' a raw

