module Extract0

open Mem
open Pkg
open Idx 
open Pkg.Tree
open KDF // avoid?


/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

assume val flag_KEF0: d:nat -> b:bool{b ==> model /\ flag_KDF d ==> b}
type idealKEF0 d = b2t (flag_KEF0 d)
// to be refined. When exactly do we switch KEF0? (after KDF0?)
assume val lemma_kdf_kef0: d:nat -> Lemma (idealKDF d ==> idealKEF0 d)

let safeKEF0 (d:nat) (i:regid) = idealKEF0 d /\ honest i

/// key-derivation table (memoizing create/coerce)


// temporary
let there = Mem.tls_tables_region

// memoizing a single extracted secret
// not [private] anymore because of its reuse in Extract2.
type mref_secret (d:nat) (u: usage d) (i: regid) =
  // would prefer: HyperStack.mref (option (secret u i)) (ssa #(secret u i))
  m_rref there (option (secret d u i)) ssa

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
type psk (d:nat) (u: usage d) (i: (Idx?.t ii) {ii.registered i}) =
  ir_key (safeKEF0 d) (mref_secret d u i) (real_secret i) i

let psk_ideal (#d:nat) (#u: usage d) (#i:regid) (p:psk d u i {safeKEF0 d i}): mref_secret d u i =
  let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF0 d i <==> Ideal? s} = p in
  Ideal?.v t

let ideal_psk (#d:nat) (#u: usage d) (#i:regid) (t: mref_secret d u i{safeKEF0 d i}) : psk d u i =
  let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF0 d i <==> Ideal? s} = Ideal t in
  assert(model); t

let psk_real (#d:nat) (#u: usage d) (#i:regid) (p:psk d u i {~(safeKEF0 d i)}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF0 d i <==> Ideal? s} = p in
    Real?.v t
  else p

let real_psk (#d:nat) (#u: usage d) (#i:regid) (t: real_secret i{~(safeKEF0 d i)}) : psk d u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret d u i) (real_secret i) {safeKEF0 d i <==> Ideal? s} = Real t in s)
  else t

type ext0 (d:nat) (u:usage d) (i:id {registered i}) =
  _:unit{registered (Derive i "" Extract)} & psk d u (Derive i "" Extract)

#set-options "--lax" //17-12-08 until KDF converges


val coerceT_psk:
  #d: nat ->
  #u: usage d ->
  i: id {registered i /\ ~(safeKEF0 d i)} ->
  a: info {a == get_info i} ->
  raw: lbytes32 (secret_len a) ->
  GTot (ext0 d u i)
let coerceT_psk #d #u i a raw =
  real_psk #d #u #(Derive i "" Extract) raw

val coerce_psk:
  #d: nat ->
  #u: usage d ->
  i: id {registered i /\ ~(safeKEF0 d i)} ->
  a: info {a == get_info i} ->
  raw: lbytes32 (secret_len a) ->
  ST (ext0 d u i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> k == coerceT_psk #d #u i a raw)

let coerce_psk #d #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_psk #d #u #i' raw |)

val create_psk:
  #d: nat ->
  #u: usage d ->
  i: id {registered i} ->
  a: info {a == get_info i} ->
  ST (ext0 d u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)

let create_psk #d #u i a =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF0 d && honest' then
    let t' = secret d u i' in
    let r: mref_secret d u i' = ralloc #(option t') #(ssa #t') there None in
    (| (), ideal_psk #d #u #i' r |)
  else
    (| (), real_psk #d #u #i' (sample (secret_len a)) |)

let local_ext0_pkg (d:nat) (u:usage d) : local_pkg ii =
  LocalPkg
    (fun (i:id{registered i}) -> ext0 d u i)
    (fun i -> a: info{a == get_info i})
    (fun #_ a -> secret_len a)
    (idealKEF0 d)
    (Set.empty <: rset)
    (fun #i (k:ext0 d u i) -> Set.empty)
    // local invariant
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #_ _ _ _ -> True) // no post-condition
    (fun #_ _ _ _ _ _ -> ())
    (create_psk #d #u)
    (coerceT_psk #d #u)
    (coerce_psk #d #u)

let pskp (d:nat) (u:usage d): ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
  =
  memoization_ST (local_ext0_pkg d u)

/// HKDF.Extract(key=0, materials=k) idealized as a (single-use) PRF,
/// possibly customized on the distribution of k.
val extract0:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  k: ext0 d u i ->
  a: info {a == get_info i} ->
  ST
    (secret d u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract0 #d #u #i k a =
  let (| _, p |) = k in
  let i':regid = Derive i "" Extract in
  let honest' = get_honesty i' in
  lemma_kdf_kef0 d;
  if flag_KEF0 d && honest'
  then
    let k: mref_secret d u i' = psk_ideal p in
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
    let k = psk_real p in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
    coerce d u i' a raw
