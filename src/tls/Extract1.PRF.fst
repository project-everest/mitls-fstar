module Extract1.PRF

open Mem
open Pkg
open Idx 
open Pkg.Tree
open KDF // avoid?

/// The "salt" is an optional secret used (exclusively) as HKDF
/// extraction key. The absence of salt (e.g. when no PSK is used) is
/// handled using a special, constant salt marked as compromised.
///
/// salt is indexed by the usage of the secret that will be extracted
/// (the usage of the salt itself is fixed).
///
/// We use separate code for salt1 and salt2 because they are
/// separately idealized (salt1 is more complicated)

let idealPRF1 (d:nat) = b2t (Flags.flag_PRF1 d)
let lemma_kdf_prf1 (d:nat) : Lemma (idealKDF d ==> idealPRF1 d) = admit()

type safePRF1 (d:nat) (i:regid) = idealPRF1 d /\ honest i

assume type salt (d:nat) (u: usage d) (i: id)

assume val create_salt:
  #d: nat ->
  #u: usage d ->
  i: id ->
  a: info ->
  salt d u i

assume val coerce_salt:
  #d: nat ->
  #u: usage d ->
  i: id ->
  a: info ->
  raw: lbytes32 (secret_len a) ->
  salt d u i

#set-options "--admit_smt_queries true" 

noextract
let local_salt_pkg (d:nat) (u:usage d) : local_pkg ii =
  LocalPkg
    (salt d u)
    (fun (i:id{registered i}) -> a:info{a == get_info i})
    (fun #_ a -> secret_len a)
    (idealPRF1 d)
    // local footprint
    (Set.empty <: rset)
    (fun #i (k:salt d u i) -> Set.empty)
    // local invariant
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #_ _ _ _ -> True) // no post-condition
    (fun #_ _ _ _ _ _ -> ())
    (create_salt #d #u)
    (magic ())
    (coerce_salt #d #u)

let saltp (d:nat) (u:usage d) : ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> True)
  =
  memoization_ST (local_salt_pkg d u)


/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-step
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.

/// two flags; we will idealize ODH first
///
type idealODH (d:nat) = b2t (Flags.flag_ODH d)
type safeODH (d:nat) (i:regid) = idealODH d /\ honest i

/// we write prf_ for the middle salt-keyed extraction, conditionally
/// idealized as a PRF keyed by salt1 depending on flag_prf1
///
/// its interface provides create, coerce, leak, and extract its
/// internal table memoizes it either with *wide* domain gZ, or with
/// *narrow* domain idh
///
/// Returns a narrow-indexed key,
///
/// its internal state ensures sharing

assume val prf_leak:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  #a: info {a == get_info i} ->
  s: salt d u i {~(safePRF1 d i)} ->
  Hashing.Spec.hkey a.ha

type ext1 (d:nat) (u:usage d) (i:regid) (idh:id_dhe) =
  _:unit{registered (Derive i "" (ExtractDH idh))} &
  secret d u (Derive i "" (ExtractDH idh))

val prf_extract1:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt d u i ->
  idh: id_dhe{~(honest_idh (ExtractDH idh))} ->
  gZ: bytes ->
  ST (ext1 d u i idh)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> True)

let prf_extract1 #d #u #i a s idh gZ =
  let j, honest' = register_derive i "" (ExtractDH idh) in
  lemma_corrupt_invariant i "" (ExtractDH idh);
  let honest = get_honesty i in
  lemma_kdf_prf1 d;
  if Flags.flag_PRF1 d && honest
  then
    // This is the narrow idealized variant--see paper for additional
    // discussion. Note the algorithm is determined by the salt index.
    //
    (| (), create d u j a |)
    //
    // We use the define table of the derived KDF to represent the
    // state of the PRF.  todo: guard [create] with a table lookup;
    // informally, when calling [prf_extract1] we don't care about the
    // state of the KDF, as long as it meets its invariant.
    //
    // The wide idealized variant is as follows:
    //
    // let j0 =
    //   match Map.find !s.wide (i,gZ) with
    //   | Some j0 -> j0
    //   | None    -> s.wide := !s.wide ++ ((i,gZ), length !s.wide) in
    // JKDF.create u j j0 a
    //
    // or just
    // JKDF.create u j (i,gZ) a
  else
    let raw_salt = prf_leak #d #u #i #a s in
    let raw = HKDF.extract raw_salt gZ in
    (| (), coerce d u j a raw |)
    // we allocate a key at a narrow index, possibly re-using key
    // materials if there are collisions on gZ or raw_salt
