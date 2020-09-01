(* Idealizing derived authentication tokens; independent of TLS, used for TLS 1.2 Finished message payloads. *)
module Token.UF1CMA

//TODO use this file instead of TLSPRF

open FStar.Bytes
open Mem
open Pkg

module M = LowStar.Modifies
module DT = DefineTable
module H = Hashing.Spec

private let is_safe (#ip:ipkg) (i:regid ip) : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
  =
  let b = ip.get_honesty i in
  ideal && b

let goodish (#ip:ipkg) (i:ip.Pkg.t) (u:info) =
  squash (safe i ==>  u.good)

// runtime (concrete) type of MAC instances
noeq
type concrete_key (#ip:ipkg) (ha_of_i: ip.t -> ha) (good_of_i: ip.t -> bool) (i:ip.t) =
  | MAC: u:info0 ha_of_i good_of_i i -> k:keyrepr u.alg -> concrete_key ha_of_i good_of_i i

private type log_t (#ip:ipkg) (i:ip.Pkg.t) (u:info) (r:rgn) =
  m_rref r (option (goodish #ip i u)) ssa

// The model type of instances - either ideal, or real
// The real and concrete version are related by the functional correctness of HMAC
noeq (* abstract *) type ir_key (#ip:ipkg)
  (ha_of_i: ip.t -> ha) (good_of_i: ip.t -> bool) (i:ip.Pkg.t) =
  | IdealKey:
    ck: concrete_key ha_of_i good_of_i i ->
    region: Mem.subrgn ck.u.parent {~(is_tls_rgn region)} ->  // intuitively, the writer's region
    log: log_t i ck.u region ->
    ir_key ha_of_i good_of_i i
  | RealKey: ck:concrete_key ha_of_i good_of_i i -> ir_key ha_of_i good_of_i i

type key (#ip:ipkg) (ha_of_i: ip.t -> ha) (good_of_i: ip.t -> bool) (i:regid ip) =
  (if model
  then k:ir_key ha_of_i good_of_i i{IdealKey? k <==> safe i}
  else concrete_key ha_of_i good_of_i i)

let usage #ip #hofi #gofi #i (k:key #ip hofi gofi i) =
  if model then
    let k' : ir_key hofi gofi i = k in
    match k' with
    | IdealKey ck _ _ -> ck.u
    | RealKey ck -> ck.u
  else (k <: concrete_key hofi gofi i).u

let keyval #ip #hofi #gofi #i (k:key #ip hofi gofi i): GTot (keyrepr (usage k).alg) =
  if model then
    let k' : ir_key hofi gofi i = k in
    match k' with
    | IdealKey ck _ _ -> ck.k
    | RealKey ck -> ck.k
  else (k <: concrete_key hofi gofi i).k

let footprint #ip #hofi #gofi : DT.local_fp (key #ip hofi gofi)
  = fun #i k ->
  if model then
    let k' : ir_key hofi gofi i = k in
    match k' with
    | IdealKey _ r _ -> M.loc_region_only true r
    | RealKey _ -> M.loc_none
  else M.loc_none

let create #ip hofi gofi i u =
  assume false;
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let kv: keyrepr u.alg = Random.sample32 (Hacl.Hash.Definitions.hash_len u.alg) in
  let ck = MAC u kv in
  let k : ir_key hofi gofi i =
    if is_safe i then
      let region: Mem.subrgn u.parent = new_region u.parent in
      let log: log_t #ip i u region = ralloc region None in
      IdealKey ck region log
    else
      RealKey ck in
  k <: key hofi gofi i

let coerceT (#ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: ip.Pkg.t -> bool)
  (i: regid ip{~(safe i)}) (u: info0 ha_of_i good_of_i i)
  (kv: lbytes32 (uf1cma_keylen u.alg)) : GTot (key ha_of_i good_of_i i)
  =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let ck = MAC u kv in
  if model then
    let k : ir_key ha_of_i good_of_i i = RealKey ck in k
  else ck

let coerce #ip hofi gofi i u kv =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let ck = MAC u kv in
  if model then
    let k : ir_key hofi gofi i = RealKey ck in k
  else ck

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (uf1cma_keylen u)))))

private let get_key #ip #hofi #gofi #i (k:key #ip hofi gofi i)
  : concrete_key hofi gofi i
  =
  if model then
    let k' : ir_key hofi gofi i = k in
    match k' with
    | IdealKey rk _ _ -> rk
    | RealKey rk -> rk
  else k

// we may be more precise to prove ideal functional correctness,
let token #ip #hofi #gofi #i k =
  let MAC _ t = get_key k in
  if is_safe i then
    (let IdealKey _ _ log = k <: ir_key hofi gofi i in
    log := Some ());
  t

let verify #ip #hofi #gofi #i k t =
  let MAC _ t' = get_key k in
  let verified = (t = t') in
  if is_safe i then
    // We use the log to correct any verification errors
    let IdealKey _ _ log = k <: ir_key hofi gofi i in
    match !log with
    | Some () -> verified
    | None    ->
      assume false; //18-01-04 TODO how can this fail otherwise?
      false
  else
    verified

//TODO (later) support dynamic key compromise


(** The rest of the file is a unit test for the packaging of UFCMA *)

val coerce_eq2: a: (nat -> Type0) -> b: (nat -> Type0) -> v:a 0 -> Pure (b 0)
  (requires a == b) (ensures fun _ -> True)
let coerce_eq2 _ _ v = v // this works; many similar variants did not.

#set-options "--initial_fuel 1 --max_fuel 2 --initial_ifuel 1 --max_ifuel 2"
open FStar.Tactics

private type id = nat
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

private let test (r:rgn {~(is_tls_rgn r)}) (t': Hashing.Spec.tag Hashing.SHA2_256)
  : ST unit
  (requires fun h0 -> model)
  (ensures fun h0 _ h1 -> True)
  =
  // testing usability of local packages
  let a:ha  = Hashing.SHA2_256 in
  let ha_of_i (i:ip.Pkg.t) = a in
  let good_of_i (i:ip.Pkg.t) = true in // a property worth MACing!

  let p = localpkg ip ha_of_i good_of_i in
  let q = Pkg.memoization_ST p in

  let h0 = Mem.get() in
  // assert(
  //   let open Pkg in
  //   let log : i_mem_table p.key = itable q.define_table in
  //   let v = HS.sel h0 log in
  //   lemma_mm_forall_init v p.local_invariant h0;
  //   mm_forall v p.local_invariant h0);
  // assert_norm(q.Pkg.package_invariant h0);
  //if model then
  //  else True in
//  assume(False);
  //TODO call memoization_ST instead of memoization? We miss this postcondition.
//  assume(q.Pkg.package_invariant h0);

  //17-11-23  causing mysterious squash error
  // assert_by_tactic(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == Pkg.Pkg?.info q 0) FStar.Tactics.(norm "foo");
  // let u = u <: Pkg.Pkg?.info q 0 in
  let i0 : ip.t = 0 in
  let a0 : info0 ha_of_i good_of_i i0 = Info r a (good_of_i 0) in
  assume(DT.fresh q.define_table 0 h0);
  let k : key ha_of_i good_of_i i0 = Pkg.Pkg?.create q i0 a0 in

  // testing usability of logical payloads
  assert(good_of_i 0);
  let t = token k in

  let b = verify k t in
  assert(b /\ b2t ideal ==> good_of_i 0);
  // assert false; // sanity check
  ()
