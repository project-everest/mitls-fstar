(* Idealizing derived authentication tokens; independent of TLS, used for TLS 1.2 Finished message payloads. *) 
module Token.UF1CMA

//TODO use this file instead of TLSPRF

open FStar.Bytes
open Mem

// this file is adapted from HMAC.UFCMA but simpler, and yield
// probabilistic security: the advantage of an adversary guessing the
// random token is just 1/#tokens. (Do we need to enforce a single
// verification attempt?)

let ipkg = Pkg.ipkg
let model = Flags.model
let ideal = Flags.ideal_HMAC 
// secret idealization flag for the UF1CMA assumption
//TODO use a separate flag 

type safe (#ip:ipkg) (i:ip.Pkg.t) = b2t ideal /\ ip.Pkg.honest i

private let is_safe (#ip:ipkg) (i:ip.Pkg.t{ip.Pkg.registered i}): ST bool 
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
  =
  let b = ip.Pkg.get_honesty i in
  ideal && b

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

// formally agile in the KDF algorithm, which controls the token length. 
type ha = Hashing.Spec.alg

// initial parameters
noeq type info = {
  parent: r:rgn {~ (is_tls_rgn r)};
  alg: Hashing.Spec.alg; //too loose? Pkg.kdfa;
  good: bool //TODO: should be Type0 instead of bool, and erased, but hard to propagate
}

type tag (u:info) = lbytes32 (Hashing.tagLen u.alg)

let keylen (u:info): Pkg.keylen = Hashing.Spec.tagLen u.alg
type keyrepr (u:info) = Hashing.Spec.hkey u.alg

let goodish (#ip:ipkg) (i:ip.Pkg.t) (u:info) = _: unit{~(safe i) \/ u.good}

private type log_t (#ip:ipkg) (i:ip.Pkg.t) (u:info) (r:rgn) = 
  m_rref r (option (goodish #ip i u)) ssa

// runtime (concrete) type of MAC instances
noeq abstract type concrete_key =
  | MAC: u:info -> k:keyrepr u -> concrete_key

// The model type of instances - either ideal, or real
// The real and concrete version are related by the functional correctness of HMAC
noeq (* abstract *) type ir_key (ip:ipkg) (i:ip.Pkg.t) =
  | IdealKey:
    ck: concrete_key ->
    region: Mem.subrgn ck.u.parent {~(is_tls_rgn region)} ->  // intuitively, the writer's region
    log: log_t i ck.u region ->
    ir_key ip i
  | RealKey: ck:concrete_key -> ir_key ip i

type key (ip:ipkg) (i:ip.Pkg.t{ip.Pkg.registered i}) =
  (if model 
  then k:ir_key ip i{IdealKey? k <==> safe i}
  else concrete_key)

let usage (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): GTot info =
  if model then
    match k <: ir_key ip i with
    | IdealKey ck _ _ -> ck.u
    | RealKey ck -> ck.u
  else k.u

let keyval (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): GTot (keyrepr (usage k)) =
  if model then
    match k <: ir_key ip i with
    | IdealKey ck _ _ -> ck.k
    | RealKey ck -> ck.k
  else k.k

let region (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): 
  Ghost (subrgn (usage k).parent)
  (requires safe i) 
  (ensures fun _ -> True)
  = let IdealKey _ r _ = k <: ir_key ip i in r

let shared_footprint: rset = Set.empty

let footprint (#ip:ipkg) (#i:ip.Pkg.t {ip.Pkg.registered i}) (k:key ip i): 
  s:rset{s `Set.disjoint` shared_footprint}
  =
  assume false; //TODO downwards closed set
  if model then
    match k <: ir_key ip i with
    | IdealKey _ r _ -> Set.singleton r
    | RealKey _ -> Set.empty
  else Set.empty

val create:
  ip:ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (ip.Pkg.t -> bool) ->
  i:ip.Pkg.t {ip.Pkg.registered i} ->
  u:info {u.alg = ha_of_i i /\ u.good == good_of_i i} -> ST (k:key ip i)
  (requires fun _ -> model)
  (ensures fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)

let create ip _ _ i u =
  let kv: keyrepr u = CoreCrypto.random32 (Hashing.tagLen u.alg) in
  let ck = MAC u kv in
  let k : ir_key ip i =
    if is_safe i then
      let region: Mem.subrgn u.parent = new_region u.parent in
      assert(~(is_tls_rgn u.parent));
      let log: log_t #ip i u region = ralloc region None in
      IdealKey ck region log
    else
      RealKey ck in
  k <: key ip i

let coerceT (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: ip.Pkg.t -> bool)
  (i: ip.Pkg.t {ip.Pkg.registered i /\ ~(safe i)})
  (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i})
  (kv: lbytes32 (keylen u)) : GTot (key ip i)
  =
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck

val coerce:
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (ip.Pkg.t -> bool) ->
  i: ip.Pkg.t {ip.Pkg.registered i /\ ~(safe i)} ->
  u: info {u.alg = ha_of_i i /\ u.good == good_of_i i} ->
  kv: lbytes32 (keylen u) -> ST (k:key ip i)
  (requires fun _ -> True)
  (ensures fun h0 k h1 ->
    modifies_none h0 h1 /\
    k == coerceT ip ha_of_i good_of_i i u kv /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)

let coerce ip _ _ i u kv =
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (keylen u)))))

private let get_key (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i)
  : concrete_key
  =
  if model then
    match k <: ir_key ip i with
    | IdealKey rk _ _ -> rk
    | RealKey rk -> rk
  else k

val token:
  #ip:ipkg -> #i:ip.Pkg.t{ip.Pkg.registered i} -> k:key ip i ->
  ST (tag (usage k))
  (requires fun _ -> (usage k).good \/ ~(safe i))
  (ensures fun h0 t h1 -> modifies (footprint k) h0 h1)
  // we may be more precise to prove ideal functional correctness,
let token #ip #i k =
  let MAC _ t = get_key k in
  if is_safe i then
    (let IdealKey _ _ log = k <: ir_key ip i in
    log := Some ());
  t

assume val equalBytes : b1:Bytes.bytes -> b2:Bytes.bytes -> Tot (b:bool{b = (b1=b2)})

val verify:
  #ip:ipkg -> #i:ip.Pkg.t {ip.Pkg.registered i} -> k:key ip i ->
  t: tag (usage k) -> ST bool
  (requires fun _ -> True)
  (ensures fun h0 b h1 -> 
    modifies_none h0 h1 /\
    (b /\ safe i ==> (usage k).good))
let verify #ip #i k t =
  let MAC _ t' = get_key k in 
  let verified = (t = t') in
  if is_safe i then
    // We use the log to correct any verification errors
    let IdealKey _ _ log = k <: ir_key ip i in
    match !log with 
    | Some () -> verified
    | None    -> 
      assume false; //18-01-04 TODO how can this fail otherwise?
      false
  else
    verified

type info1 (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha)
  (good_of_i: ip.Pkg.t -> bool) (i: ip.Pkg.t)
  =
  a:info{a.alg = ha_of_i i /\ a.good == good_of_i i}

unfold let localpkg (ip: ipkg) (ha_of_i: (i:ip.Pkg.t -> ha)) (good_of_i: ip.Pkg.t -> bool)
  : Pure (Pkg.local_pkg ip)
  (requires True) (ensures fun p -> p.Pkg.key == key ip /\ p.Pkg.info == info1 ip ha_of_i good_of_i)
  =
  Pkg.LocalPkg
    (key ip)
    (info1 ip ha_of_i good_of_i)
    (fun #_ u -> keylen u )
    (b2t ideal)
    shared_footprint
    footprint // local footprint
    (fun #_ k h -> True) // local invariant
    (fun r i h0 k h1 -> ()) // Local invariant framing
    (fun #i u k h1 -> usage k == u) // create/coerce postcondition
    (fun #i u k h1 r h2 -> ())
    (create ip ha_of_i good_of_i)
    (coerceT ip ha_of_i good_of_i)
    (coerce ip ha_of_i good_of_i)

//TODO (later) support dynamic key compromise


(** The rest of the file is a unit test for the packaging of UFCMA *)

val coerce_eq2: a: (nat -> Type0) -> b: (nat -> Type0) -> v:a 0 -> Pure (b 0)
  (requires a == b) (ensures fun _ -> True)
let coerce_eq2 _ _ v = v // this works; many similar variants did not.

#set-options "--initial_fuel 1 --max_fuel 2 --initial_ifuel 1 --max_ifuel 2"
open FStar.Tactics

private type id = nat
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

private let test (r:rgn {~(is_tls_rgn r)}) (t': Hashing.Spec.tag Hashing.SHA256)
  : ST unit
  (requires fun h0 -> model)
  (ensures fun h0 _ h1 -> True)
  =
  // testing usability of local packages
  let a = Hashing.SHA256 in
  let ha_of_i (i:ip.Pkg.t) = a in
  let good_of_i (i:ip.Pkg.t) = true in // a property worth MACing!

  let p = localpkg ip ha_of_i good_of_i in
  let table = mem_alloc (key ip) in

  let q = Pkg.memoization p table in

  assert(Pkg.Pkg?.key q == key ip);
  assert(Pkg.Pkg?.info q == info1 ip ha_of_i good_of_i);

  let u : info1 ip ha_of_i good_of_i 0 = {parent=r; alg=a; good=good_of_i 0} in
  let u = coerce_eq2 (info1 ip ha_of_i good_of_i) (Pkg.Pkg?.info q) u in

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

  //TODO call memoization_ST instead of memoization? We miss this postcondition.
  assume(q.Pkg.package_invariant h0);

  assert(mem_fresh q.Pkg.define_table 0 h0);

  //17-11-23  causing mysterious squash error
  // assert_by_tactic(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == Pkg.Pkg?.info q 0) FStar.Tactics.(norm "foo");
  // let u = u <: Pkg.Pkg?.info q 0 in
  let k: key ip 0 = Pkg.Pkg?.create q 0 u in

  // testing usability of logical payloads
  assert(good_of_i 0);
  let t = token #ip #0 k in

  let b = verify #ip #0 k t in
  assert(b /\ b2t ideal ==> good_of_i 0);
  // assert false; // sanity check
  ()
