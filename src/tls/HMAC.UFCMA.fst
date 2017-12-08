(**! Idealizing HMAC for Finished message payloads and Binders. *)
module HMAC.UFCMA

open Mem

open Platform.Bytes
open Platform.Error

module MM = FStar.Monotonic.Map

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

// To be moved to Flags.
let model = Flags.model
assume val ideal: b:bool{b ==> model}
let ipkg = Pkg.ipkg
type safe (#ip:ipkg) (i:ip.Pkg.t) = ideal /\ ip.Pkg.honest i

let is_safe (#ip:ipkg) (i:ip.Pkg.t{ip.Pkg.registered i})
  : ST bool (requires fun h0 -> True)
  (ensures fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
  =
  let b = ip.Pkg.get_honesty i in
  ideal && b

//let _ = assert false

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type ha = Hashing.Spec.alg
type text = bytes

noeq type info: Type0 = {
  parent: r:rgn {~ (is_tls_rgn r)};
  alg: Hashing.Spec.alg; //too loose? Pkg.kdfa;
  good: text -> bool (*TODO: should be Type0 *)}

type tag (u:info) = lbytes (Hashing.Spec.tagLen u.alg)

let keylen (u:info): Pkg.keylen = UInt32.uint_to_t (Hashing.Spec.tagLen u.alg)
type keyrepr (u:info) = Hashing.Spec.hkey u.alg

let goodish (#ip:ipkg) (i:ip.Pkg.t) (u:info) (msg:text) =
  _: unit{
  (~ ideal)\/
  ip.Pkg.corrupt i \/
  u.good msg}

private type log_t
  (#ip:ipkg)
  (i:ip.Pkg.t)
  (u:info)
  (r:rgn)
= MM.t r (tag u * text) (fun (t,v) -> goodish i u v) (fun _ -> True) // could constrain size

// The runtime (concrete) type of MAC instances
noeq abstract type concrete_key =
  | MAC: u:info -> k:keyrepr u -> concrete_key

// The model type of instances - either ideal, or real
noeq abstract type ir_key (ip:ipkg) (i:ip.Pkg.t) =
  | IdealKey:
    ck: concrete_key ->
    region: Mem.subrgn ck.u.parent {~(is_tls_rgn region)} ->  // intuitively, the writer's region
    log: log_t i ck.u region ->
    ir_key ip i
  | RealKey: ck:concrete_key -> ir_key ip i

type key (ip:ipkg) (i:ip.Pkg.t) =
  (if model then
    k:ir_key ip i{IdealKey? k <==> safe i}
  else concrete_key)

let usage (#ip:ipkg) (#i:ip.Pkg.t) (k:key ip i) : GTot info =
  if model then
    match k <: ir_key ip i with
    | IdealKey ck _ _ -> ck.u
    | RealKey ck -> ck.u
  else k.u

let keyval (#ip:ipkg) (#i:ip.Pkg.t) (k:key ip i) : GTot (keyrepr (usage k)) =
  if model then
    match k <: ir_key ip i with
    | IdealKey ck _ _ -> ck.k
    | RealKey ck -> ck.k
  else k.k

let region (#ip:ipkg) (#i:ip.Pkg.t) (k:key ip i)
  : Ghost (subrgn (usage k).parent)
  (requires safe i) (ensures fun _ -> True)
  = let IdealKey _ r _ = k <: ir_key ip i in r

let footprint (#ip:ipkg) (#i:ip.Pkg.t {ip.Pkg.registered i}) (k:key ip i) : Pkg.rset =
  if model then
    match k <: ir_key ip i with
    | IdealKey _ r _ -> assume false; Set.singleton r // FIXME downwards closed set
    | RealKey _ -> Set.empty
  else Set.empty

val create:
  ip:ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (ip.Pkg.t -> text -> bool) ->
  i:ip.Pkg.t {ip.Pkg.registered i} ->
  u:info {u.alg = ha_of_i i /\ u.good == good_of_i i} -> ST (k:key ip i)
  (requires fun _ -> model)
  (ensures fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)

let create ip _ _ i u =
  let region: Mem.subrgn u.parent = new_region u.parent in
  assert(~(is_tls_rgn u.parent));
  let log: log_t #ip i u region = MM.alloc #_ #_ #_ #_ in
  let kv: keyrepr u = CoreCrypto.random (Hashing.Spec.tagLen u.alg) in
<<<<<<< HEAD
  gen ip i u kv 

// placeholder; will require allocating the sub-region only ideally.
assume val coerceT: 
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (ip.Pkg.t -> text -> bool) ->
  i: ip.Pkg.t {ip.Pkg.registered i} -> 
  u: (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i}) ->
  kv: Pkg.lbytes (keylen u) -> 
  key ip i

val coerce: 
=======
  let ck = MAC u kv in
  let k : ir_key ip i =
    if is_safe i then
      IdealKey ck region log
    else
      RealKey ck in
  k <: key ip i

let coerceT (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: ip.Pkg.t -> text -> bool)
  (i: ip.Pkg.t {ip.Pkg.registered i}) (u: u:info {u.alg = ha_of_i i /\ u.good == good_of_i i})
  (kv: Pkg.lbytes (keylen u))
  : Ghost (key ip i) (requires ~(safe i)) (ensures fun _ -> True) =
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck

val coerce:
>>>>>>> Checkpoint
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (ip.Pkg.t -> text -> bool) ->
  i: ip.Pkg.t {ip.Pkg.registered i} ->
  u: (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i}) ->
  kv: Pkg.lbytes (keylen u) ->
  ST (k:key ip i)
<<<<<<< HEAD
  (requires (fun _ -> ideal ==> ip.Pkg.corrupt i))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    k == coerceT ip ha_of_i good_of_i i u kv /\
    k.u == u /\
    fresh_subregion (region k) u.parent h0 h1 ))
let coerce ip ha_of_i good_of_i i u kv = 
  let k = gen ip i u kv in
  assume (k == coerceT ip ha_of_i good_of_i i u kv);
  k

=======
  (requires fun _ -> ~(safe i))
  (ensures fun h0 k h1 ->
    modifies_none h0 h1 /\
    ~(safe i) /\ // annoying
    k == coerceT ip ha_of_i good_of_i i u kv /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)

let coerce ip _ _ i u kv =
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck
>>>>>>> Checkpoint

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (keylen u)))))

unfold let info1
  (ip:ipkg)
  (ha_of_i: ip.Pkg.t -> ha)
  (good_of_i: ip.Pkg.t -> text -> bool)
  (i: ip.Pkg.t): Type0
  =
  a:info{a.alg = ha_of_i i /\ a.good == good_of_i i}

unfold let localpkg
  (ip: ipkg)
  (ha_of_i: i:ip.Pkg.t -> ha)
<<<<<<< HEAD
  (good_of_i: ip.Pkg.t -> text -> bool) 
  : 
  p: Pkg.local_pkg ip {Pkg.LocalPkg?.info #ip p == info1 ip ha_of_i good_of_i}
= 
=======
  (good_of_i: ip.Pkg.t -> text -> bool)
  : p: Pkg.local_pkg ip {Pkg.LocalPkg?.info #ip p == info1 ip ha_of_i good_of_i}
  =
>>>>>>> Checkpoint
    Pkg.LocalPkg
      (fun (i:ip.Pkg.t {ip.Pkg.registered i}) -> key ip i)
      (info1 ip ha_of_i good_of_i)
      (fun #_ u -> keylen u )
      ideal
      footprint // local footprint
      (fun #_ k h -> True) // local invariant
      (fun r i h0 k h1 -> ()) // Local invariant framing
      (fun #i u k h1 -> usage k == u) // create/coerce postcondition
      (fun #i u k h1 r h2 -> ())
      (create ip ha_of_i good_of_i)
      (coerceT ip ha_of_i good_of_i)
      (coerce ip ha_of_i good_of_i)

unfold
let pkg
  (ip:ipkg)
  (ha_of_i: ip.Pkg.t -> ha)
  (good_of_i: ip.Pkg.t -> text -> bool)
  (table: Pkg.mem_table (key ip))
  : Pkg.pkg ip
//  (requires fun h0 -> True)
//  (ensures fun h0 r h1 -> modifies_one tls_define_region h0 h1)
=
  let p = localpkg ip ha_of_i good_of_i in
  //assert(p.Pkg.key == key ip);
  assert(Pkg.LocalPkg?.info #ip p == info1 ip ha_of_i good_of_i);

  let table: Pkg.mem_table p.Pkg.key = admit() in //table in
  let q = Pkg.memoization p table in
  assert(Pkg.Pkg?.key q == key ip);
  q

val leak:
  #ip: ipkg ->
  #i: ip.Pkg.t ->
  k: key ip i {ip.Pkg.corrupt i} -> kv:keyrepr k.u { kv = keyval k }
let leak #_ #_ k = k.kv

val mac:
  #ip:ipkg -> #i:ip.Pkg.t -> k:key ip i ->
  p:text {ip.Pkg.corrupt i \/ k.u.good p} -> ST (tag k.u)
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1 ))
  // we may be more precise to prove ideal functional correctness,
  // e,g,  /\ sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
let mac #ip #i k p =
  let kv: keyrepr k.u = k.kv in
  let t: tag k.u = HMAC.hmac k.u.alg kv p in
  if None? (MM.lookup k.log (t,p)) then MM.extend k.log (t,p) ();
  t

val verify:
  #ip:ipkg -> #i:ip.Pkg.t {ip.Pkg.registered i} -> k:key ip i ->
  p:text -> t: tag k.u -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    modifies Set.empty h0 h1 /\
    (b /\ ideal /\ ip.Pkg.honest i ==> k.u.good p)))

// We use the log to correct any verification errors
let verify #ip #i k p t =
  let verified = HMAC.hmacVerify k.u.alg k.kv p t in
  if ideal then
    let bad = not(ip.Pkg.get_honesty i) in
    match FStar.Monotonic.Map.lookup k.log (t,p) with
    | Some _ -> verified        (* genuine MAC *)
    | None   -> verified && bad (* forgery, blocked when ideal & honest *)
  else
    verified


/// Now entirely independent of TLS.
///
/// We'll use something of the form
///
/// let good text =
///   exists digest.
///     hashed ha digest /\
///     text = hash ha digest /\
///     witnessed (fun h -> "this is the writer's state is ...")
///
/// - how to deal with agility here?
/// - which level of abstraction?


/// TODOs:
/// - Type0/Type1
/// - how to pass key-generation-time usage parameters?
/// - how to guarantee matching goodnesses?
/// - more specific instantiations?
/// (later) support dynamic key compromise

val coerce_eq2: a: (nat -> Type0) -> b: (nat -> Type0) -> v:a 0{a == b} -> b 0
let coerce_eq2 a b v = v // this works; many similar variants did not.

module MR = FStar.Monotonic.RRef

#set-options "--initial_fuel 1 --max_fuel 3 --initial_ifuel 1 --max_ifuel 3"
open FStar.Tactics

let test
  (r:rgn {~(is_tls_rgn r)})
  (v': bytes)
  (t': Hashing.Spec.tag Hashing.SHA256)
  :
  ST unit
  (requires fun h0 -> Pkg.model)
  (ensures fun h0 _ h1 -> True)
=
  let ip = Pkg.Idx // honest, simple indexes
    nat
    (fun _ -> True)
    (fun _ -> True)
    (fun _ -> False)
    (fun _ -> true) in

  // testing usability of local packages
  let a = Hashing.SHA256 in
  let ha_of_i (i:nat) = a in
  let good_of_i i v = length v = i in // a property worth MACing!
  let p = localpkg ip ha_of_i good_of_i in
  // assert (Pkg.LocalPkg?.info #ip p == info1 ip ha_of_i good_of_i); // provable only with unfolds?

  let u = {parent=r; alg=a; good=good_of_i 0} in
  let u = coerce_eq2 (info1 ip ha_of_i good_of_i) (Pkg.LocalPkg?.info #ip p) u in
  let k0: key ip 0 = (Pkg.LocalPkg?.create p) 0 u in

  // testing usability of full packages
  let table = Pkg.mem_alloc #(i:ip.Pkg.t{ip.Pkg.registered i}) (key ip) in
  let q = pkg ip (fun (_:ip.Pkg.t) -> a) good_of_i table in

  let h0 = Mem.get() in
  // assert(
  //   let open Pkg in
  //   let log : i_mem_table p.key = itable q.define_table in
  //   let v = MR.m_sel h0 log in
  //   lemma_mm_forall_init v p.local_invariant h0;
  //   mm_forall v p.local_invariant h0);
  // assert_norm(q.Pkg.package_invariant h0);
  //if model then
  //  else True in

  assume(q.Pkg.package_invariant h0);

  //TODO superficial but hard to prove...
  // assume(Monotonic.RRef.m_sel h0 (Pkg.itable table) == MM.empty_map ip.Pkg.t (key ip));
  // assert(MM.fresh (Pkg.itable table) 0 h0);
  // assert(q.Pkg.define_table == table);
  assume(Pkg.mem_fresh q.Pkg.define_table 0 h0);

  //17-11-23  causing mysterious squash error
  // assert_by_tactic(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == Pkg.Pkg?.info q 0) FStar.Tactics.(norm "foo");
  // let u = u <: Pkg.Pkg?.info q 0 in
  let k: key ip 0 = (Pkg.Pkg?.create q) 0 u in

  // testing usability of logical payloads
  let v = empty_bytes in
  assert(good_of_i 0 v);
  let t = mac #ip #0 k v in

  let b = verify #ip #0 k v' t' in
  assert(b /\ ideal ==> length v' = 0);
  //assert false; // sanity check
  ()

(*

/// ------------ older, TLS-specific implementation

//17-10-21 ADAPT: should depend only on agility parameter.

type id =
| HMAC_Finished of TLSInfo.finishedId
| HMAC_Binder of TLSInfo.binderId

let alg (i:id) = match i with
| HMAC_Finished i -> TLSInfo.finishedId_hash i
| HMAC_Binder i -> TLSInfo.binderId_hash i

//assume
val authId: id -> Tot bool
let authId id = false // TODO: move to Flags

type tag (i:id) = tag (alg i)



// We keep the tag in case we later want to enforce tag authentication
abstract type entry (i:id) (good: bytes -> Type) =
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good


val region: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot rid
val keyval: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot (keyrepr i)

let region #i #good (k:key i good) = k.region
let keyval #i #good (k:key i good) = k.kv

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
// todo: mark it as private
private let gen0 i good (parent:rgn) kv : ST (key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region #i #good k) parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region = new_region parent in
  let log = ralloc region Seq.createEmpty in
  Key #i #good #region kv log

val gen: i:id -> good: (bytes -> Type) -> parent: rgn -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))
let gen i good parent =
  gen0 i good parent (CoreCrypto.random (keysize i))

val coerce: i:id -> good: (bytes -> Type) -> parent: rgn -> kv:keyrepr i -> ST(key i good)
  (requires (fun _ -> ~(authId i)))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))
let coerce i good parent kv =
  gen0 i good parent kv

val leak: #i:id -> #good: (bytes -> Type) -> k:key i good {~(authId i)} -> Tot (kv:keyrepr i { kv = keyval k })
let leak   #i #good k = k.kv

val mac: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes { authId i ==> good p } -> ST(tag i)
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1
  //  /\
  //  sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))


// We log every authenticated texts, with their index and resulting tag
let mac #i #good k p =
  let p : p:bytes { authId i ==> good p } = p in
  let t = HMAC.hmac (alg i) k.kv p in
  let e : entry i good = Entry t p in
  recall k.log;
  k.log := snoc !k.log e;
  t

abstract val matches: #i:id -> #good:(bytes -> Type) -> p:text -> entry i good -> Tot bool
let matches #i #good p (Entry _ p') = p = p'

val verify: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes -> t:tag i -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 /\ (b /\ authId i ==> good p)))

// We use the log to correct any verification errors
let verify #i #good k p t =
  let x = HMAC.hmacVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || Some? (seq_find (matches p) log))
*)
