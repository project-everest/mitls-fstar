(**! Idealizing HMAC for Finished message payloads and Binders. *)
module HMAC.UFCMA

open Mem
open Platform.Bytes
open Platform.Error

module MM = FStar.Monotonic.Map 

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

// FIXME
assume val ideal: bool
 
//let _ = assert false 

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type ha = Hashing.Spec.alg 
type text = bytes

noeq type info: Type0 = { 
  parent: r:rgn {~ (is_tls_rgn r)};
  alg: IK.kdfa; 
  good: text -> bool (*TODO: should be Type0 *)}

type tag (u:info) = lbytes (Hashing.Spec.tagLen u.alg)

let keylen (u:info): IK.keylen = UInt32.uint_to_t (Hashing.Spec.tagLen u.alg)
type keyrepr (u:info) = Hashing.Spec.hkey u.alg 

let ipkg = IK.ipkg  

let goodish (#ip:ipkg) (i:ip.IK.t) (u:info) (msg:text) = 
  _: unit{
  (~ ideal)\/ 
  ip.IK.corrupt i \/ 
  u.good msg}

private type log_t
  (#ip:ipkg)
  (i:ip.IK.t)
  (u:info)
  (r:rgn)
= MM.t r (tag u * text) (fun (t,v) -> goodish i u v) (fun _ -> True) // could constrain size

// readers and writers share the same private state: a log of MACed messages
noeq abstract type key (#ip:ipkg) (i:ip.IK.t) =
  | Key:
    u: info -> // creation-time parameters, kept for convenience
    region: Mem.subrgn u.parent {~(is_tls_rgn region)} ->  // intuitively, the writer's region
    kv: keyrepr u ->
    log: log_t i u region -> //TODO: make conditional
    key i 

val region: #ip:ipkg -> #i:ip.IK.t -> k:key i -> GTot (subrgn k.u.parent)
val keyval: #ip:ipkg -> #i:ip.IK.t -> k:key i -> GTot (keyrepr k.u)

let region #ip #i k  = k.region
let keyval #ip #i k = k.kv

private let gen (#ip:ipkg) (i:ip.IK.t) (u:info) (kv:keyrepr u) : ST (k:key i {k.u == u})
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region k) u.parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region: Mem.subrgn u.parent = new_region u.parent in
  assert(~(is_tls_rgn u.parent));
  let log: log_t #ip i u region = MM.alloc #_ #_ #_ #_ in 
  Key u region kv log

val create: 
  #ip:ipkg -> ha_of_i: (ip.IK.t -> ha) -> good_of_i: (ip.IK.t -> text -> bool) ->
  i:ip.IK.t {ip.IK.registered i} -> 
  u:info {u.alg = ha_of_i i /\ u.good == good_of_i i} -> ST (k:key i {k.u == u})
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    k.u == u /\
    Mem.fresh_subregion (region k) u.parent h0 h1 ))
let create #ip _ _ i u =
  let kv: keyrepr u = CoreCrypto.random (Hashing.Spec.tagLen u.alg) in
  gen i u kv 

val coerce: 
  #ip: ipkg -> ha_of_i: (ip.IK.t -> ha) -> good_of_i: (ip.IK.t -> text -> bool) ->
  i: ip.IK.t {ip.IK.registered i} -> 
  u: (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i}) ->
  kv: IK.lbytes (keylen u) -> // keyrepr u -> 
  ST (k:key i)
  (requires (fun _ -> ideal ==> ip.IK.corrupt i))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    k.u == u /\
    fresh_subregion (region k) u.parent h0 h1 ))
let coerce #ip _ _ i u kv = 
  gen i u kv

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (keylen u)))))

val footprint:
  ip: ipkg -> ha_of_i: (ip.IK.t -> ha) -> good_of_i: (ip.IK.t -> text -> bool) ->
  #i: ip.IK.t {ip.IK.registered i} -> 
  k: key i -> rset 
let footprint _ _ _ #_ k = 
  Set.singleton k.region

let pkg 
  (ip:ipkg) 
  (ha_of_i: ip.IK.t -> ha)
  (good_of_i: ip.IK.t -> text -> bool): ST (IK.pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> modifies_one tls_define_region h0 h1)
= 
  IK.memoization (IK.LocalPkg
    (key #ip)
    (fun (i:ip.IK.t) -> a:info{a.alg = ha_of_i i /\ a.good == good_of_i i})
    (fun #_ u -> keylen u ) 
    ideal  
    // local footprint 
    (fun #i (k:key i) -> Set.singleton k.region) 
    // local invariant 
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #i u h0 k h1 -> k.u == u /\ fresh_subregion (region k) u.parent h0 h1 )
    (fun #i u h0 k h1 r h2 -> ())
    (create #ip ha_of_i good_of_i)
    (coerce #ip ha_of_i good_of_i) )

val leak: 
  ip: ipkg -> ha_of_i: (ip.IK.t -> ha) -> good_of_i: (ip.IK.t -> text -> bool) ->
  #i: ip.IK.t -> 
  k: key i {ip.IK.corrupt i} -> kv:keyrepr k.u { kv = keyval k }
let leak _ _ _ #i k = k.kv

val mac: 
  #ip:ipkg -> #i:ip.IK.t -> k:key i ->
  p:text {ip.IK.corrupt i \/ k.u.good p} -> ST (tag k.u)
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
  #ip:ipkg -> #i:ip.IK.t {ip.IK.registered i} -> k:key i ->
  p:text -> t: tag k.u -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 -> 
    modifies Set.empty h0 h1 /\ 
    (b /\ ideal /\ ip.IK.honest i ==> k.u.good p)))

// We use the log to correct any verification errors
let verify #ip #i k p t =
  let verified = HMAC.hmacVerify k.u.alg k.kv p t in
  if ideal then 
    let bad = not(ip.IK.get_honesty i) in
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

let test 
  (v' t': bytes) 
  (r:rgn {~(is_tls_rgn r)}): St unit 
= 
  let ip = IK.Idx 
    nat 
    (fun _ -> True)
    (fun _ -> True)
    (fun _ -> False)
    (fun _ -> true) in
  let a = Hashing.SHA256 in
  let ha_of_i (i:nat) = a in 
  let good_of_i i v = length v = i in
  let p = pkg ip (fun _ -> a) good_of_i in
  // assume(IK.Pkg?.info p == (fun (i:ip.IK.t) -> a:info{a.alg = ha_of_i i /\ a.good == good_of_i i}));
  let u = {parent=r; alg=a; good=good_of_i 0} in
  let u: IK.Pkg?.info p 0 = u in // can't get this 
  //let u : u: info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} = {parent=r; alg=a; good=good_of_i 0} in
  //assert_norm(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == IK.Pkg?.info p 0);
  
  let k = (IK.Pkg?.create p) 0 u in
  let v = empty_bytes in
  assert(good_of_i 0 v);
  // let v: p:text {ip.IK.corrupt 0 \/ k.u.good p} = v in 
  let t = mac #ip #0 k v in
  let b = verify #ip #0 k v' t' in
  assert( b ==> length v' = 0 );
  ()
//assert( b ==> length v' = 1 );
//assert(false)


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

