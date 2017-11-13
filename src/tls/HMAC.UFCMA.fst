(**! Idealizing HMAC for Finished message payloads and Binders. *)
module HMAC.UFCMA

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Seq
 // for e.g. found

open Platform.Bytes
open Platform.Error
//open CoreCrypto

//open TLSConstants
open TLSError

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
//open IK 


type rgn = TLSConstants.rgn
type fresh_subregion rg parent h0 h1 = stronger_fresh_region rg h0 h1 /\ extends rg parent

type ha = Hashing.Spec.alg 
type text = bytes


noeq type info: Type0 = { 
  parent:rgn; 
  alg:ha; 
  good: text -> bool (*TODO: should be Type0 *)}

type tag (u:info) = lbytes (Hashing.Spec.tagLen u.alg)

let keylen (u:info): IK.keylen = UInt32.uint_to_t (Hashing.Spec.tagLen u.alg)
type keyrepr (u:info) = lbytes (UInt32.v (keylen u))


private type log_t
  (#ip:IK.ipkg)
  (i:ip.IK.t)
  (u:info)
  (r:rgn)
= FStar.Monotonic.Map.t r (tag u * text) (fun (t,v) -> _:unit{ip.IK.honest i ==> u.good v}) (fun _ -> True) // could constrain size

// readers and writers share the same private state: a log of MACed messages
noeq abstract type key (#ip:IK.ipkg) (i:ip.IK.t) (u:info) =
  | Key:
    #region: rgn{extends region u.parent} -> // intuitively, the writer's region
    kv: keyrepr u ->
    log: log_t i u region -> //TODO: make conditional
    key i u

val region: #ip:IK.ipkg -> #i:ip.IK.t -> #u:info -> key i u -> GTot rid
val keyval: #ip:IK.ipkg -> #i:ip.IK.t -> #u:info -> key i u -> GTot (keyrepr u)

let region #ip #i #u k  = k.region
let keyval #ip #i #u k = k.kv

private let gen (#ip:IK.ipkg) (i:ip.IK.t) (u:info) (kv:keyrepr u) : ST (key i u)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region k) u.parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region: r:rgn{extends r u.parent} = new_region u.parent in
  let log: log_t #ip i u region = FStar.Monotonic.Map.alloc #region #(tag u * text) #(fun (t,v) -> _:unit{ip.IK.honest i ==> u.good v}) #(fun _ -> True) in
  Key kv log

val create: #ip:IK.ipkg -> i:ip.IK.t -> u:info -> ST (key i u)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region k) u.parent h0 h1 ))
let create #ip i u =
  gen i u (CoreCrypto.random (UInt32.v (keylen u)))

val coerce: #ip:IK.ipkg -> i:ip.IK.t -> u:info -> kv:keyrepr u -> ST (key i u)
  (requires (fun _ -> ~(ip.IK.honest i)))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region k) u.parent h0 h1 ))
let coerce #ip i u kv = 
  gen i u kv

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (keylen u)))))

val leak: #ip:IK.ipkg -> #i:ip.IK.t -> #u:info -> k:key i u {~(ip.IK.honest i)} -> kv:keyrepr u { kv = keyval k }
let leak  #ip #i #u k = k.kv

val mac: 
  #ip:IK.ipkg -> #i:ip.IK.t -> #u:info -> k:key i u ->
  p:text { ip.IK.honest i ==> u.good p } -> ST (tag u)
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1
  //  we may be more precise, e,g,  /\ sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))


let mac #ip #i #u k p =
  //let p : p:bytes { ip.IK.honest i ==> u.good p } = p in
  let t = HMAC.hmac u.alg k.kv p in
  if None? (FStar.Monotonic.Map.lookup k.log (t,p)) then FStar.Monotonic.Map.extend k.log (t,p) ();
  t

//abstract val matches: #i:id -> #good:(bytes -> Type) -> p:text -> entry i good -> Tot bool
//let matches #i #good p (Entry _ p') = p = p'

val verify: 
  #ip:IK.ipkg -> #i:ip.IK.t -> #u:info -> k:key i u ->
  p:text -> t: tag u -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 /\ (b /\ ip.IK.honest i ==> u.good p)))

// We use the log to correct any verification errors
let verify #ip #i #u k p t =
  let verified = HMAC.hmacVerify u.alg k.kv p t in
  let maced  = Some? (FStar.Monotonic.Map.lookup k.log (t,p)) in
  verified  &&
  (not(ip.IK.honest i) || maced)


let pkg (#ip:IK.ipkg) (u:info): IK.pkg ip = IK.Pkg
  info
  key
  keylen
  create
  coerce

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

type tag (i:id) = tagr (alg i)


 
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
