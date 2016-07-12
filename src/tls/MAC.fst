module MAC

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found

open Platform.Bytes
open Platform.Error
open CoreCrypto 

open TLSConstants
open TLSInfo
open TLSError

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

type id = i:id { is_ID12 i /\ (let ae = aeAlg_of_id i in is_MACOnly ae \/ is_MtE ae) }

let alg (i:id) = macAlg_of_id i

type text = bytes
type tag (i:id) = lbytes (macSize (alg i))
type keyrepr (i:id) = bytes


type fresh_subregion rg parent h0 h1 = fresh_region rg h0 h1 /\ extends rg parent

// We keep the tag in case we later want to enforce tag authentication
abstract type entry (i:id) (good: bytes -> Type) = 
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good

// readers and writers share the same private state: a log of MACed messages
// TODO make it abstract
noeq type key (i:id) (good: bytes -> Type) = 
  | Key: #region : rid -> // intuitively, the writer's region
         kv      : keyrepr i ->
         log     : rref region (seq (entry i good)) -> key i good

val region: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot rid
val keyval: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot (keyrepr i)
        
let region #i #good (k:key i good) = k.region
let keyval #i #good (k:key i good) = k.kv 

val gen: i:id -> good: (bytes -> Type) -> parent: rid -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->  
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 )) 

val coerce: i:id -> good: (bytes -> Type) -> parent: rid -> kv:keyrepr i -> ST(key i good)
  (requires (fun _ -> ~(authId i)))
  (ensures (fun h0 k h1 ->  
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 )) 

val leak: #i:id -> #good: (bytes -> Type) -> k:key i good {~(authId i)} -> Tot (kv:keyrepr i { kv = keyval k })

// todo: mark it as private
private let gen0 i good parent kv = 
  let region = new_region parent in 
  let log = ralloc region Seq.createEmpty in 
  Key #i #good #region kv log

let gen    i good parent    = gen0 i good parent (CoreCrypto.random (macKeySize (alg i)))
let coerce i good parent kv = gen0 i good parent kv
let leak   #i #good k = k.kv

val mac: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes { authId i ==> good p } -> ST(tag i) 
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> 
    modifies (Set.singleton (region k)) h0 h1 
  //  /\ 
  //  sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))


// We log every authenticated texts, with their index and resulting tag
let mac #i #good k p =
  assume (HMAC.is_tls_mac (alg i));
  let p : p:bytes { authId i ==> good p } = p in
  let t = HMAC.tls_mac (alg i) k.kv p in
  let e : entry i good = Entry t p in
  k.log := snoc !k.log e;
  t

abstract val matches: #i:id -> #good:(bytes -> Type) -> p:text -> entry i good -> Tot bool 
let matches #i #good p (Entry _ p') = p = p'

val verify: #i:id -> #good:(bytes -> Type) -> k:key i good{HMAC.is_tls_mac (alg i)} -> p:bytes -> t:tag i -> ST bool
  (requires (fun _ -> True)) 
  (ensures (fun h0 b h1 -> h0 == h1 /\ (b /\ authId i ==> good p)))

// We use the log to correct any verification errors
let verify #i #good k p t =
  let x = HMAC.tls_macVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || is_Some (seq_find (matches p) log))
