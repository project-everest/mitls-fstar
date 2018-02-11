module MAC

(* Idealizing HMAC for the TLS 1.2 record layer (not the handshake)
   TODO: review indexing *) 

open FStar.Seq
 // for e.g. found

open Platform.Bytes
open FStar.Error
//open CoreCrypto 

open Mem
open TLSConstants
open TLSInfo
open TLSError

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

type id = i:id { ID12? i /\ (let ae = aeAlg_of_id i in MACOnly? ae \/ MtE? ae) }

let alg (i:id) = macAlg_of_id i

type text = bytes
type tag (i:id) = lbytes (macSize (alg i))
type keyrepr (i:id) = lbytes (macSize (alg i))

// We keep the tag in case we later want to enforce tag authentication
abstract type entry (i:id) (good: bytes -> Type) = 
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good

// readers and writers share the same private state: a log of MACed messages
// TODO make it abstract
(*
 * AR: two changes: region is of type rgn.
 * log is a hyperstack ref with refinement capturing its rid.
 *)
noeq type key (i:id) (good: bytes -> Type) = 
  | Key: 
    #region: rgn -> // intuitively, the writer's region
    kv: keyrepr i ->
    log: ref (seq (entry i good)){log.id = region} -> key i good

val region: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot rid
val keyval: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot (keyrepr i)
        
let region #i #good (k:key i good) = k.region
let keyval #i #good (k:key i good) = k.kv 

// todo: mark it as private
private let gen0 i good parent kv = 
  let region = new_region parent in 
  let log = ralloc region Seq.createEmpty in 
  Key #i #good #region kv log

val gen: i:id -> good: (bytes -> Type) -> parent: rgn -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->  
    modifies Set.empty h0 h1 /\
    Mem.fresh_subregion (region #i #good k) parent h0 h1 )) 
let gen i good parent = 
  gen0 i good parent (CoreCrypto.random (macKeySize (alg i)))

val coerce: i:id -> good: (bytes -> Type) -> parent: rgn -> kv:keyrepr i -> ST(key i good)
  (requires (fun _ -> ~(authId i)))
  (ensures (fun h0 k h1 ->  
    modifies Set.empty h0 h1 /\
    Mem.fresh_subregion (region #i #good k) parent h0 h1 )) 
let coerce i good parent kv = gen0 i good parent kv

val leak: #i:id -> #good: (bytes -> Type) -> k:key i good {~(authId i)} -> Tot (kv:keyrepr i { kv = keyval k })
let leak   #i #good k = k.kv

val mac: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes { authId i ==> good p } -> ST(tag i) 
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1 
  //  /\ 
  //  sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))


// We log every authenticated texts, with their index and resulting tag
(*
 * AR: had to add a recall to satisfy the precondition of k.log write.
 *)
let mac #i #good k p =
  //assume (HMAC.is_tls_mac (alg i));
  let p : p:bytes { authId i ==> good p } = p in
  let t = HMAC.tls_mac (alg i) k.kv p in
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
  let x = HMAC.tls_macVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || Some? (seq_find (matches p) log))
 
