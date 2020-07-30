(**
Idealizing HMAC for Finished message payloads and binders.
*)
module Old.HMAC.UFCMA

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Seq
open FStar.Bytes
open FStar.Error

open Mem
open TLS.Result
open TLSInfo

module HS = FStar.HyperStack

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type finishedId = i:pre_finishedId{valid (I_FINISHED i)}
type binderId = i:pre_binderId{valid (I_BINDER i)}
type hsId = i:pre_hsId{valid (I_HS i)}
type asId = i:pre_asId{valid (I_AS i)}

type id =
| HMAC_Finished of finishedId
| HMAC_Binder of binderId

let alg (i:id) : HMAC.ha = match i with
| HMAC_Finished i -> TLSInfo.finishedId_hash i
| HMAC_Binder i -> TLSInfo.binderId_hash i

//assume
let authId (_:id) : Tot bool = false  // TODO: move to Flags

type text = bytes
type tag (i:id) = lbytes32 (Hacl.Hash.Definitions.hash_len (alg i))

let keysize (i:id) = Hacl.Hash.Definitions.hash_len (alg i)
type keyrepr (i:id) = lbytes32 (keysize i)

type fresh_subregion rg parent h0 h1 = HS.fresh_region rg h0 h1 /\ extends rg parent

// We keep the tag in case we later want to enforce tag authentication
val entry (i:id) (good: bytes -> Type0) : Type0

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
    log: ref (seq (entry i good)){HS.frameOf log = region} ->
    key i good

let region (#i:id) (#good:(bytes -> Type)) (k:key i good) : GTot rid = k.region
let keyval (#i:id) (#good:(bytes -> Type)) (k:key i good) : GTot (keyrepr i) = k.kv

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
// todo: mark it as private
private let gen0 i good (parent:rgn) kv : ST (key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region #i #good k) parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region = new_region parent in
  let log = ralloc region Seq.empty in
  Key #i #good #region kv log

val gen: i:id -> good: (bytes -> Type) -> parent: rgn -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))

val coerce: i:id -> good: (bytes -> Type) -> parent: rgn -> kv:keyrepr i -> ST(key i good)
  (requires (fun _ -> ~(authId i)))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))

val leak: #i:id -> #good: (bytes -> Type) -> k:key i good {~(authId i)} -> Tot (kv:keyrepr i { kv = keyval k })

val mac: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes { authId i ==> good p } -> ST(tag i)
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1
  //  /\
  //  sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))



val matches: #i:id -> #good:(bytes -> Type) -> p:text -> entry i good -> Tot bool

#set-options "--admit_smt_queries true"
let rec log_entry_matches_p #i #good (log:seq (entry i good)) (p:text) =
  if Seq.length log = 0 then false
  else matches p (Seq.head log)
       || log_entry_matches_p (Seq.tail log) p
       
let verify: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes -> t:tag i -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 /\ (b /\ authId i ==> good p))) =

// We use the log to correct any verification errors
  fun #i #good k p t ->
  let x = HMAC.hmacVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || log_entry_matches_p log p)
