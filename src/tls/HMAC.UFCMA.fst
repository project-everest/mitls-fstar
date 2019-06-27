(**! Idealizing agile HMAC; independent of TLS, used for TLS 1.3 Finished message payloads and Binders. *)
module HMAC.UFCMA

open FStar.Bytes
open Mem
open Pkg

module H = Hashing.Spec
module B = FStar.Bytes
module M = LowStar.Modifies
module DT = DefineTable
module MDM = FStar.Monotonic.DependentMap

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

inline_for_extraction noextract
let ideal = Flags.ideal_HMAC // secret idealization flag for the UFCMA assumption

type safe (#ip:ipkg) (i:ip.t) = b2t ideal /\ ip.honest i
noextract private let is_safe (#ip:ipkg) (i:regid ip) : ST bool 
  (requires fun h0 -> True) (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> safe i)) =
  let b = ip.get_honesty i in ideal && b

// Concrete parameters of an HMAC instance
noeq type info (#ip:ipkg) (i:ip.t) =
| Info: 
  alg: HMAC.ha -> 
  good: (Hashing.macable alg -> bool) ->
  info i

let klen (a:H.alg) : keylen = H.hash_len a
type krepr (a:H.alg) = Hashing.hkey a
type text (a:H.alg) = Hashing.macable a
type tag (a:H.alg) = B.lbytes32 (klen a)

// Type of keyed entries in the MAC idealization table
let log_key (a:H.alg) = tag a * text a
let entry (#ip:ipkg) (i:ip.t) (a:info i) (k:log_key a.alg) =
  squash (safe i ==> a.good (snd k))

// We create a log only for safe instaces
noeq type log_t (#ip:ipkg) (i:ip.t) (a:info i) = 
| Ideal of DT.dt (entry i a)
| Real

noeq type key (#ip:ipkg) (i:regid ip) =
| MAC:
  info: info i ->
  krepr: krepr info.alg ->
  log: log_t i info{Ideal? log <==> safe i} ->
  key i

let footprint (#ip:ipkg) (#i:regid ip) (k:key i)
  : GTot (l:M.loc{not model ==> l == M.loc_none}) =
  match k.log with
  | Ideal log -> DT.loc log
  | Real -> M.loc_none

noextract
val create:
  #ip: ipkg ->
  i: regid ip ->
  a: info i ->
  ST (k:key i)
    (requires fun _ -> model)
    (ensures fun h0 k h1 -> k.info == a /\
      M.modifies M.loc_none h0 h1 /\
      fresh_loc (footprint k) h0 h1)

let create #ip i a =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized a.alg (H.hash_length a.alg));
  let kv: krepr a.alg = Random.sample32 (H.hash_len a.alg) in
  let log =
    if is_safe i then Ideal (DT.alloc (entry i a))
    else Real in
  MAC a kv log

noextract
let coerceT (#ip: ipkg)
  (i: regid ip{~(safe i)})
  (a: info i)
  (kv: lbytes32 (klen a.alg))
  : GTot (key i) =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized a.alg (H.hash_length a.alg));
  MAC a kv Real

val coerce:
  #ip: ipkg ->
  i: regid ip{~(safe i)} ->
  a: info i ->
  kv: lbytes32 (klen a.alg) ->
  ST (key i)
  (requires fun _ -> True)
  (ensures fun h0 k h1 -> k.info == a /\
    k == coerceT i a kv /\
    M.modifies M.loc_none h0 h1 /\
    fresh_loc (footprint k) h0 h1)

let coerce #ip i a kv =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized a.alg (H.hash_length a.alg));
  MAC a kv Real

let log_of (#ip:ipkg) (#i:regid ip) (k:key i)
  : Pure (DT.dt (entry i k.info)) (requires safe i) (ensures fun _ -> True)
  =
  let Ideal log = k.log in log

val mac:
  #ip: ipkg ->
  #i: regid ip -> 
  k: key i ->
  p: text k.info.alg ->
  ST (tag k.info.alg)
  (requires fun _ -> k.info.good p)
  (ensures fun h0 t h1 ->
    M.modifies (footprint k) h0 h1 /\
    (safe i ==> DT.defined (log_of k) (t,p)))

let mac #ip #i k p =
  let tag = HMAC.hmac k.info.alg k.krepr p in
  if is_safe i then
   begin
    let log = log_of k in
    match DT.lookup log (tag,p) with
    | None -> DT.extend log #(tag,p) ()
    | _ -> ()
   end;
  tag

val verify:
  #ip: ipkg ->
  #i: regid ip -> 
  k: key i ->
  p: text k.info.alg ->
  t: tag k.info.alg -> 
  ST bool
  (requires fun _ -> True)
  (ensures fun h0 b h1 -> M.modifies M.loc_none h0 h1 /\
    ((b /\ safe i) ==> k.info.good p))

let verify #ip #i k p t =
  let verified = HMAC.hmacVerify k.info.alg k.krepr p t in
  if is_safe i then
    (match DT.lookup (log_of k) (t,p) with
    | Some u -> verified
    | None -> false) // Detected forgery
  else verified

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

/// For TLS, we'll use something of the form
///
/// let good text =
///   exists digest.
///     hashed ha digest /\
///     text = hash ha digest /\
///     witnessed (fun h -> "this is the writer's state ...")
///
/// - how to deal with agility here?
/// - which level of abstraction?

noextract
unfold let localpkg 
  (ip: ipkg)
  : Pure (local_pkg ip)
  (requires True) 
  (ensures fun p ->
    LocalPkg?.key p == key #ip /\
    LocalPkg?.info p == info)
  =
  Pkg.LocalPkg
    (key #ip)
    info
    (fun #i k -> k.info)
    (fun #i a -> klen a.alg)
    (b2t ideal)
    (footprint #ip) // local footprint
    (fun #_ k h -> True) // local invariant
    (fun #i k h0 l h1 -> ()) // Local invariant framing
    (create #ip)
    (coerceT #ip)
    (coerce #ip)

//TODO (later) support dynamic key compromise

// 18-01-07 only for debugging; how to reliably disable this function otherwise?
noextract 
let string_of_key (#ip:ipkg) (#i:regid ip) (k:key i) : string = 
//18-08-31 TODO string vs string
//"HMAC-"^Hashing.Spec.string_of_alg u.alg^" key="^print_bytes kv
"HMAC key="^print_bytes (k.krepr)

(**! Unit test for the packaging of UFCMA *)

private type id0 =
| Index: hash_alg:H.alg -> nat -> id0
type id = (if model then id0 else unit)
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"

noextract
private let test (a: HMAC.ha) (v': Hashing.macable a) (t': H.tag a)
  : ST bool
  (requires fun h0 -> model)
  (ensures fun h0 _ h1 -> True)
  =
  let p = localpkg ip in
  let q = memoization_ST p in
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
  //assume(q.Pkg.package_invariant h0);

  //TODO superficial but hard to prove...
  // assume(Monotonic.RRef.m_sel h0 (Pkg.itable table) == MDM.empty_map ip.Pkg.t (key ip));
  // assert(MDM.fresh (Pkg.itable table) 0 h0);
  // assert(q.Pkg.define_table == table);
  //assert(mem_fresh q.Pkg.define_table 0 h0);

  //17-11-23  causing mysterious squash error
  // assert_by_tactic(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == Pkg.Pkg?.info q 0) FStar.Tactics.(norm "foo");
  // let u = u <: Pkg.Pkg?.info q 0 in
  let i0 = Index a 0 in
  let a0 : info #ip i0 = Info a (fun v -> length v = 0) in
  assume(DT.fresh q.define_table i0 h0);
  let k: key #ip i0 = Pkg?.create q i0 a0 in

  // testing usability of logical payloads
  let v = empty_bytes in
  assert(a0.good v);
  let t = mac k v in
  let b0 = verify k v' t in
  assert(b0 /\ b2t ideal ==> length v' = 0);
  let b1 = verify k v' t' in
  assert(b1 /\ b2t ideal ==> length v' = 0);
  //assert false; // sanity check
  let _ = IO.debug_print_string (string_of_key k^" tag="^print_bytes t^"\n") in
  b0 && not b1

noextract
let unit_test(): St bool = 
  let _ = IO.debug_print_string "HMAC.UFCMA\n" in 
  assume(model); //18-01-07 avoid?
  let b0 = 
    let a = Hashing.SHA1 in 
    assert_norm(Hashing.Spec.block_length a <= Hashing.Spec.max_input_length a);
    test a empty_bytes (Bytes.create (Hacl.Hash.Definitions.hash_len a) 42z) in
  let b1 = 
    let a = Hashing.SHA1 in 
    test a empty_bytes (Bytes.create (Hacl.Hash.Definitions.hash_len a) 42z) in
  let b2 = 
    let a = Hashing.SHA1 in 
    test a empty_bytes (Bytes.create (Hacl.Hash.Definitions.hash_len a) 42z) in
  b0 && b1 && b2
  // nothing bigger? 

(* --------- older, TLS-specific implementation. 18-01-07 to be deleted

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
  let log = ralloc region Seq.empty in
  Key #i #good #region kv log

val gen: i:id -> good: (bytes -> Type) -> parent: rgn -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))
let gen i good parent =
  gen0 i good parent (Random.sample (keysize i))

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
