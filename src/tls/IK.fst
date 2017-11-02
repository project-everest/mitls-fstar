module IK 

/// Standalone experiment modelling key extraction and key derivation
/// parametrized by a usage function from labels to derived keyed
/// functionalities.
///
/// * captures nested derivations via bounded-recursive instantiation.
/// * captures PRF-ODH double game 
/// * applied to the full extract/expand key schedule of TLS 1.3
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility and ideal-only indexes.
///
/// We plan to split this file into many modules, as planned on slack.
/// 
/// Not done yet:
///
/// * mysterious typing errors (see comments) 
/// * reliance on u_of_i in DH extraction (intuitive but hard to code)
/// * key registration and discretionary compromise 
/// * extraction: ensure all strongly-dependent types disappear
/// * deal with create/coerce stateful pre- and post-condition.
/// * usage restriction for KDFs, based on a generalization of wellformed_id
///
/// Note also that we support rather static agility and usages; we may
/// enable more details to be bound as part of the derivation label.

open FStar.HyperStack
open FStar.HyperStack.ST

// temporary imports

type bytes = Platform.Bytes.bytes
let lbytes (len:UInt32.t) = Platform.Bytes.lbytes (UInt32.v len)

let sample (len:UInt32.t): ST (lbytes len) 
    (requires fun h0 -> True)
    (ensures fun h0 r h1 -> True)
  = CoreCrypto.random (UInt32.v len)

/// --------------------------------------------------------------------------------------------------
/// module Pkg (stateless)
/// We embed first-class modules as datatype "packages"
///
/// Index packages provide a "safe" predicate to control conditional idealization.
/// We use "honest" to refer to the adversarie's intent, and "safe" for fine-grained idealization,
/// with "safe ==> honest" as a pointwise lemma.
/// When do we need to access one vs the other? Each instance can cache "safe". 

noeq type ipkg (info: Type0)  = | Idx: 
  t: Type0 -> 
  get_info: (t -> info) ->
  honest: (t -> bool) ->  
  ipkg info

/// Keyed functionality define Key packages, parametric in their
/// indexes, but concrete on their key randomness; instances may have
/// any number of other functions (such a leak, for instance).

/// Derived key length restriction when using HKDF
type keylen = l:UInt32.t {UInt32.v l <= 256} 

// got into trouble using a type abbreviation for "info i"; retry later

noeq type pkg (info: Type0) (ip: ipkg info) = | Pkg:
  key: (ip.t -> Type0) -> 
  len: (info -> keylen) ->
  create: (
    i:ip.t -> a:info{a == ip.get_info i} -> ST (key i)
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> True)) -> 
  coerce: (
    i:ip.t -> a:info{a == ip.get_info i} -> lbytes (len a) -> ST (key i)
    (requires fun h0 -> ~(ip.honest i))
    (ensures fun h0 p h1 -> True)) ->
  pkg info ip 

/// The "get_info" function ensure that all instances share the same
/// runtime information; we still pass info inasmuch as the index will
/// be erased.


/// NEXT, WE DEFINE A FEW SAMPLE FUNCTIONALITIES,
/// parameterized on their abstract index package.
/// 
/// can we factor out pre/post and boilerplate spec? 
///
/// When ~(honest i), we must have  
///
/// create i a == coerce i a (sample (len a))

/// --------------------------------------------------------------------------------------------------
/// module AEAD
/// sample generic, agile functionality.
///
/// TODO package instead StAE.

type aeadAlg = | AES_GCM128 | AES_GCM256
let aeadLen: aeadAlg -> keylen = function
  | AES_GCM128 -> 32ul
  | AES_GCM256 -> 48ul

// 17-10-31  this abbreviation breaks typechecking when used; why?
// unfold type aeadAlgi (#ip:ipkg aeadAlg) (i:ip.t) = a:aeadAlg {a == ip.get_info i}

type keyrepr a = lbytes (aeadLen a)
assume new type key (#ip: ipkg aeadAlg) (i: ip.t) // abstraction required for indexing
assume val create_key: #ip: ipkg aeadAlg -> i: ip.t -> a:aeadAlg {a == ip.get_info i} -> 
  ST (key i)
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> True)  

assume val coerce_key: #ip: ipkg aeadAlg -> i: ip.t -> a:aeadAlg {a == ip.get_info i} -> keyrepr a ->
  ST (key i)
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> True)

let mp (ip:ipkg aeadAlg): pkg aeadAlg ip = Pkg 
  key 
  aeadLen 
  create_key 
  coerce_key

val encrypt: #ip:ipkg aeadAlg -> #i:ip.t -> k: key i -> nat -> nat 
let encrypt #ip #i k v = v + 1

/// --------------------------------------------------------------------------------------------------
/// module Raw
/// a default functionality (no idealization);
/// for modelling, we could also provide a "leak" function

type raw  (#ip: ipkg keylen) (i: Idx?.t ip) = lbytes (ip.get_info i)
let create_raw (#ip: ipkg keylen) (i: ip.t) (len:keylen {len = ip.get_info i}): St (raw  i) = sample len
let coerce_raw (#ip: ipkg keylen) (i: ip.t) (len:keylen {len = ip.get_info i}) (r:lbytes len): raw i = r
let rp (ip:ipkg keylen): pkg keylen ip = Pkg 
  raw 
  (fun n -> n) 
  create_raw 
  coerce_raw


/// TLS-SPECIFIC KEY SCHEDULE
/// --------------------------------------------------------------------------------------------------

/// module Index
/// 
/// We provide an instance of ipkg to track key derivation (here using constant labels)
/// these labels are specific to HKDF, for now strings e.g. "e exp master".
type label = string

/// the middle extraction takes an optional DH secret, identified by this triple
/// we use our own datatype to simplify typechecking
type id_dhe = 
  | NoDHE
  | DHE:
    g: CommonDH.group -> 
    gX: CommonDH.share g ->
    gY: CommonDH.share g -> id_dhe

// The "ciphersuite hash algorithms"  eligible for TLS 1.3 key derivation. 
// We will be more restrictive. 
type kdfa = Hashing.Spec.alg

/// Runtime key-derivation parameters, to be adjusted.
///
/// HKDF defines an injective function from label * context to bytes, to be used as KDF indexes.
///
type context = 
  | Extract: context // TLS extractions have no label and no context; we may separate Extract0 and Extract2
  | ExtractDH: id_dhe -> context // This is Extract1 (the middle extraction)
  | Expand: context // TLS expansion with default hash value 
  | ExpandLog: // TLS expansion using hash of the handshake log
    info: TLSInfo.logInfo (* ghost, abstract summary of the transcript *) -> 
    hv: Hashing.Spec.anyTag (* requires stratification *) -> context

type id_psk = nat // external application PSKs only; we may also set the usage's maximal recursive depth here.
type pre_id = 
  | Preshared: 
      a: kdfa (* fixing the hash algorithm *) -> 
      id_psk  -> 
      pre_id 
  | Derive: 
      i:pre_id (* parent index *) -> 
      l:label (* static part of the derivation label *) -> 
      context (* dynamic part of the derivation label *) -> 
      pre_id

(* was:
  | Extract0: materials: pre_id -> pre_id
  | Extract1: salt: pre_id -> materials: id_dhe -> pre_id 
  | Extract2: salt: pre_id -> pre_id
  | Derived: 
    secret:pre_id -> 
    lbl: (* HKDF constant *) label -> 
    info: TLSInfo.logInfo (* ghost, abstract summary of the transcript *) -> 
    hv: Hashing.Spec.anyTag (* requires stratification *) -> pre_id 

  | Derived: 
    secret:pre_id -> 
    lbl: (* HKDF constant *) label -> 
    ctx: context -> 
    pre_id 
    
    info: TLSInfo.logInfo (* ghost, abstract summary of the transcript *) -> 
    hv: Hashing.Spec.anyTag (* requires stratification *) -> pre_id 

// We could have different constructors, depending on the presence of
// a digest and length (in which case we should be careful of label
// formatting) or not, keeping any case analysis on the label local.
//
// Underneath, HKDF takes a "context" and a required length, with
// disjoint internal encodings of the context:
// [HKDF.format #ha label digest len]
//
// [lbl] and [hv] and ha_of_id determine the HKDF context; in HKDF we
// prove that their encoding is injective.
//
// info is a function of hv, included for verification convenience.
// (details to be adapted from the HS). 
// Hence same hashed digest ==> same logInfo, but not the converse.
*)

//17-10-30 painful
// #set-options "--max_ifuel 3 --initial_ifuel 1"

// always bound by the index (and also passed concretely at creation-time).
val ha_of_id: i:pre_id -> kdfa
let rec ha_of_id = function 
  | Preshared a _ -> a
  | Derive i lbl ctx -> ha_of_id i 

// placeholders
assume val idh_of_log: TLSInfo.logInfo -> id_dhe
assume val summary: bytes -> TLSInfo.logInfo

// concrete transcript digest
let digest_info (a:kdfa) (info:TLSInfo.logInfo) (hv: Hashing.Spec.anyTag) =
  exists (transcript: bytes). 
    // Bytes.length hv = tagLen a /\
    hv = Hashing.Spec.hash a transcript /\ 
    Hashing.CRF.hashed a transcript /\
    info = summary transcript 

/// stratified definition of id required.
///
let rec wellformed_id: (pre_id -> Type0) = function
  | Preshared a _ -> True
  | Derive i l (ExpandLog info hv) -> wellformed_id i /\ digest_info (ha_of_id i) info hv 
  | Derive i lbl ctx -> 
      //TODO "ctx either extends the parent's, or includes its idh" /\ 
      wellformed_id i
           
type id = i:pre_id {wellformed_id i}


// 17-10-21 WIDE/NARROW INDEXES (old) 
//
// We'd rather keep wide indexes secret.  Internally, for each salt
// index, we maintain a table from (g, gX, gY) to PRFs, with some
// sharing.  (The sharing may be public, but not wide indexes values
// are not.)  Informally this is sound because our limited use of the
// tables does not depend on their sharing.
//
// The danger of overly precise indexes is that, ideally, we may
// separate instances that use the same concrete keys---in our case
// this does not matter because security does not depend on their
// sharing.

assume val honest: i:id -> bool //17-10-31 FIXME
let ii (#info:Type0) (get_info: id -> info) = Idx id get_info honest
/// Try out on examples: we may need a stateful invariant of the form
/// "I have used this secret to create exactly these keys".


/// We expect this function to be fully applied at compile time,
/// returning a package and a algorithm-derivation function to its
/// agility parameter (to be usually applied at run-time).
/// 

noeq type range (info: Type0) (lbl:label) = | Use:
    info': Type0 ->
    get_info': (id -> info') ->
    pkg': pkg info' (ii #info' get_info') -> 
    derive: (i: id -> a: info -> ctx: context {wellformed_id (Derive i lbl ctx)} -> a': info' {a' == get_info' (Derive i lbl ctx)}) -> range info lbl

type usage (info: Type0) = lbl: label -> (* compile-time *) range info lbl

// Initially, the info only consists of the hash algorithm, and it is
// invariant through extractions and derivations... until the first
// hashed transcript, at which point the

(* 
/// parametricity? (Old/Later)
/// we have [#id #pd #u #i #a] 
/// u v returns [#ip #p (derive_alg: pd.info -> p.info) (derive_index: id.t -> i.t)] 
///
/// We finally use a global, recursive instantiation of indexes to
/// compose all our functionalities, with for instance
/// (fun i -> Derived i v) to get the derived index.

// (*UNUSED *) type usage' (#ii:ipkg) (a: ii.t -> Type0) = 
//   label -> 
//     ip:ipkg & 
//     p: pkg ip & 
//     derive_index: (ii.t -> ip.t) &
//     derive_info: (i: ii.t -> a i -> p.use (derive_index i))
// note that [a] is [d.use]
// should usage be part of info?
// what about state state (safety etc)? 
*)

/// --------------------------------------------------------------------------------------------------
/// module KDF
/// 
/// we define a KDF parametric in both its usage and ipkg
/// We rely on type abstraction to separate secrets with different indexes
/// For soundness, we must also prevent external calls to create derived secrets.
///
/// We idealize KDF as a random function, with lazy sampling.
/// This holds syntactically only after inlining all calls to
/// pkg.create/coerce.
/// 
/// This requires memoizing calls, which is a bit tricky when calling
/// stateful allocators.

type details (ha:kdfa) = | Log: 
  loginfo: TLSInfo.logInfo -> 
  hv: Hashing.Spec.anyTag {digest_info ha loginfo hv} -> details ha

type info = | Info:
  ha:kdfa ->
  option (details  ha) -> info 

val get_info: id -> info 
// 17-11-01 can't get it to verify; should follow from the definition of wellformed_id? 
let rec get_info (i0: id): info = 
  match i0 with 
  | Preshared a _ -> Info a None 
  | Derive i l (ExpandLog log hv) ->
       assert(wellformed_id i0); 
       assume false; 
       // assert(wellformed_id i); 
       let i:id = i in // sigh
       let Info a _ = get_info i in
       Info a (Some (Log log hv))
  | Derive i _ _ -> 
       assert(wellformed_id i); 
       let i:id = i in // sigh
       get_info i 

let derived_key 
  (u: usage info) 
  (i: id) 
  (lbl: label)
  (c: context {wellformed_id (Derive i lbl c)})
= 
  let use = u lbl in 
  let i': id = Derive i lbl c in 
  use.pkg'.key i'

let there: FStar.Monotonic.RRef.rid = admit() 

/// key-derivation table (memoizing create/coerce)
type domain (i: id) = | Domain:
  lbl: label -> 
  ctx: context {wellformed_id (Derive i lbl ctx)} -> domain i 

private type table 
  // (ip: ipkg) 
  (u: usage info)
  (i: id) 
= MonotoneMap.t there (domain i) (fun (Domain lbl ctx) -> derived_key u i lbl ctx) (fun _ -> True)

let secret_len (a: info): keylen = UInt32.uint_to_t (Hashing.Spec.tagLen a.ha)
 
// when to be parametric on ip? not for the KDF itself: we use ip's constructors.
let secret (u: usage info) (i: id) 
=
  if honest i 
  then table u i 
  else lbytes (secret_len (get_info i))

let secret_ideal (#u: usage info) (#i: id) (t: secret u i {honest i}): table u i = t 
let ideal_secret (#u: usage info) (#i: id) (t: table u i {honest i}): secret u i = t 
//let corrupt_secret (#u: usage info) (#i: id) (v: lbytes (secret_len (get_info i)) {~(honest i)}): secret u i = v

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).
 
/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.
///
/// MK: what does reverse-inline of low-level KeyGen mean?

val coerce: 
//ip: ipkg ->
  u: usage info ->
  i: id ->
  a: info {a == get_info i} (* run-time *) -> 
  repr: lbytes (secret_len a) -> 
  ST (secret u i)
  (requires fun h0 -> ~(honest i))
  (ensures fun h0 p h1 -> True)
let coerce u i a repr = repr

val create: 
//ip: ipkg ->
  u: usage info -> 
  i: id ->
  a: info {a == get_info i}(* run-time *) ->
  ST (secret u i)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let create u i a = 
  if honest i 
  then 
    //style: how to avoid repeating those parameters?
    MonotoneMap.alloc #there #(domain i) #(fun (Domain lbl ctx) -> derived_key u i lbl ctx) #(fun _ -> True) 
  else 
    coerce u i a (sample (secret_len a)) 

let pp (* ip:ipkg *) (u: usage info): pkg info (ii get_info) = Pkg 
  (secret u) 
  secret_len
  (create u) 
  (coerce u)

/// TODO consider separating pp packages more explicitly, so that we
/// can idealize them one at a time. (Having one proof step for each
/// nested level of key derivation seems unavoidable.)


inline_for_extraction
val derive:
  #u: usage info ->
  #i: id ->
  a: info {a == get_info i} -> 
  k: secret u i ->
  lbl: label -> 
  ctx: context {wellformed_id (Derive i lbl ctx)} ->
  ST (derived_key u i lbl ctx)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)

let derive  #u #i a k lbl ctx = 
  let x = Domain lbl ctx in 
  let use = u lbl in 
  let a' = use.derive i a ctx in 
  let i' = Derive i lbl ctx in 
  if honest i (*safe?*) 
  then
    let v: option (derived_key u i lbl ctx) = MonotoneMap.lookup (secret_ideal k) x in 
    match v with 
    //17-10-30 was failing with scrutiny error: match MonotoneMap.lookup (secret_ideal k) x
    | Some dk -> dk
    | None -> 
      let dk = use.pkg'.create i' a' in 
      //17-10-20 TODO framing across create
      let h = HyperStack.ST.get() in 
      assume(MonotoneMap.fresh (secret_ideal k) x h);
      MonotoneMap.extend (secret_ideal k) x dk; 
      dk
  else 
    let raw =
      HKDF.expand #(a.ha) k (Platform.Bytes.abytes lbl) (UInt32.v (use.pkg'.len a')) in 
    assume(honest i' ==> honest i); //17-10-31 TODO with Antoine
    use.pkg'.coerce i' a' raw

/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

/// key-derivation table (memoizing create/coerce)

let ssa #a: Preorder.preorder (option a) = fun x y -> 
  match x, y with
  | None, Some _ -> True 
  | Some v, Some v' -> v == v'
  | _ -> False 

// memoizing a single extracted secret
private type mref_secret (u: usage info) (i: id) = 
  HyperStack.mref (option (secret u i)) ssa 

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
type psk (u: usage info) (i: id) = (
  let i' = Derive i "" Extract in 
  if (* Flags.extract0 && *) honest i 
  then mref_secret u i'
  else lbytes (secret_len (get_info i')))

val coerce_psk: 
  #u: usage info ->
  i: id -> 
  a: info {a == get_info i} -> 
  raw: lbytes (secret_len a) -> 
  ST (psk u i)
  (requires fun h0 -> ~(honest i))
  (ensures fun h0 p h1 -> (*TBC*) True)
let coerce_psk #u i a raw = raw

val create_psk: 
  #u: usage info ->
  i: id -> 
  a: info {a == get_info i} -> 
  ST (psk u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
let create_psk #u i a = 
  if honest i then 
    let t' = secret u (Derive i "" Extract) in 
    let r: psk u i = Monotonic.RRef.m_alloc #(option t') #ssa there None in // better style or library call? 
    r
  else 
    coerce_psk #u i a (sample (secret_len a)) 

let pskp (*ip:ipkg*) (u:usage info): pkg info (ii get_info) = Pkg 
  (psk u)
  secret_len
  create_psk
  coerce_psk

/// HKDF.Extract(key=0, materials=k) idealized as a (single-use) PRF,
/// possibly customized on the distribution of k.
val extract0:
  #u: usage info ->
  #i: id ->
  k: psk u i -> 
  a: info {a == get_info i} ->
  ST 
    (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract0 #u #i k a = 
  let i': id = Derive i "" Extract in 
  if (* Flags.extract0 && *) honest i 
  then 
    let k: mref_secret u i = k in 
    match admit() (* Monotonic.RRef.m_read k *) with //17-11-02 ?!
    | Some extract -> extract
    | None -> 
        let extract = create u i' a in 
        //TODO framing 
        // Monotonic.RRef.m_write k extract; 
        extract 
  else 
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in 
    assume(honest i' ==> honest i); //17-10-31 TODO with Antoine
    coerce u i' a raw


/// The "salt" is an optional secret used (exclusively) as HKDF
/// extraction key. The absence of salt (e.g. when no PSK is used) is
/// handled using a special, constant salt marked as compromised.
/// 
/// salt is indexed by the usage of the secret that will be extracted
/// (the usage of the salt itself is fixed).
///
/// We use separate code for salt1 and salt2 because they are
/// separately idealized (salt1 is more complicated)

assume type salt (u: usage info) (i: id)

assume val create_salt: 
  #u: usage info -> 
  i: id -> 
  a: info -> 
  salt u i

assume val coerce_salt: 
  #u: usage info ->
  i: id ->
  a: info -> 
  raw: lbytes (secret_len a) ->
  salt u i 

let saltp (*ip:ipkg*) (u:usage info): pkg info (ii get_info) = Pkg 
  (salt u)
  secret_len
  create_salt 
  coerce_salt


/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-step
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.

/// two flags; we will idealize ODH first
/// 
assume val flag_prf1: bool 
assume val flag_odh: b:bool { (flag_prf1 ==> b) /\ (b ==> Flags.ideal_KEF) } 

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
///
assume val prf_extract1:
  #u: usage info -> 
  #i: id ->
  a: info {a == get_info i} -> 
  s: salt u i ->
  idh: id_dhe ->
  gZ: bytes -> 
  ST (secret u (Derive i "" (ExtractDH idh)))
  (requires fun h0 -> True) 
  (ensures fun h0 k h1 -> True)
(*
let prf_extract1 #u #i #a s g gX gY gZ = 
  let idh = (| g, gX, gY |) in
  let j = Extract1 i idh in
  let pkg = pp ii u in 
  if flag_prf1 && ii.honest i 
  then 
    let w = 
      // "wide" PRF, memoized on gZ
      match find s.wide gZ with 
      | Some w -> w // may return k
      | None -> 
        let w = pkg.create0 j a in
        s.wide := snoc s.wide w;
        w in 
    pkg.create j k 
    // agreement on the algorithms follows from the salt.
  else 
    let raw = HKDF.extract (prf_leak s) gZ (* narrow, concrete *) in 
    pkg.coerce j a raw 
*)

assume val prf_leak:
  #u: usage info -> 
  #i: id ->
  #a: info {a == get_info i} -> 
  s: salt u i { flag_prf1 ==> ~(honest i)} -> Hashing.Spec.hkey a.ha
// revisit condition, a bit awkward.

/// ODH (precisely tracking the games, not yet code-complete
/// --------------------------------------------------------------------------------------------------

// Ideally, we maintain a monotonic map from every honestly-sampled
// initiator share gX to its set of honestly-sampled responders shares
// (i,gY). 
// The table exists when [Flags.ideal_KDF], a precondition for [flag_odh]

// We need a variant of MonotoneMap that enables monotonic updates to
// each entry. We used nested ones to re-use existing libraries, but
// may instead invest is a custom library.
//
// how to share the u and a parameters? intuitively, u is statically
// fixed for everyone, and a is determined by the index i.

//17-10-30 unclear how to fix the usage at packaging-time.  This
// should be entirely static. Intuitively, there is a function from
// indexes to usage. Probably definable with the actual usage (big
// mutual reduction?)
assume val u_of_i: i:id -> usage info 

let peer_table (#g: CommonDH.group) (gX: CommonDH.share g): Type0 = 
  MonotoneMap.t there 
    (i:id * gY: CommonDH.share g)
    (fun i_gY -> 
      let (i, gY) = i_gY in 
      secret (u_of_i i) (Derive i "" (ExtractDH (DHE g gX gY))))
    (fun _ -> True)

let odh_table = 
  MonotoneMap.t there 
  (g: CommonDH.group & gX: CommonDH.share g)
  (fun (| g, gX |) -> _: peer_table gX{CommonDH.honest_share (|g, gX|)})
  (fun _ -> True)

let odh_state: (if Flags.ideal_KEF then odh_table else unit) = 
  if Flags.ideal_KEF
  then MonotoneMap.alloc 
    #there
    #(g: CommonDH.group & gX: CommonDH.share g)
    #(fun (| g, gX |) -> _:peer_table gX{CommonDH.honest_share (|g, gX|)})
    #(fun _ -> True)
  else ()

val honest_gX: #g:CommonDH.group -> gX: CommonDH.share g -> Type0 
let honest_gX #g gX = 
  if Flags.ideal_KEF then 
    let t: odh_table = odh_state in 
    Monotonic.RRef.witnessed (MonotoneMap.defined t (|g,gX|))
  else True
//17-10-22 why can't I write flag_odh ==> ... ? {logic} error   
//17-10-23 for now we could use that style only with an annotated let instead of val;let

val test_honest_gX: #g:CommonDH.group -> gX: CommonDH.share g -> ST (b:bool)
  (requires fun h0 -> Flags.ideal_KEF)
  (ensures fun h0 b h1 -> 
    h0 == h1 /\ 
    Flags.ideal_KEF /\ 
    (let t: odh_table = odh_state in 
    ( b2t b == MonotoneMap.defined t (|g,gX|) h1) /\
      (b ==> honest_gX gX)
    ))
let test_honest_gX #g gX = 
  let t: odh_table = odh_state in
  match MonotoneMap.lookup t (|g,gX|) with
  | Some _ -> true
  | None -> false


//assume val info_id: i:id -> a: info


#set-options "--print_universes --print_implicits"

// assume val peer_gX: #g:CommonDH.group -> i:id -> gX: CommonDH.share g -> gY: CommonDH.share g {wellformed_id (Derive i "" (ExtractDH (Some (| g, gX, gY |))))} -> 
//   option (secret 
//     (u_of_i i)
//     (Derive i "" (ExtractDH (Some (| g, gX, gY |)))) 
//     (info_id (Derive i "" (ExtractDH (Some (| g, gX, gY |))))))


// let peers_gX #g gx = let t: peer_table = odh_table in MonotoneMap.lookup h0.[t] (|g,gX|)

// ideal state 
// val peer: mref (map gX --> list (i,gY)) 
// - presence codes I[X]
// - contents codes R[X] 
// conversely [keyshare] locally provides  x

/// Client-side instance creation
/// (possibly used by many honest servers)
val odh_init: g: CommonDH.group -> ST (CommonDH.keyshare g)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 -> honest_gX (CommonDH.pubshare x))
// TODO framing: we only modify the global table regions for CommonDH and ODH
 
let odh_init g = 
  let x = CommonDH.keygen g in 
  if Flags.ideal_KEF then (
    let t: odh_table = odh_state in 
    let gX: CommonDH.share g = CommonDH.pubshare x in  
    assert(CommonDH.honest_share (|g,gX|));
    // TODO 17-10-22 since gX is freshly registered, we statically
    // know it can't occur in the peers table; what's a better keygen
    // spec for that?
    let peers = MonotoneMap.alloc 
      #there 
      #(i:id * gY: CommonDH.share g)
      #(fun i_gY -> 
        let (i, gY) = i_gY in 
        secret (u_of_i i) (Derive i "" (ExtractDH (DHE g gX gY))))
      #(fun _ -> True) in
    if None? (MonotoneMap.lookup t (|g,gX|)) then MonotoneMap.extend t (|g,gX|) peers;
    assert(honest_gX gX)
    );
  x // could additionally return gX 
// TODO crypto agility: do we record keygen as honest for a bad group? 


/// Server-side creation and completion
///
/// An elaboration of "derive" for two-secret extraction
/// - kdf is the child KDF package.
/// - HKDF is the concrete algorithm
///
/// We require that gX be the share of a honest initiator,
/// but not that they agree on the salt index
val odh_test:
  #u: usage info -> 
  #i: id -> 
  a: info {a == get_info i} -> 
  s: salt u i ->
  g: CommonDH.group ->
  gX: CommonDH.share g -> 
  ST ( 
    gY:CommonDH.share g &
    (let idh = DHE g gX gY in //17-10-31 BUG? adding the eta-expansion was necessary
    secret u (Derive i "" (ExtractDH idh))))
  (requires fun h0 -> honest_gX gX)
  (ensures fun h0 r h1 -> 
    // todo, as sanity check
    // let (|gY, s|) = dfst r in 
    // flag_odh ==> s == peer_gX gY
    True)

let odh_test #u #i a s g gX = 
  assume (u == u_of_i i); //17-11-01 TODO modelling
  (* we get the same code as in the game by unfolding dh_responder, e.g.
  let y = CommonDH.keygen g in 
  let gY = CommonDH.pubshare y in  
  let gZ: bytes (*CommonDH.share g*) = ... in  // used only when (not flag_odh)
  *)
  let gY, gZ = CommonDH.dh_responder gX in 
  let idh = DHE g gX gY in
  let j = Derive i "" (ExtractDH idh) in 
  assert(a == get_info j);
  let k: secret u j = 
    if flag_odh
    then (*KDF.*) create u j a (* narrow *)
    else 
      // we know the salt is dishonest because flag_kdf is off
      let raw = HKDF.extract #a.ha (prf_leak s) gZ (* wide, concrete *) in 
      //TODO deduce that j is dishonest too.
      assume(~(honest j));
      coerce u j a raw in
  if Flags.ideal_KEF then (
      let t: odh_table = odh_state in 
      // guaranteed to succeed by honest_gX 
      Monotonic.RRef.testify(MonotoneMap.defined t (|g,gX|));
      let peers = Some?.v (MonotoneMap.lookup t (|g,gX|)) in 
      if None? (MonotoneMap.lookup peers (i,gY)) then 
      MonotoneMap.extend peers (i,gY) k
      );
  (| gY, k |) 

// the PRF-ODH oracle, computing with secret exponent x
val odh_prf:
  #u: usage info -> 
  #i: id -> 
  a: info {a == get_info i}-> 
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.keyshare g -> 
  gY: CommonDH.share g -> 
  ST (
    let gX = CommonDH.pubshare x in 
    let idh = DHE g gX gY in //17-10-31 BUG? adding the eta-expansion was necessary
    secret u (Derive i "" (ExtractDH idh)))
    (requires fun h0 -> 
      let gX = CommonDH.pubshare x in
      honest_gX gX /\ (
      Flags.ideal_KEF ==> (
        let t: odh_table = odh_state in 
        MonotoneMap.defined t (|g,gX|) h0 /\ (
        let peers = MonotoneMap.value t (|g,gX|) h0 in 
        ~ (MonotoneMap.defined peers (i,gY) h0)))))  // what a mouthful
    (ensures fun h0 _ h1 -> True)

// requires peer[gX] is defined (witnessed in x) and does not contain (i,gY)
// None? (find (i, gY) !peer[gX])

// 17-11-01 stuck on seemingly identical types.
// #set-options "--detail_errors"
// #set-options "--print_full_names --print_universes --print_implicits"
// #set-options "--ugly" 
let odh_prf #u #i a s g x gY = 
  let gX = CommonDH.pubshare x in 
  let idh = DHE g gX gY in
  let gZ = CommonDH.dh_initiator x gY in
  admit()
  // prf_extract1 a s idh gZ


/// --------------------------------------------------------------------------------------------------
/// Diffie-Hellman shares
/// module Extract1, or KEF.ODH

// TODO: instead of CommonDH.keyshare g, we need an abstract stateful
// [abstract type private_keyshare g = mref bool ...] that enables
// calling it exactly once

/// Initiator computes DH keyshare, irrespective of the KDF & salt. 
let initI (g:CommonDH.group) = odh_init g 

/// Responder computes DH secret material
val extractR:
  #u: usage info -> 
  #i: id -> 
  s: salt u i ->
  a: info {a == get_info i} -> 
  g: CommonDH.group ->
  gX: CommonDH.share g ->
  ST( 
    gY:CommonDH.share g & (
      let idh = DHE g gX gY in 
      secret u (Derive i "" (ExtractDH idh))))
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 -> True)

//#set-options "--print_universes --print_implicits --print_full_names"
//#set-options "--max_ifuel 3 --initial_ifuel 1"
//#set-options "--ugly" 
let extractR #u #i s a g gX = 
  let b = 
    if Flags.ideal_KEF then test_honest_gX gX else false in
  if b 
  then 
//17-11-01 why do I need to rewrite [odh_test a s g gX] to this?
    let (| gY, k |) = odh_test a s g gX in
    (| gY, k |)
  else
    // real computation: gY is honestly-generated but the exchange is doomed
    let gY, gZ = CommonDH.dh_responder gX in 
    let idh = DHE g gX gY in
    let j = Derive i "" (ExtractDH idh) in 
    let k = prf_extract1 a s idh gZ in
//17-11-01 still stuck on that one
   admit() 
   // (| gY, k |)

/// Initiator computes DH secret material
val extractI: 
  #u: usage info -> 
  #i: id -> 
  a: info {a == get_info i} ->
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.keyshare g ->
  gY: CommonDH.share g ->
  ST(secret u (Derive i "" (ExtractDH (DHE g (CommonDH.pubshare x) gY))))
  (requires fun h0 -> honest_gX (CommonDH.pubshare x))
  (ensures fun h0 k h1 -> True)

let extractI #u #i a s g x gY = 
  if Flags.ideal_KEF then 
    let gX = CommonDH.pubshare x in
    let t: odh_table = odh_state in 
    Monotonic.RRef.testify(MonotoneMap.defined t (|g,gX|));
    let idh = DHE g (CommonDH.pubshare x) gY in
    let peers = Some?.v (MonotoneMap.lookup t (|g,gX|)) in 
    let i' = Derive i "" (ExtractDH idh) in
    assert(wellformed_id i);
    assume(wellformed_id i'); //17-11-01 same as above?
    let ot = secret u i' in
    assume (u == u_of_i i); //17-11-01 indexing does not cover u yet
    let o : option ot = MonotoneMap.lookup peers (i,gY) in
    match o with 
    | Some k -> k
    | None -> odh_prf #u #i a s g x gY
  else odh_prf #u #i a s g x gY

val extractP: 
  #u:usage info ->
  #i: id ->
  a: info {a == get_info i} -> 
  s: salt u i ->
  ST(secret u (Derive i "" (ExtractDH NoDHE)))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let extractP #u #i a s = 
  let gZ = Hashing.Spec.zeroHash a.ha in
///17-11-01 stuck on this one too.  
  admit()
  // prf_extract1 a s NoDHE gZ
  


/// ---------------- final (useless) extraction --------------------
/// 
type salt2 (u: usage info) (i: id) = (
  let i' = Derive i "" Extract in 
  if (*TODO Flags.ideal && *) honest i  
  then mref_secret u i'
  else lbytes (secret_len (get_info i')))

// same code as for PSKs; but extract0 and extract2 differ concretely

val coerce_salt2: 
  #u: usage info ->
  i: id ->
  a: info {a == get_info i} -> 
  raw: lbytes (secret_len a) ->
  ST (salt2 u i)
  (requires fun h0 -> ~(honest i))
  (ensures fun h0 p h1 -> (*TBC*) True)
let coerce_salt2 #u i a raw = raw

val create_salt2: 
  #u: usage info -> 
  i: id -> 
  a: info {a == get_info i} -> 
  ST (salt2 u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
let create_salt2 #u i a = 
  if honest i then 
    let t' = secret u (Derive i "" Extract) in 
    let r: salt2 u i = Monotonic.RRef.m_alloc #(option t') #ssa there None in // better style or library call? 
    r
  else 
    coerce_salt2 #u i a (sample (secret_len a)) 

let saltp2 (u:usage info): pkg info (ii get_info) = Pkg 
  (salt2 u)
  secret_len
  create_salt2 
  coerce_salt2

/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
/// The salt is used just for extraction, hence [u] here is for the extractee.
/// Otherwise the code is similar to [derive], with different concrete details
val extract2: 
  #u: usage info ->
  #i: id ->
  s: salt2 u i -> 
  a: info {a == get_info i} ->
  ST (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract2 #u #i s a = 
  let i' = Derive i "" Extract in 
  assert(wellformed_id i');
  assert(a = get_info i');
  if (* Flags.extract0 && *) honest i 
  then 
    let s: mref_secret u i = s in 
    match admit() (* Monotonic.RRef.m_read k *) with //17-11-02 ?!
    | Some extract -> extract
    | None -> 
        let extract = create u i' a in 
        //TODO framing 
        // Monotonic.RRef.m_write k extract; 
        extract 
  else 
    let raw = HKDF.extract #(a.ha) s (Hashing.zeroHash a.ha) in 
    assume(honest i' ==> honest i); //17-10-31 TODO with Antoine
    coerce u i' a raw





/// module KeySchedule
/// composing them specifically for TLS

// not sure how to enforce label restrictions, e.g.
// val u_traffic: s:string { s = "ClientKey" \/ s = "ServerKey"} -> ip:ipkg -> pkg ip

let some_keylen: keylen = 32ul
let get_keylen (i:id) = some_keylen

inline_for_extraction
let u_default:  usage info = fun lbl -> Use keylen get_keylen (rp (ii get_keylen)) (fun i a ctx -> some_keylen)

// p:pkg ii & (i:id -> ctx:info i -> j:id & p.use j)  = 

assume val get_aeadAlg: i:id -> aeadAlg 
let derive_aea (lbl:label) (i:id) (a:info) (ctx:context{wellformed_id (Derive i lbl ctx)}):  a': aeadAlg {a' == get_aeadAlg (Derive i lbl ctx)}
=
  //fixme! should be extracted from a
  get_aeadAlg (Derive i lbl ctx)
 
inline_for_extraction
let u_traffic: usage info = 
  fun (lbl:label) -> 
  match lbl with 
  | "ClientKey" | "ServerKey" -> Use aeadAlg get_aeadAlg (mp (ii get_aeadAlg)) (derive_aea lbl)
  | _ -> u_default lbl

// #set-options "--detail_errors"
// #set-options "--print_universes --print_implicits"

let derive_info (lbl:label) (i:id) (a:info) (ctx:context{wellformed_id (Derive i lbl ctx)}): a': info {a' == get_info (Derive i lbl ctx)}
= 
  let Info ha o = a in 
  assume false; //17-11-02 lemma needed?
  match ctx with 
  | ExpandLog log hv -> Info ha (Some (Log log hv))
  | _ -> Info ha o

// 17-10-20 this causes a loop, as could be expected.
inline_for_extraction
let rec u_master_secret (n:nat ): Tot (usage info) (decreases (%[n; 0])) = 
  fun lbl -> match lbl with 
  | "traffic" -> Use info get_info (pp u_traffic) (derive_info lbl)
  | "resumption" -> 
    if n > 0 
    then Use info get_info (pskp (u_early_secret (n-1))) (derive_info lbl)
    else u_default lbl
  | _ -> u_default lbl
and u_handshake_secret (n:nat): Tot (usage info) (decreases (%[n; 1])) =  
  fun lbl -> match lbl with 
  | "traffic" -> Use info get_info (pp u_traffic) (derive_info lbl)
  | "salt" -> Use info get_info (saltp2 (u_master_secret n)) (derive_info lbl)
  | _ -> u_default lbl
and u_early_secret (n:nat): Tot (usage info) (decreases (%[n;2])) = 
  fun lbl -> match lbl with 
  | "traffic" -> Use info get_info (pp u_traffic) (derive_info lbl)
  | "salt" -> Use info get_info (saltp (u_handshake_secret n)) (derive_info lbl)
  | _ -> u_default lbl

/// Tot required... can we live with this integer indexing?
/// One cheap trick is to store a PSK only when it enables resumption.

(* not necessary?
type shape = | 
  | Preshared0: nat 
  | Derive0: shape -> label -> shape

type secret (ui: id -> usage info) (i: id) 
type secret (u: usage info) (ul: label -> usage info) (i: id) 

let pp (#s: shape) (u: usage s info): pkg info (ii get_info) = Pkg 
  (secret s u) 
  secret_len
  (create s u) 
  (coerce s u)

val u_of_i: id -> usage info 

/// We replay the key derivation (in reverse constructor order)
let rec u_of_i i = match i with 
  | Preshared _ _ -> u_early_secret 1
  | Derive i lbl _ -> 
       let u = u_of_i i in 
       let (| info', get_info', pkg', _ |) = u lbl in 
*)       

/// Usability? A mock-up of the TLS 1.3 key schedule.
/// 
/// Although the usage computes everything at each derivation, each
/// still requires 3 type annotations to go through... Can we improve
/// it?

// Testing normalization works for a parametric depth
assume val depth:  n:nat {n > 1} 
let u: usage info = u_early_secret depth 

val ks: unit -> St unit 
let ks() =
  let ipsk: id = Preshared Hashing.Spec.SHA1 0 in
  let a = Info Hashing.Spec.SHA1 None in
  let psk0: psk u ipsk = create_psk ipsk a in
  
  let i0: id = Derive ipsk "" Extract in 
  let early_secret: secret u i0 = extract0 psk0 a in
  let i_traffic0: id = Derive i0 "traffic" Expand in 
  let early_traffic: secret u_traffic i_traffic0 = derive a early_secret "traffic" Expand in  
  let i_0rtt: id = Derive i_traffic0 "ClientKey" Expand in
  let k0: key #(ii get_aeadAlg) i_0rtt = derive a early_traffic "ClientKey" Expand in 
  let cipher  = encrypt k0 10 in 

  let i_salt1: id = Derive i0 "salt" Expand in 
  let salt1:  salt (u_handshake_secret depth) i_salt1 = derive a early_secret "salt" Expand in
  let g = CommonDH.default_group in
  let x = initI g in 
  let gX = CommonDH.pubshare x in
  let (| gY, hs_secret |) = extractR salt1 a g gX in 
  let idh = DHE g gX gY in 
  let i1: id = Derive i_salt1 "" (ExtractDH idh) in 
  let hs_secret: secret (u_handshake_secret depth) i1= hs_secret in 
  let i_traffic1: id = Derive i1 "traffic" Expand  in
  let hs_traffic: secret u_traffic i_traffic1 = derive a hs_secret "traffic" Expand in 
  let k1: key #(ii get_aeadAlg) (Derive i_traffic1 "ServerKey" Expand) = derive a hs_traffic "ServerKey" Expand in 
  let cipher  = encrypt k1 11 in 
  
  let i_salt2: id = Derive i1 "salt" Expand in 
  let salt2: salt (u_master_secret depth) i_salt2 = derive a hs_secret "salt" Expand in 
  let i2: id = Derive i_salt2 "" Extract in 
  let master_secret: secret (u_master_secret depth) i2 = extract2 #(u_master_secret depth) #i_salt2 salt2 a in 
  let i3: id = Derive i2 "resumption" Expand in 
  let rsk: psk (u_early_secret (depth - 1)) i3  = derive a master_secret "resumption" Expand in 
  let i4: id = Derive i3 "" Extract in
  let next_early_secret: secret (u_early_secret (depth -1)) i4 = extract0 rsk a in
  ()


(* --- 

let i3 = Extract0 (Derived i2 "resumption")
let rsk = derive master_secret "resumption" 
// #(u_master_secret depth ) #i2 
val next_early_secret: secret (u_early_secret (depth - 1)) i3 a
let next_early_secret = extract0 rsk


// same, using top-level bindings for debuggability.

let ipsk = Preshared Hashing.Spec.SHA1 0
let a: info ipsk = Info Hashing.Spec.SHA1 None
let psk0: psk #u ipsk  a = create_psk ipsk a

let i0 = Derive ipsk "" Extract
let a0 = Info #i0 Hashing.Spec.SHA1 None
let early_secret: secret u i0 a0 = extract0 psk0 

let i_traffic0 = Derive i0 "traffic" Expand 
let a_traffic0 = Info #i_traffic0 Hashing.Spec.SHA1 None
val early_traffic: secret u_traffic i_traffic0 a_traffic0
let early_traffic = derive early_secret "traffic" Expand 
// not sure where to add the loginfo

let i_0rtt = Derive i_traffic0 "ClientKey" Expand
val k0: key #ii i_0rtt AES_GCM256
let k0 = derive early_traffic "ClientKey" Expand 
let cipher  = encrypt k0 10

let i_salt1 = Derive i0 "salt" Expand 
let a_salt1 = Info #i_salt1 Hashing.Spec.SHA1 None
val salt1:  salt (u_handshake_secret depth) i_salt1 a_salt1 
let salt1  = derive early_secret "salt" Expand


let g = CommonDH.default_group
//let x: CommonDH.sh = initI g 
let x = CommonDH.keygen g 
let gX = CommonDH.pubshare x
let gY: CommonDH.share g = admit()
let dhe_id: id_dhe = Some (| g, gX, gY |)

let i1 = Extract1 (Derived i0 "salt") dhe_id

// we really need [let u_extract1 = u_handshake_secret depth] to go past this point. 

val hs_secret : secret (u_handshake_secret depth) i1 a
let hs_secret = extractI salt1 g x gY

val hs_traffic: secret u_traffic (Derived i1 "traffic") a
let hs_traffic = derive hs_secret "traffic"

val k1: key #ii (Derived (Derived i1 "traffic") "ServerKey") AES_GCM256
let k1 = derive hs_traffic "ServerKey" 
let cipher' = encrypt k1 11

val salt2:  salt ii (u_master_secret depth) (Derived i1 "salt") a
let salt2  = derive hs_secret "salt"

let i2 = Extract2 (Derived i1 "salt")  
val master_secret: secret (u_master_secret depth) i2 a
let master_secret = extract2 salt2 

val rsk: psk #ii #(u_early_secret (depth - 1)) (Derived i2 "resumption") a

let i3 = Extract0 (Derived i2 "resumption")
let rsk = derive master_secret "resumption" 
// #(u_master_secret depth ) #i2 
val next_early_secret: secret (u_early_secret (depth - 1)) i3 a
let next_early_secret = extract0 rsk

/// Proof?  Typing against plain, multi-instance assumptions for each
/// algorithm (including the KDFs)---once an instance is created at
/// the right index, we don't care about its generation.
///
/// Informally, we can explain it as a game against an adversary that tries to
/// distinguish between KDFs with oracle access to create_psk, derive,
/// and (all) coerce functions.
///
/// Idea: use an intermediate multi-instance PRF, then complete the
/// proof by typing. The main problem is to move around the fresh
/// random sampling...
///
/// Underlying functionality: create takes explicit random input
/// idealizes (at most) when its input is freshly sampled.
///
/// real: at creation-time, 
/// table: label -> 
/// 
/// - how to benefit from the create post-condition? explicit? 
/// 

 
// let k0 = create_psk 0 //: secret (u depth) ii (Secret 0) = create (u depth) ii (Secret 0)
// let i1 = Derived (Preshared 0) "secret" (* this seems to help normalization *)
// let k1: secret (u (depth-1)) ii i1  = derive k0 "secret" 
// let k2: key #ii (Derived i1 "aead") = derive k1 "aead" 
// let cipher  = encrypt k2 42
// let k3: list nat  = derive k1 "raw"
//
// let k1' = derive k0 "secret" 
// let k2' = derive #(u 22)  k1'  "aead"  // the type is not normalized; the key is not usable.

--- *)
