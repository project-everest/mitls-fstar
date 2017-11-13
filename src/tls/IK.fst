module IK

/// Standalone experiment modelling key extraction and key derivation
/// parametrized by a usage function from labels to derived keyed
/// functionalities.
///
/// * captures resumption derivations via bounded-recursive instantiation.
/// * captures PRF-ODH double game
/// * applied to the full extract/expand key schedule of TLS 1.3
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility on hash algorithms and DH groups, and ideal-only indexes.
///
/// We plan to split this file into many modules, as planned on slack.
///
/// Not done yet:
///
/// * mysterious typing errors (see comments)
///
/// * define/review all idealization flags. How are they accessed?
///
/// * reliance on u_of_i in DH extraction (intuitive but hard to code)
///
/// * key registration and discretionary compromise
///
/// * extraction: ensure all strongly-dependent types disappear and
///   (concretely) the key schedule directly allocates all key
///   instances.
///
/// * deal with create/coerce stateful pre- and post-condition.
///
/// * usage restriction for KDFs, based on a generalization of wellformed_id
///   (starting with an example of hashed-log derivation)
///
/// Note also that we support rather static agility and usages; while
/// this is sufficient for TLS, we might enable more details to be
/// bound at derivation-time as part of the derivation context.

open FStar.HyperStack
open FStar.HyperStack.ST

module MM = FStar.Monotonic.Map
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

let model = Flags.model

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
  r: MR.rid ->
  get_info: (t -> info) ->
  honest: (i:t -> GTot Type0) ->
  corrupt: (i:t -> GTot Type0) ->
  get_honest: (i:t -> ST bool
    (requires (fun _ -> True))
    (ensures (fun h0 b h1 -> h0 == h1
      /\ (b ==> honest i) /\ (not b ==> corrupt i)))) ->
  ipkg info

/// Keyed functionality define Key packages, parametric in their
/// indexes, but concrete on their key randomness; instances may have
/// any number of other functions (such a leak, for instance).

/// Derived key length restriction when using HKDF
type keylen = l:UInt32.t {UInt32.v l <= 256}

// got into trouble using a type abbreviation [a:info{a == ip.get_info i}]; retry later; NS-11/03: Didn't understand this remark

noeq type pkg (info: Type0) (ip: ipkg info) = | Pkg:
  key: (ip.t -> Type0) ->
  len: (info -> keylen) ->
  ideal: Type0 -> // Type-level access to the ideal flag of the package
  create: (
    i:ip.t -> a:info{a == ip.get_info i} -> ST (key i)
    (requires fun h0 -> model)
    (ensures fun h0 p h1 -> True)) ->
  coerce: (
    i:ip.t -> a:info{a == ip.get_info i} -> lbytes (len a) -> ST (key i)
    (requires fun h0 -> ideal ==> ip.corrupt i)
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

assume val flag_Key: bool
type idealKey = b2t flag_Key

type keyrepr a = lbytes (aeadLen a)
assume new type key (#ip: ipkg aeadAlg) (i: ip.t) // abstraction required for indexing
assume val create_key: #ip: ipkg aeadAlg -> i: ip.t -> a:aeadAlg {a == ip.get_info i} ->
  ST (key i)
    (requires fun h0 -> model)
    (ensures fun h0 p h1 -> True)

assume val coerce_key: #ip: ipkg aeadAlg -> i: ip.t -> a:aeadAlg {a == ip.get_info i} -> keyrepr a ->
  ST (key i)
    (requires fun h0 -> idealKey ==> ip.corrupt i)
    (ensures fun h0 p h1 -> True)

let mp (ip:ipkg aeadAlg): pkg aeadAlg ip = Pkg
  key
  aeadLen
  idealKey
  create_key
  coerce_key

val encrypt: #ip:ipkg aeadAlg -> #i:ip.t -> k: key i -> nat -> nat
let encrypt #ip #i k v = v + 1

/// --------------------------------------------------------------------------------------------------
/// module Raw
/// a default functionality (no idealization);
/// for modelling, we could also provide a "leak" function

assume val flag_Raw: bool
type idealRaw = b2t flag_Raw

type raw  (#ip: ipkg keylen) (i: Idx?.t ip) = lbytes (ip.get_info i)
let create_raw (#ip: ipkg keylen) (i: ip.t) (len:keylen {len = ip.get_info i})
  : ST (raw  i) (requires fun h0 -> model) (ensures fun h0 p h1 -> True) =
  sample len
let coerce_raw (#ip: ipkg keylen) (i: ip.t) (len:keylen {len = ip.get_info i}) (r:lbytes len)
  : ST (raw i) (requires fun h0 -> idealRaw ==> ip.corrupt i)
  (ensures fun h0 p h1 -> True) = r

let rp (ip:ipkg keylen): pkg keylen ip = Pkg
  raw
  (fun n -> n)
  idealRaw
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
  | NoIDH
  | IDH:
    gX: CommonDH.dhi ->
    gY: CommonDH.dhr gX -> id_dhe

// The "ciphersuite hash algorithms"  eligible for TLS 1.3 key derivation.
// We will be more restrictive.
type kdfa = Hashing.Spec.alg

/// Runtime key-derivation parameters, to be adjusted.
///
/// HKDF defines an injective function from label * context to bytes, to be used as KDF indexes.
///
type context =
  | Extract: context // TLS extractions have no label and no context; we may separate Extract0 and Extract2
  | ExtractDH: v:id_dhe -> context // This is Extract1 (the middle extraction)
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
/// we will enforce
/// * consistency on the hash algorithm
/// * monotonicity of the log infos (recursively including earlier resumption logs).
/// * usage restriction: the log after DH must include the DH identifier of the parent.
///   (Hence, we should either forbid successive DHs or authenticate them all.)
///
val wellformed_id: pre_id -> Type0
let rec wellformed_id = function
  | Preshared a _ -> True
  | Derive i l (ExpandLog info hv) -> wellformed_id i /\ digest_info (ha_of_id i) info hv
  | Derive i lbl ctx ->
      //TODO "ctx either extends the parent's, or includes its idh" /\
      wellformed_id i

type id = i:pre_id {wellformed_id i}

type honest_idh (c:context) =
  ExtractDH? c /\ IDH? (ExtractDH?.v c) /\
  (let ExtractDH (IDH gX gY) = c in CommonDH.honest_dhr gY)

// ADL: we use a global honesty table for all indexes
// Inside ipkg, we assume all index types are defined in the table below
// We assume write access to this table is public, but the following global
// invariant must be enforced: if i is corrupt then all indexes derived from i
// are also corrupt - EXCEPT if ctx is ExtractDH g gx gy with CommonDH.honest_dhr gy
let honest_region:MR.rid = new_region HH.root
type honesty_invariant (m:MM.map' id (fun _ -> bool)) =
  (forall (i:id) (l:label) (c:context{wellformed_id (Derive i l c)}).
  {:pattern (m (Derive i l c))}
  Some? (m (Derive i l c)) ==> Some? (m i) /\
  (m i = Some false ==> (honest_idh c \/ m (Derive i l c) = Some false)))

private type i_honesty_table =
  MM.t honest_region id (fun (t:id) -> bool) honesty_invariant
private let h_table = if model then i_honesty_table else unit

let honesty_table: h_table =
  if model then
    MM.alloc #honest_region #id #(fun _ -> bool) #honesty_invariant
  else ()

// Registered is monotonic
type registered (i:id) =
  (if model then
    let log : i_honesty_table = honesty_table in
    MR.witnessed (MM.defined log i)
  else True)

type regid = i:id{registered i}

type honest (i:regid) =
  (if model then
    let log : i_honesty_table = honesty_table in
    MR.witnessed (MM.contains log i true)
  else False)

type corrupt (i:regid) =
  (if model then
    let log : i_honesty_table = honesty_table in
    MR.witnessed (MM.contains log i false)
  else True)

// ADL: difficult to prove, see CommonDH for details
let lemma_honest_corrupt (i:regid)
  : Lemma (honest i <==> ~(corrupt i)) =
  admit()

let lemma_corrupt_invariant (i:regid) (lbl:label)
  (ctx:context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)})
  : ST unit
  (requires fun h0 -> ~(honest_idh ctx))
  (ensures fun h0 _ h1 ->
    corrupt i ==> corrupt (Derive i lbl ctx) /\ h0 == h1)
  =
  lemma_honest_corrupt i;
  lemma_honest_corrupt (Derive i lbl ctx);
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    match MM.lookup log i with
    | Some true -> ()
    | Some false ->
      let m = MR.m_read log in
      // No annotation, but the proof relies on the global log invariant
      MR.testify (MM.defined log (Derive i lbl ctx));
      MM.contains_stable log (Derive i lbl ctx) false;
      MR.witness log (MM.contains log (Derive i lbl ctx) false)
  else ()

let get_honest (i:regid) : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> h0 == h1
    /\ (b <==> honest i) /\ (not b <==> corrupt i))
  =
  lemma_honest_corrupt i;
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    match MM.lookup log i with
    | Some b -> b
  else false

// TODO(adl) preservation of the honesty table invariant
let rec lemma_honesty_update (m:MM.map id (fun _ -> bool) honesty_invariant)
  (i:regid) (l:label) (c:context{wellformed_id (Derive i l c)})
  (b:bool{b <==> honest i /\ not b <==> corrupt i})
  : Lemma (honesty_invariant (MM.upd m (Derive i l c) b))
  = admit()

let register_derive (i:regid) (l:label) (c:context{wellformed_id (Derive i l c)})
  : ST (regid * bool)
  (requires fun h0 -> True)
  (ensures fun h0 (i', b) h1 ->
    modifies_one honest_region h0 h1
    /\ (i' == Derive i l c)
    /\ (b2t b <==> honest i')
    /\ (not b <==> corrupt i'))
  =
  let i':id = Derive i l c in
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    match MM.lookup log i' with
    | Some b -> lemma_honest_corrupt i'; (i', b)
    | None ->
      let b = get_honest i in
      let h = get () in
      lemma_honesty_update (MR.m_sel h log) i l c b;
      MM.extend log i' b;
      lemma_honest_corrupt i';
      (i', b)
  else (i', false)

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

let ii (#info:Type0) (get_info: id -> info) =
  Idx regid honest_region get_info honest corrupt get_honest

/// Try out on examples: we may need a stateful invariant of the form
/// "I have used this secret to create exactly these keys".


/// We expect this function to be fully applied at compile time,
/// returning a package and a algorithm-derivation function to its
/// agility parameter (to be usually applied at run-time).
///

/// ADL: PROPOSED CHANGE (09/11/17)
/// ===================================================================================
/// We propose to encode the idealization order of packages inside the usage function
/// Namely, for all labels, the associated derived package can only be ideal if
/// its parent is ideal. This condition will be checked when the packages are created
/// (the packager must provide a flag that satisfies this condition), after the
/// derivation tree is fixed.
/// ===================================================================================
/// noeq type range (info: Type0) (lbl:label) (ideal: Type0) = | Use:
///     info': Type0 ->
///     get_info': (id -> info') ->
///     pkg': pkg info' (ii #info' get_info'){pkg'.ideal ==> ideal} ->
///     derive: (i: id -> a: info -> ctx: context {wellformed_id (Derive i lbl ctx)} -> a': info' {a' == get_info' (Derive i lbl ctx)}) ->
///     range info lbl
///
/// type usage (info: Type0) = (| ideal:Type0 & lbl: label -> (* compile-time *) range info lbl parent_ideal |)
/// ===================================================================================

noeq type range (info: Type0) (lbl:label) = | Use:
    info': Type0 ->
    get_info': (id -> info') ->
    pkg': pkg info' (ii #info' get_info') ->
    derive: (i: id -> a: info -> ctx: context {wellformed_id (Derive i lbl ctx)} -> a': info' {a' == get_info' (Derive i lbl ctx)}) ->
    range info lbl

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

assume val flag_KDF: b:bool{b ==> model}
type idealKDF = b2t flag_KDF

// Note that when model is off, safeKDF is False and corruptKDF is True
type safeKDF (i:regid) = idealKDF /\ honest i
type corruptKDF (i:regid) = idealKDF ==> corrupt i

type details (ha:kdfa) = | Log:
  loginfo: TLSInfo.logInfo ->
  hv: Hashing.Spec.anyTag {digest_info ha loginfo hv} -> details ha

type info = | Info:
  ha:kdfa ->
  option (details  ha) -> info

// TODO find a nice way to express the idealization ordering
assume val lemma_ideal_order: u:usage info -> lbl:label
  -> Lemma (let use = u lbl in use.pkg'.ideal ==> idealKDF)

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
  (i: regid)
  (lbl: label)
  (c: context {wellformed_id (Derive i lbl c) /\ registered (Derive i lbl c)})
=
  let use = u lbl in
  let i' = Derive i lbl c in
  use.pkg'.key i'

let there: MR.rid = admit()

/// key-derivation table (memoizing create/coerce)
type domain (i:regid) = | Domain:
  lbl: label ->
  ctx: context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)} -> domain i

type ideal_or_real (it:Type0) (rt:Type0) =
  | Ideal: v:it -> ideal_or_real it rt
  | Real: v:rt -> ideal_or_real it rt

unfold type ir_key (safe: regid -> GTot Type0) (it:Type0) (rt:Type0) (i:regid) =
  (if model then
    s:ideal_or_real it rt{safe i <==> Ideal? s}
  else rt)

private type table
  // (ip: ipkg)
  (u: usage info)
  (i: regid)
= MM.t there (domain i) (fun (Domain lbl ctx) -> derived_key u i lbl ctx) (fun _ -> True)

let secret_len (a: info): keylen = UInt32.uint_to_t (Hashing.Spec.tagLen a.ha)
type real_secret (i:regid) = lbytes (secret_len (get_info i))

type secret (u: usage info) (i:regid) =
  ir_key safeKDF (table u i) (real_secret i) i

// when to be parametric on ip? not for the KDF itself: we use ip's constructors.
//type secret (u: usage info) (i:regid) =
//  (if honest i then table u i
//  else lbytes (secret_len (get_info i)))

let secret_ideal (#u: usage info) (#i: regid) (t: secret u i {safeKDF i}): table u i =
  let t : s:ideal_or_real (table u i) (real_secret i) {safeKDF i <==> Ideal? s} = t in
  Ideal?.v t

let ideal_secret (#u: usage info) (#i: regid) (t: table u i {safeKDF i}) : secret u i =
  let t : s:ideal_or_real (table u i) (real_secret i) {safeKDF i <==> Ideal? s} = Ideal t in
  assert(model); t

let secret_corrupt (#u: usage info) (#i: regid) (t: secret u i {corruptKDF i}): real_secret i =
  if model then
   let t : s:ideal_or_real (table u i) (real_secret i) {safeKDF i <==> Ideal? s} = t in
   (lemma_honest_corrupt i; Real?.v t)
  else t

let corrupt_secret (#u: usage info) (#i: regid) (t: real_secret i {corruptKDF i}) : secret u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (table u i) (real_secret i) {safeKDF i <==> Ideal? s} = Real t in s)
  else t

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).

/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.
///
/// MK: what does reverse-inline of low-level KeyGen mean?

val coerce:
  u: usage info ->
  i: regid ->
  a: info {a == get_info i} (* run-time *) ->
  repr: lbytes (secret_len a) ->
  ST (secret u i)
  (requires fun h0 -> idealKDF ==> corrupt i)
  (ensures fun h0 p h1 -> True)
let coerce u i a repr = corrupt_secret #u #i repr

/// NS:
/// MM.alloc is a stateful function with all implicit arguments
/// F* will refuse to instantiate all those arguments, since implicit
/// instantiation in F* should never result in an effect.
///
/// Stateful functions always take at least 1 concrete argument.
///
/// I added a unit here
///
/// CF: Ok; I did not know. Is it a style bug in FStar.Monotonic.Map ?
let alloc (#r:FStar.Monotonic.RRef.rid) #a #b #inv (u:unit)
  : ST (MM.t r a b inv)
       (requires (fun h -> inv (MM.empty_map a b)))
       (ensures (fun h0 x h1 ->
    inv (MM.empty_map a b) /\
    ralloc_post r (MM.empty_map a b) h0 (FStar.Monotonic.RRef.as_hsref x) h1))
  = MM.alloc #r #a #b #inv

val create:
//ip: ipkg ->
  u: usage info ->
  i: regid ->
  a: info {a == get_info i}(* run-time *) ->
  ST (secret u i)
  (requires fun h0 -> model)
  (ensures fun h0 r h1 -> True)
let create u i a =
  let honest = get_honest i in
  if flag_KDF && honest then
    let t : table u i = MM.alloc #there #(domain i) #(fun (Domain lbl ctx) -> derived_key u i lbl ctx) #(fun _ -> True) in
    ideal_secret t
  else
    corrupt_secret #u #i (sample (secret_len a))

/// We are using many KDF packages (one for each usage),
/// idealized one at a time.  (Having one proof step for each nested
/// level of key derivation seems unavoidable: we need to idealize
/// parents before childrens.)

let pp (* ip:ipkg *) (u: usage info): pkg info (ii get_info) = Pkg
  (secret u)
  secret_len
  idealKDF
  (create u)
  (coerce u)

let ukey (u:usage info) (lbl:label) (i':regid) =
  let use = u lbl in
  use.pkg'.key i'

/// The well-formedness condition on the derived label (opaque from
/// the viewpoint of the KDF) enforces
///
inline_for_extraction
val derive:
  #u: usage info ->
  #i: regid ->
  a: info {a == get_info i} ->
  k: secret u i ->
  lbl: label ->
  ctx: context {~(honest_idh ctx) /\ wellformed_id (Derive i lbl ctx)} ->
  ST (_:unit{registered (Derive i lbl ctx)} & ukey u lbl (Derive i lbl ctx))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True
    // modifies our own local state and whatever create/coerce modifies
    // no need to track the ideal state
  )

let derive #u #i a k lbl ctx =
  // register (Derive i lbl ctx) and return its honesty (defaults to get_honest i)
  let honest = get_honest i in
  let i', honest' = register_derive i lbl ctx in
  lemma_corrupt_invariant i lbl ctx;
  let x = Domain lbl ctx in
  let use = u lbl in
  lemma_ideal_order u lbl; // TODO(adl) get the idealization order condition from (u lbl) above
  let a' = use.derive i a ctx in
  if flag_KDF && honest
  then
    let v: option (derived_key u i lbl ctx) = MM.lookup (secret_ideal k) x in
    match v with
    //17-10-30 was failing with scrutiny error: match MM.lookup (secret_ideal k) x
    | Some dk -> (| (), dk |)
    | None ->
      let dk = use.pkg'.create i' a' in
      //17-10-20 TODO framing across create
      let h = get() in
      assume(MM.fresh (secret_ideal k) x h); // FIXME(adl)!!
      MM.extend (secret_ideal k) x dk;
      (| (), dk |)
  else
    let raw =
      HKDF.expand #(a.ha) (secret_corrupt k) (Platform.Bytes.abytes lbl) (UInt32.v (use.pkg'.len a')) in
    let dk = use.pkg'.coerce i' a' raw in
    (| (), dk |)

/// Outlining a global KDF state invariant, supported by package
/// definition tables for all derivable functionalities.
///
/// for all (i: id) (lbl) (ctx).
///   let i' = Derive lbl ctx in
///   wellformed_id i' ==>
///   let u = u_of_i i in
///   let pkg',... = u lbl in
///   match KDF.lookup i with
///   | None -> None? pkg'.lookup i' // used when creating PRFs
///   | Some k -> pkg'.lookup i' == lookup k (Domain lbl ctx) // used when extending PRFs.
///
/// The invariant is restored by the time derive return.
/// (note we implicitly rely on u_of_i)


/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

/// key-derivation table (memoizing create/coerce)

assume val ssa: #a:Type0 -> Preorder.preorder (option a)

assume val flag_KEF0: b:bool{b ==> model /\ flag_KDF ==> b}
type idealKEF0 = b2t flag_KEF0
assume val lemma_kdf_kef0: unit -> Lemma (idealKDF ==> idealKEF0)

let safeKEF0 (i:regid) = idealKEF0 /\ honest i
let corruptKEF0 (i:regid) = idealKEF0 ==> corrupt i

// memoizing a single extracted secret
private type mref_secret (u: usage info) (i: regid) =
  MR.m_rref there (option (secret u i)) ssa

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
type psk (u: usage info) (i: regid) =
  ir_key safeKEF0 (mref_secret u i) (real_secret i) i

let psk_ideal (#u: usage info) (#i:regid) (p:psk u i {safeKEF0 i}): mref_secret u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = p in
  Ideal?.v t

let ideal_psk (#u: usage info) (#i:regid) (t: mref_secret u i{safeKEF0 i}) : psk u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = Ideal t in
  assert(model); t

let psk_real (#u: usage info) (#i:regid) (p:psk u i {corruptKEF0 i}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = p in
    Real?.v t
  else p

let real_psk (#u: usage info) (#i:regid) (t: real_secret i{corruptKEF0 i}) : psk u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = Real t in s)
  else t

type ext0 (u:usage info) (i:regid) =
  _:unit{registered (Derive i "" Extract)} & psk u (Derive i "" Extract)

val coerce_psk:
  #u: usage info ->
  i: regid ->
  a: info {a == get_info i} ->
  raw: lbytes (secret_len a) ->
  ST (ext0 u i)
  (requires fun h0 -> idealKEF0 ==> corrupt i)
  (ensures fun h0 p h1 -> (*TBC*) True)

let coerce_psk #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_psk #u #i' raw |)

val create_psk:
  #u: usage info ->
  i: regid ->
  a: info {a == get_info i} ->
  ST (ext0 u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
let create_psk #u i a =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF0 && honest' then
    let t' = secret u i' in
    let r: mref_secret u i' = MR.m_alloc #(option t') #(ssa #t') there None in
    (| (), ideal_psk #u #i' r |)
  else
    (| (), real_psk #u #i' (sample (secret_len a)) |)

let pskp (*ip:ipkg*) (u:usage info): pkg info (ii get_info) = Pkg
  (ext0 u)
  secret_len
  idealKEF0
  create_psk
  coerce_psk

/// HKDF.Extract(key=0, materials=k) idealized as a (single-use) PRF,
/// possibly customized on the distribution of k.
val extract0:
  #u: usage info ->
  #i: regid ->
  k: ext0 u i ->
  a: info {a == get_info i} ->
  ST
    (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract0 #u #i k a =
  let (| _, p |) = k in
  let i':regid = Derive i "" Extract in
  let honest' = get_honest i' in
  lemma_kdf_kef0 (); // idealKDF ==> idealKEF0
  if flag_KEF0 && honest'
  then
    let k: mref_secret u i' = psk_ideal p in
    match MR.m_read k with
    | Some extract -> extract
    | None ->
      let extract = create u i' a in
      let mrel = ssa #(secret u i') in
      let () =
        MR.m_recall k;
        let h = get() in
        assume (MR.m_sel h k == None); // TODO framing of call to create
        assume (mrel None (Some extract)); // TODO Fix the monotonic relation
        MR.m_write k (Some extract) in
      extract
  else
    let k = psk_real p in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
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

assume val flag_PRF1: b:bool{flag_KDF ==> b /\ b ==> model /\ flag_KEF0 ==> b}
let idealPRF1 = b2t flag_PRF1
let lemma_kdf_prf1 () : Lemma (idealKDF ==> idealPRF1) = admit()

type safePRF1 (i:regid) = idealPRF1 /\ honest i
type corruptPRF1 (i:regid) = idealPRF1 ==> corrupt i

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
  idealPRF1
  create_salt
  coerce_salt

/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-step
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.

/// two flags; we will idealize ODH first
assume val flag_ODH: b:bool { (flag_PRF1 ==> b) /\ (b ==> model)}
type idealODH = b2t flag_ODH

type safeODH (i:regid) = idealODH /\ honest i
type corruptODH (i:regid) = idealODH ==> corrupt i

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
assume val prf_leak:
  #u: usage info ->
  #i: regid ->
  #a: info {a == get_info i} ->
  s: salt u i {idealPRF1 ==> corrupt i} ->
  Hashing.Spec.hkey a.ha

type ext1 (u:usage info) (i:regid) (idh:id_dhe) =
  _:unit{registered (Derive i "" (ExtractDH idh))} & secret u (Derive i "" (ExtractDH idh))

val prf_extract1:
  #u: usage info ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  idh: id_dhe{~(honest_idh (ExtractDH idh))} ->
  gZ: bytes ->
  ST (ext1 u i idh)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> True)

let prf_extract1 #u #i a s idh gZ =
  let j, honest' = register_derive i "" (ExtractDH idh) in
  lemma_corrupt_invariant i "" (ExtractDH idh);
  let honest = get_honest i in
  lemma_kdf_prf1 ();
  if flag_PRF1 && honest
  then
    (* TBD: memoization
    let w =
      // "wide" PRF, memoized on gZ
      match find s.wide gZ with
      | Some w -> w // may return k
      | None ->
        let w = pkg.create0 j a in
        s.wide := snoc s.wide w;
        w in  *)
    (| (), create u j a |)
    // agreement on the algorithms follows from the salt.
  else
    let raw_salt = prf_leak #u #i #a s in
    let raw = HKDF.extract raw_salt gZ (* narrow, concrete *) in
    (| (), coerce u j a raw |)

/// ODH (precisely tracking the games, not yet code-complete
/// --------------------------------------------------------------------------------------------------

// Ideally, we maintain a monotonic map from every honestly-sampled
// initiator share gX to its set of honestly-sampled responders shares
// (i,gY).
// The table exists when [Flags.ideal_KDF], a precondition for [flag_odh]

// We need a variant of FStar.Monotonic.Map that enables monotonic updates to
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

type odhid = x:CommonDH.dhi{CommonDH.registered_dhi x}

type peer_index (x:odhid) =
  i:regid & y:CommonDH.dhr x {CommonDH.registered_dhr y /\ registered (Derive i "" (ExtractDH (IDH x y)))}

type peer_instance (#x:odhid) (iy:peer_index x) =
  secret (u_of_i (dfst iy)) (Derive (dfst iy) "" (ExtractDH (IDH x (dsnd iy))))

let peer_table (x:odhid): Type0 =
  MM.t there (peer_index x) (peer_instance #x) (fun _ -> True)
type odh_table = MM.t there odhid peer_table (fun _ -> True)

let odh_state : (if model then odh_table else unit) =
  if model then MM.alloc #there #odhid #peer_table #(fun _ -> True)
  else ()

type odh_fresh (i:odhid) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    MM.fresh log i h
  else True)

let lemma_fresh_odh (i:CommonDH.dhi) (h:mem)
  : Lemma (CommonDH.fresh_dhi i h ==> odh_fresh i h)
  = admit () // i:dhi implies registered_dhi i and registered_dhi i /\ fresh_dhi i h ==> False

let lemma_fresh_odh_framing (i:CommonDH.dhi) (h0:mem) (h1:mem)
  : Lemma (odh_fresh i h0 /\ modifies_one CommonDH.dh_region h0 h1 ==> odh_fresh i h1)
  = admit() // assume(HH.disjoint there CommonDH.dh_region)

type odh_defined (i:odhid) =
  (if model then
    let log : odh_table = odh_state in
    MR.witnessed (MM.defined log i)
  else True)

type odhr_fresh (#i:odhid) (r:peer_index i) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    (match MM.sel (MR.m_sel h log) i with
    | Some t ->
      (match MM.sel (MR.m_sel h t) r with
      | None -> True
      | _ -> False)
    | _ -> False)
  else True)

let lemma_fresh_dhr (#i:odhid) (r:peer_index i) (h:mem)
  : Lemma (CommonDH.fresh_dhr (dsnd r) h ==> odhr_fresh r h)
  = admit () // contradition on  CommonDH.registered_dhr y

let lemma_fresh_dhr_framing (#i:odhid) (r:peer_index i) (h0:mem) (h1:mem)
  : Lemma (odhr_fresh r h0 /\ modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton honest_region)) h0 h1 ==> odhr_fresh r h1)
  = admit() // assume(HH.disjoint there CommonDH.dh_region)

/// Client-side instance creation
/// (possibly used by many honest servers)
val odh_init: g: CommonDH.group -> ST (CommonDH.ikeyshare g)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    let gx : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton there)) h0 h1
    /\ model ==> (odh_fresh gx h0 /\ odh_defined gx /\ CommonDH.honest_dhi gx))

let odh_init g =
  let h0 = get () in
  let x = CommonDH.keygen g in
  let h1 = get () in
  if model then
   begin
    let log : odh_table = odh_state in
    let i : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    lemma_fresh_odh i h0;
    lemma_fresh_odh_framing i h0 h1;
    assert(MM.sel (MR.m_sel h1 log) i == None);
    let peers : peer_table i = MM.alloc #there #(peer_index i) #(peer_instance #i) #(fun _ -> True) in
    let h2 = get () in
    assume(MM.sel (MR.m_sel h2 log) i == None); // FIXME allocate peers somewhere else !!
    MM.extend log i peers;
    assume(MR.stable_on_t log (MM.defined log i));
    MR.witness log (MM.defined log i)
   end;
  x

// TODO crypto agility: do we record keygen as honest for a bad group?

/// Server-side creation and completion
///
/// An elaboration of "derive" for two-secret extraction
/// - kdf is the child KDF package.
/// - HKDF is the concrete algorithm
///
/// We require that gX be the share of a honest initiator,
/// but not that they agree on the salt index

private let register_odh (i:regid) (gX:CommonDH.dhi) (gY:CommonDH.dhr gX)
  : ST (j:regid{j == Derive i "" (ExtractDH (IDH gX gY))})
  (requires fun h0 -> model /\ CommonDH.honest_dhr gY)
  (ensures fun h0 _ h1 -> modifies_one honest_region h0 h1)
  =
  let idh = IDH gX gY in
  let ctx = ExtractDH idh in
  assert(honest_idh ctx);
  let j = Derive i "" ctx in // N.B. this is the only case where i can be corrupt and j honest
  let hlog : i_honesty_table = honesty_table in
  MR.m_recall hlog;
  match MM.lookup hlog j with
  | None ->
    let m = MR.m_read hlog in
    assume(honesty_invariant (MM.upd m j true)); // Sepcial case: honest IDH
    MM.extend hlog j true;
    MM.contains_stable hlog j true;
    MR.witness hlog (MM.contains hlog j true); j
  | Some b -> j

val odh_test:
  #u: usage info ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  gX: odhid{odh_defined gX} ->
  ST (j:peer_index gX{dfst j == i} & peer_instance j)
  (requires fun h0 -> model /\ CommonDH.honest_dhi gX)
  (ensures fun h0 r h1 ->
    // todo, as sanity check
    // let (|gY, s|) = dfst r in
    // flag_odh ==> s == peer_gX gY
    True)

let odh_test #u #i a s gX =
  assume (u == u_of_i i); //17-11-01 TODO modelling
  (* we get the same code as in the game by unfolding dh_responder, e.g.
  let y = CommonDH.keygen g in
  let gY = CommonDH.pubshare y in
  let gZ: bytes (*CommonDH.share g*) = ... in  // used only when (not flag_odh)
  *)
  let h0 = get() in
  let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
  let j = register_odh i gX gY in
  let j' : peer_index gX = (| i, gY |) in
  let h1 = get() in
  lemma_fresh_dhr j' h0;
  lemma_fresh_dhr_framing j' h0 h1;
  assert(odhr_fresh j' h1);
  assert(a == get_info j);
  let k: secret u j =
    if flag_ODH then create u j a (* narrow *)
    else (
      assert(~idealPRF1);
      let raw = HKDF.extract #a.ha (prf_leak s) gZ (* wide, concrete *) in
      assume(~idealKDF); // FIXME(adl): fix the loop in the flag order dependency. See definition of usage for proposed solution
      coerce u j a raw
    ) in
  let h2 = get() in
  assume(odhr_fresh j' h2); // TODO framing of KDF
  let t: odh_table = odh_state in
  MR.testify(MM.defined t gX);
  let peers = Some?.v (MM.lookup t gX) in
  MM.extend peers j' k;
  (| j' , k |)

unfold let idh_of (#g:CommonDH.group) (x:CommonDH.ikeyshare g) (gY:CommonDH.rshare g (CommonDH.ipubshare x)) =
  IDH (| g, CommonDH.ipubshare x |) gY

// the PRF-ODH oracle, computing with secret exponent x
val odh_prf:
  #u: usage info ->
  #i: regid ->
  a: info {a == get_info i}->
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST (_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))} & secret u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX
    /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
  (ensures fun h0 _ h1 -> True)

// FIXME. Lemma is false. Not sure how to fix
let lemma_fresh_dhr_hinv (#x:CommonDH.dhi) (y:CommonDH.dhr x) (h:mem)
  : Lemma (requires (model ==> CommonDH.fresh_dhr #x y h))
          (ensures ~(honest_idh (ExtractDH (IDH x y))))
  = admit()

let odh_prf #u #i a s g x gY =
  let h = get () in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let idh = IDH gX gY in
  assert_norm(idh == idh_of x gY);
  lemma_fresh_dhr_hinv #gX gY h;
  let gZ = CommonDH.dh_initiator g x gY in
  let (| uu, k |) = prf_extract1 #u #i a s idh gZ in
  let k' : secret u (Derive i "" (ExtractDH idh)) = k in
  (| (), k' |)


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
  #i: regid ->
  s: salt u i ->
  a: info {a == get_info i} ->
  gX: odhid ->
  ST(i_gY:peer_index gX{dfst i_gY == i} & peer_instance i_gY)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)

let extractR #u #i s a gX =
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
   begin
    let t: odh_table = odh_state in
    (if None? (MM.lookup t gX) then
      let peers = MM.alloc #there #(peer_index gX) #(peer_instance #gX) #(fun _ -> True) in
      let h = get() in
      assume(None? (MM.sel (MR.m_sel h t) gX));
      MM.extend t gX peers;
      assume(MR.stable_on_t t (MM.defined t gX));
      MR.witness t (MM.defined t gX));
    odh_test a s gX
   end
  else
   begin
    // real computation: gY is honestly-generated but the exchange is doomed
    let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
    let idh = IDH gX gY in
    assume(~(honest_idh (ExtractDH idh))); // FIXME
    let (| _ , k |) : ext1 u i idh = prf_extract1 a s idh gZ in
    let k : secret u (Derive i "" (ExtractDH idh)) = k in
    let i_gY : peer_index gX = (| i, gY |) in
    let s : peer_instance #gX i_gY = admit() in
    (| i_gY, s |)
   end

(*)
     let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
     CommonDH.honest_dhi gX /\ odh_defined gX
     /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
*)

/// Initiator computes DH secret material
val extractI:
  #u: usage info ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST(_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))} & secret u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX)
  (ensures fun h0 k h1 -> True)

let extractI #u #i a s g x gY =
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
    let t: odh_table = odh_state in
    MR.testify(MM.defined t gX);
    let peers = Some?.v (MM.lookup t gX) in
    let idh = IDH gX gY in
    let i' = Derive i "" (ExtractDH idh) in
    assume(registered i');
    assert(wellformed_id i);
    assume(wellformed_id i'); //17-11-01 same as above?
    let i_gY : peer_index gX = (| i, gY |) in
    let ot = secret u i' in
    assume (u == u_of_i i); //17-11-01 indexing does not cover u yet
    let o : option ot = MM.lookup peers i_gY in
    match o with
    | Some k -> (| (), k |)
    | None -> assume false; odh_prf #u #i a s g x gY
  else odh_prf #u #i a s g x gY

val extractP:
  #u:usage info ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  ST(_:unit{registered (Derive i "" (ExtractDH NoIDH))} & secret u (Derive i "" (ExtractDH NoIDH)))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let extractP #u #i a s =
  let gZ = Hashing.Spec.zeroHash a.ha in
///17-11-01 stuck on this one too.
//  admit()
   let (| _, k |) = prf_extract1 a s NoIDH gZ in
   assert(registered (Derive i "" (ExtractDH NoIDH)));
   let k : secret u (Derive i "" (ExtractDH NoIDH)) = k in
   (| (), k |)

assume val flag_KEF2: b:bool{flag_KDF ==> b}
type idealKEF2 = b2t flag_KEF2

type safeKEF2 i = idealKEF2 /\ honest i
type corruptKEF2 i = idealKEF2 ==> corrupt i

/// ---------------- final (useless) extraction --------------------
///
type salt2 (u: usage info) (i:regid) =
  ir_key safeKEF2 (mref_secret u i) (real_secret i) i

// same code as for PSKs; but extract0 and extract2 differ concretely

let real_salt2 (#u: usage info) (#i:regid) (t: real_secret i{corruptKEF2 i}) : salt2 u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = Real t in s)
  else t

let salt2_real (#u: usage info) (#i:regid) (p:salt2 u i {corruptKEF2 i}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = p in
    Real?.v t
  else p

type ext2 (u: usage info) (i:regid) =
  _:unit{registered (Derive i "" Extract)} & salt2 u (Derive i "" Extract)

val coerce_salt2:
  #u: usage info ->
  i: regid ->
  a: info {a == get_info i} ->
  raw: lbytes (secret_len a) ->
  ST (ext2 u i)
  (requires fun h0 -> idealKEF2 ==> corrupt i)
  (ensures fun h0 p h1 -> (*TBC*) True)

let coerce_salt2 #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_salt2 #u #i' raw |)

let ideal_salt2 (#u: usage info) (#i:regid) (t: mref_secret u i{safeKEF2 i}) : salt2 u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = Ideal t in
  assert(model); t

let salt2_ideal (#u: usage info) (#i:regid) (p:salt2 u i {safeKEF2 i}): mref_secret u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = p in
  Ideal?.v t

val create_salt2:
  #u: usage info ->
  i: regid ->
  a: info {a == get_info i} ->
  ST (ext2 u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)

let create_salt2 #u i a =
  let i', honest' = register_derive i "" Extract in
  let honest = get_honest i in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF2 && honest' then
    let t' = secret u i' in
    let r: mref_secret u i' = MR.m_alloc #(option t') #(ssa #t') there None in
    (| (), ideal_salt2 #u #i' r |)
  else
    (| (), real_salt2 #u #i' (sample (secret_len a)) |)

let saltp2 (u:usage info): pkg info (ii get_info) = Pkg
  (ext2 u)
  secret_len
  idealKEF2
  create_salt2
  coerce_salt2

/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
/// The salt is used just for extraction, hence [u] here is for the extractee.
/// Otherwise the code is similar to [derive], with different concrete details
val extract2:
  #u: usage info ->
  #i: regid ->
  s: ext2 u i ->
  a: info {a == get_info i} ->
  ST (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract2 #u #i e2 a =
  let (| _, s |) = e2 in
  let i' : regid = Derive i "" Extract in
  let honest' = get_honest i' in
  assert(wellformed_id i');
  assert(a = get_info i');
  assume(idealKDF ==> idealKEF2); // TODO
  if flag_KEF2 && honest' then
    let k: mref_secret u i' = salt2_ideal s in
    match MR.m_read k with
    | Some extract -> extract
    | None ->
        let extract = create u i' a in
        let mrel = ssa #(secret u i') in
        let () =
          MR.m_recall k;
          let h = get() in
          assume (MR.m_sel h k == None); // TODO framing of call to create
          assume (mrel None (Some extract)); // TODO Fix the monotonic relation
          MR.m_write k (Some extract) in
        extract
  else
    let k = salt2_real s in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
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
//NS: Not sure what sort of improvement you're aiming for
//    Can you sketch what you would like to write instead?
//    And why you would expect it to work?
// CF: The comment is out of date: this sample code is simpler than
// one week ago. Still, I would prefer not to have to write the
// intermediate indexes, which are all computable from the usage in
// the caller context and not necessarily useful for the caller.

// Testing normalization works for a parametric depth
assume val depth:  n:nat {n > 1}
let u: usage info = u_early_secret depth

let gen_pskid a : St (n:nat{registered (Preshared a n)}) = admit()

val ks: unit -> St unit
let ks() =
  let pskctr = gen_pskid Hashing.Spec.SHA1 in
  let ipsk: regid = Preshared Hashing.Spec.SHA1 pskctr in
  let a = Info Hashing.Spec.SHA1 None in

  let psk0 : ext0 u ipsk = create_psk ipsk a in
  let i0 : regid = Derive ipsk "" Extract in
  let early_secret : secret u i0 = extract0 psk0 a in

  let (| _, et |) = derive a early_secret "traffic" Expand in
  let i_traffic0 : regid = Derive i0 "traffic" Expand in
  let a_traffic0 = Info Hashing.Spec.SHA1 None in
  let early_traffic : secret u_traffic i_traffic0 = et in

  let (| _, ae0 |) = derive a early_traffic "ClientKey" Expand in
  let i_0rtt : regid = Derive i_traffic0 "ClientKey" Expand in
  let k0 : key #(ii get_aeadAlg) i_0rtt = ae0 in

  let cipher  = encrypt #_ #i_0rtt k0 10 in

  let (| _, s1 |) = derive a early_secret "salt" Expand in
  let i_salt1: regid = Derive i0 "salt" Expand in
  let salt1: salt (u_handshake_secret depth) i_salt1 = s1 in

  let g = CommonDH.default_group in
  let x = initI g in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in

  let (| i_gY, hs1 |) = extractR salt1 a gX in
  let (| _, gY |) = i_gY in
  let i1 : regid = Derive i_salt1 "" (ExtractDH (IDH gX gY)) in
  let hs_secret: secret (u_handshake_secret depth) i1 = admit() in

  let (| _, hst |) = derive a hs_secret "traffic" Expand in
  let i_traffic1: regid = Derive i1 "traffic" Expand  in
  let hs_traffic: secret u_traffic i_traffic1 = hst in

  let (| _, ae1 |) = derive a hs_traffic "ServerKey" Expand in
  let i_1rtt : regid = Derive i_traffic1 "ServerKey" Expand in
  let k1: key #(ii get_aeadAlg) i_1rtt = ae1 in

  let cipher  = encrypt k1 11 in

  let (| _, s2 |) = derive a hs_secret "salt" Expand in
  let i_salt2: regid = Derive i1 "salt" Expand in
  let salt2 : salt2 (u_master_secret depth) i_salt2 = s2 in

  let i2 : regid = Derive i_salt2 "" Extract in
  let master_secret: secret (u_master_secret depth) i2 = extract2 #(u_master_secret depth) #i_salt2 salt2 a in
  let i3: regid = Derive i2 "resumption" Expand in

  let rsk: ext0 (u_early_secret (depth - 1)) i3 = derive a master_secret "resumption" Expand in
  let i4: regid = Derive i3 "" Extract in
  let next_early_secret: secret (u_early_secret (depth - 1)) i4 = extract0 rsk a in
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
