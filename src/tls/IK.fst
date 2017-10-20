module IK 

open FStar.HyperStack
open FStar.HyperStack.ST

/// a standalone experiment modelling key derivation parametrically in
/// the use of the derived keys.
///
/// * captures nested derivations via bounded-recursive instantiation.
/// * applied to an extract/expand schedule (simplified from TLS 1.3)
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility and ideal-only indexes.
///
/// Not done yet: conditional idealization and erasure.

type bytes = Platform.Bytes.bytes
let lbytes (len:UInt32.t) = Platform.Bytes.lbytes (UInt32.v len)
assume val sample: len:UInt32.t -> lbytes len  // not pure!

/// How to deal with agility etc? Key (i:id) (u:usage) where u is
/// concrete, and usually bound to i---in which case it is Ok to
/// select u at derivation-time.
  
/// --------------------------------------------------------------------------------------------------
/// We embed first-class modules as datatype "packages"
///
/// Index packages provide a "safe" predicate to control conditional idealization.
/// We use "honest" to refer to the adversarie's intent, and "safe" for fine-grained idealization,
/// with "safe ==> honest" as a pointwise lemma.
/// When do we need to access one vs the other? Each instance can cache "safe". 
noeq type ipkg = | Idx: 
  t: Type0 -> 
  honest: (t -> bool) ->  
  ipkg

/// Keyed functionality define Key packages, parametric in their
/// indexes, but concrete on their key randomness; instances may have
/// any number of other functions (such a leak, for instance).

/// Derived key length restriction when using HKDF
type keylen = l:UInt32.t {UInt32.v l <= 256} 

noeq type pkg (ip:ipkg) = | Pkg:
  use: Type0 -> 
  key: (ip.t -> use -> Type0) -> 
  len: (use -> keylen) ->
  create: (
    i:ip.t -> u:use -> ST (key i u)
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> True)) -> 
  coerce: (
    i:ip.t -> u:use -> lbytes (len u) -> ST (key i u)
    (requires fun h0 -> ~(ip.honest i))
    (ensures fun h0 p h1 -> True)) ->
  pkg ip

/// pick an ordering: ip.t -> use for now.
///
/// We must ensure a shared `use` for all instances (or only when
/// idealized?); this may follow from static memoization.
/// 
/// Do we want to hardwire that u is a function of i? 

/// --------------------------------------------------------------------------------------------------
/// module AEAD
/// sample agile functionality,

type aeadAlg = | AES_GCM128 | AES_GCM256
val aeadLen: aeadAlg -> keylen 
let aeadLen = function
  | AES_GCM128 -> 32ul
  | AES_GCM256 -> 48ul

type keyrepr a = lbytes (aeadLen a)
assume new type key (#ip: ipkg) (i: ip.t) (a:aeadAlg) // abstraction required for indexing
assume val create_key: #ip: ipkg -> i: ip.t -> a:aeadAlg -> key i a
assume val coerce_key: #ip: ipkg -> i: ip.t -> a:aeadAlg -> keyrepr a -> key i a

let mp (ip:ipkg): pkg ip = 
  Pkg aeadAlg key aeadLen create_key coerce_key

val encrypt: #ip:ipkg -> #i:ip.t -> #a:aeadAlg -> k: key i a -> nat -> nat 
let encrypt #ip #i #a k v = v + 1

/// --------------------------------------------------------------------------------------------------
/// module Raw
/// a default functionality (no idealization);
/// for modelling, we could also provide a "leak" function
///
type raw  (#ip: ipkg) (i: Idx?.t ip) (len:keylen) = lbytes len
let create_raw (#ip: ipkg) (i: ip.t) (len:keylen): raw  i len = sample len
let coerce_raw (#ip: ipkg) (i: ip.t) (len:keylen) (r:lbytes len): raw i len = r
let rp (ip:ipkg): pkg ip = Pkg keylen raw (fun n -> n) create_raw coerce_raw

/// --------------------------------------------------------------------------------------------------
/// module Index

/// We provide an instance of ipkg to track key derivation (here using constant labels)
type label = bytes

/// We expect this function to be fully applied at compile time,
/// returning a package and a algorithm-derivation function to its
/// agility parameter (to be usually applied at run-time).
/// 
type usage (a:Type0) (ip:ipkg) =
  label -> p:pkg ip & (ctx:a -> p.use)

type id_dhe = g: CommonDH.group & gX: CommonDH.share g & CommonDH.share g
type id_psk = nat // external application PSKs only; we may need a special PSK0 constructor too
type id = 
  | Zero // symbolic constant for absent extraction arguments
  | Preshared of id_psk  // external application PSKs only
  | Extract0: materials:id -> id
  | Extract1: salt:id -> materials: id_dhe -> id 
// do we need 2 cases?
//| ExtractWide1: salt:id -> #g: CommonDH.group -> CommonDH.share g -> id // do we need 2 cases?
  | Extract2: salt:id  -> id
  | Derived: id -> label -> id  

// 17-10-17 Discussion with Markulf
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

/// Using different constructors for different constructions; we don't
/// restrict index, but we only provide the key-level operations at
/// specific types.
///
/// TODO: extend Derived to take (and record) an optional hashed digest.
///
/// This form of indexing may be too global, e.g. extractions should
/// not depend on expansion; in principle, we could clip "Extracted"
/// to the extractor index.
///
/// MK: what is meant with "clip 'Extracted' to the extractor index"?

let ii:ipkg = Idx id (fun _ -> true)

/// TODO maintain a monotonic safety table.  and enforce fresh
/// registration at creation/coercion time.
///
/// Try out on examples: we'll need a stateful invariant of the form
/// "I have used this secret to create exactly these keys". 


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
/// 
type kdfa = Hashing.Spec.alg
type info = {ha:kdfa; aea:aeadAlg} (* runtime *) 
//type suse = a:info * usage info ii

let derived_key (u: usage info ii) (i: ii.t) (v:label) (a: info) = 
  let (| pkg', derived_alg |) = u v in 
  pkg'.key (Derived i v) (derived_alg a)

let there: FStar.Monotonic.RRef.rid = admit() 

private type table 
  // (ip: ipkg) 
  (u: usage info ii)
  (i: ii.t) 
  (a: info) 
= MonotoneMap.t there label (fun v -> derived_key u i v a) (fun _ -> True)

let secret_len a = UInt32.uint_to_t (Hashing.Spec.tagLen (a.ha))
 
let lookup   
  (#u: usage info ii)
  (#i: ii.t) 
  (#a: info) 
  (t: table u i a) = MonotoneMap.lookup t 
let extend 
  (#u: usage info ii)
  (#i: ii.t) 
  (#a: info) 
  (t: table u i a) = MonotoneMap.extend t 

// when to be parametric on ip? not for the KDF itself: we use ip's constructors.
let secret 
  // (ip: ipkg) 
  (u: usage info ii)
  (i: ii.t) 
  (a: info) : Type0
=
  if ii.honest i 
  then table u i a
  else lbytes (secret_len a)

let ideal_secret 
  (#u: usage info ii)
  (#i: ii.t { ii.honest i})
  (#a: info)
  (t: table u i a): secret u i a = t 


/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).
 
/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.
///
/// MK: what does reverse-inline of low-level KeyGen mean?

val coerce: 
//ip: ipkg ->
  u: usage info ii ->
  i: ii.t ->
  a: info (* run-time *) -> 
  repr: lbytes (secret_len a) -> 
  ST (secret u i a)
  (requires fun h0 -> ~(ii.honest i))
  (ensures fun h0 p h1 -> True)
let coerce u i a repr = repr

val create: 
//ip: ipkg ->
  u: usage info ii -> 
  i: ii.t ->
  a: info (* run-time *) ->
  ST (secret u i a)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let create u i a = 
  if ii.honest i 
  then 
    //style: how to avoid repeating those parameters?
    MonotoneMap.alloc #there #label #(fun v -> derived_key u i v a) #(fun _ -> True) 
  else 
    coerce u i a (sample (secret_len a)) 

let pp (* ip:ipkg *) (u: usage info ii): pkg ii = Pkg 
  info
  (secret u) 
  secret_len
  (create u) 
  (coerce u)

/// TODO consider separating pp packages more explicitly, so that we
/// can idealize them one at a time. (Having one proof step for each
/// nested level of key derivation seems unavoidable.)


inline_for_extraction
val derive:
  #u: usage info ii ->
  #i: id ->
  #a: info -> 
  k: secret u i a ->
  v: label ->
  ST (derived_key u i v a)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
 
let derive  #u #i #a k v = 
  let (| pkg, derived_alg |) = u v in 
  let a' = derived_alg a in 
  if ii.honest (*safe*) i 
  then
    match MonotoneMap.lookup k v with 
    | Some dk -> dk
    | None -> 
      let dk = pkg.create (Derived i v) a' in 
      MonotoneMap.extend k v dk;
      dk
  else 
    let raw =
      HKDF.expand #(a.ha) k v (UInt32.v (pkg.len a')) in 
    pkg.coerce (Derived i v) a' raw

(*
/// Reconsider packaging: should create take external randomness?

/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
assume type psk 
  (#ip: ipkg) 
  (#u: usage info ip) 
  (i: ip.t) 
  (a:info) 

// ip:ipkg or fixed id?

assume val create_psk: 
  #ip: ipkg -> 
  #u: usage info ip ->
  i: ip.t -> 
  a: info -> 
  psk #ip #u i a

assume val coerce_psk: 
  #ip: ipkg -> 
  #u: usage info ip ->
  i: ip.t -> 
  a: info -> 
  raw: lbytes (secret_len a) -> 
  psk #ip #u i a

let pskp (ip:ipkg) (u:usage info ip): pkg ip = Pkg 
  info 
  psk
  secret_len
  create_psk
  (coerce_psk #ip #u)
  

/// Derived salt; note it is already indexed by the usage of the
/// following extension.
assume type salt (ip:ipkg) (u: usage info ip) (i: ip.t)  (a: info)

assume val create_salt: 
  #ip: ipkg -> 
  #u: usage info ip -> 
  i: ip.t -> 
  a: info -> 
  salt ip u i a

assume val coerce_salt: 
  #ip: ipkg ->
  #u: usage info ip ->
  i: ip.t ->
  a: info -> 
  raw: lbytes (secret_len a) ->
  salt ip u i a

// use instances of the same package for both? 

let saltp1 (ip:ipkg) (u:usage info ip): pkg ip = Pkg 
  info 
  (salt ip u)
  secret_len
  create_salt 
  coerce_salt

let saltp2 (ip:ipkg) (u:usage info ip) : pkg ip = Pkg 
  info 
  (salt ip u)
  secret_len
  create_salt 
  coerce_salt


/// HKDF.Extract(key=0, materials=k) idealized as a single-use PRF,
/// possibly customized on the distribution of k.
assume val extract0:
  #u: usage info ii ->
  #i: id ->
  #a: info ->
  k: psk #ii #u i a -> 
  secret ii u (Extract0 i) a


/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-bit
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.

/// we write prf_ for the middle salt-keyed extraction, conditionally
/// idealized as a PRF keyed by salt1 depending on b1.
/// 
/// its interface provides create, coerce, leak, and extract
/// its internal table memoizes it with *wide* domain gZ 

/// Allocates a 
/// Returns a narrow-indexed key, 
/// 
/// its internal state must ensure sharing
///
val prf_extract1:
  #u: usage info ii -> 
  #i: id ->
  #a: info -> 
  s: salt ii u i a ->
  g: CommonDH.group ->
  gX: CommonDH.share g -> 
  gY: CommonDH.share g ->
  gZ: CommonDH.share.g (* { dh gX gY gZ } *) ->
  secret ii u (Extract1 i (| g, gX, gY |)) a

(*
let prf_extract1 #u #i #a s g gX gY gZ = 
  let idh = (| g, gX, gY |) in
  let j = Extract1 i idh in
  let pkg = pp ii u in 
  if ii.honest i & b1 
  then 
    if b2 then 
    let 
    let w = 
      // "wide" PRF, memoized on gZ
      match find s.wide gZ with 
      | Some w -> w // may return k
      | None -> 
        let w = pkg.create0 j a in
        s.wide := snoc s.wide w;
        w in 
    pkg.narrow j k 
    // agreement on the algorithms follows from the salt.
  else 
    let raw = HKDF.extract (prf_leak s) gZ (* wide, concrete *) in 
    pkg.coerce j a raw 
*)

val prf_leak:
  #u: usage info ii -> 
  #i: id ->
  #a: info -> 
  s: salt ii u i a -> bytes 
// requires ~(honest i)


(*
/// ODH
/// --------------------------------------------------------------------------------------------------

assume val honest_gX: 
  #g: CommonDH.group ->
  gX: CommonDH.share g -> 
  bool 

// ideal state 
// val peer: mref (map gX --> list (i,gY)) 
// - presence codes I[X]
// - contents codes R[X] 
// conversely [keyshare] locally provides  x

/// Client-side instance creation
/// (possibly used by many honest servers)
val odh_init:
  g: CommonDH.group -> St (CommonDH.keyshare g)

let odh_init g = 
  let x = CommonDH.keygen g in 
  let gX = CommonDH.pubshare y in  
  // check gX is fresh;
  // peer[gX] := []
  x // also return gX?

/// Server-side creation and completion
///
/// An elaboration of "derive" for two-secret extraction
/// - kdf is the child KDF package.
/// - HKDF is the concrete algorithm
///
val odh_test:
  #u: usage info ii -> 
  #i: id -> 
  #a: info -> 
  s: salt ii u i a ->
  g: CommonDH.group ->
  gX: CommonDH.share g { honest_gX gX } -> 
  ( gY:CommonDH.share g &
  secret ii u (Extract1 i (| g, gX, gY |)) a )
// requires peer[gX] defined.
// I and R may not share the same salt (i)

let odh_test #u #i #a s g gX = 
  let y = CommonDH.keygen g in 
  let gY = CommonDH.pubshare y in  
  peer[gX] += (i, gY);
  let idh = (| g, gX, gY |) in
  let j = Extract1 i idh in 
  let k = 
    if b0 
    then kdf.create j a (* narrow *)
    else 
      let gZ: commonDH.share g = admit() in 
      let raw = HKDF.extract (prf_leak s) gZ (* wide, concrete *) in 
      kdf.coerce j a raw 
  in
  gY, k (* TODO k is not registered yet *)

// the PRF-ODH oracle, computing with secret exponent x
val odh_prf:
  #u: usage info ii -> 
  #i: id -> 
  #a: info -> 
  s: salt ii u i a ->
  g: CommonDH.group ->
  x: CommonDH.keyshare g { honest_gX (CommonDH.pubshare x) } -> 
  gY: CommonDH.share g -> 
  secret ii u (Extract1 i (| g, CommonDH.pubshare x, gY |)) a 
// requires peer[gX] is defined (witnessed in x) and does not contain (i,gY)
// None? (find (i, gY) !peer[gX])

let odh_prf #u #i #a s g x gY = 
  let gX = CommonDH.pubshare x in
  let gZ: CommonDH.share g = admit() in 
  prf_extract1 s (| g, gX, gY |) gZ 

/// --------------------------------------------------------------------------------------------------
/// Diffie-Hellman shares
/// module Extract1 

// TODO: instead of CommonDH.keyshare g, we need an abstract stateful
// [abstract type private_keyshare g = mref bool ...] that enables
// calling it exactly once

/// Initiator computes DH keyshare, irrespective of the KDF & salt. 
let initI (g:CommonDH.group) = odh_init g 

/// Responder computes DH secret material
assume val extractR:
  #u: usage info ii -> 
  #i: id -> 
  #a: info -> 
  s: salt ii u i a ->
  g: CommonDH.group ->
  gX: CommonDH.share g ->
  ( gY:CommonDH.share g &
  secret ii u (Extract1 i (| g, gX, gY |)) a )

let extractR #u #i #a s g gX = 
  if honest_gX gX 
  then ODH_test gX i
  else
    // real computation: gY is dishonest
    let y = CommonDH.keygen g in 
    let gY = CommonDH.pubshare y in  
    let gZ: CommonDH.share g = admit() in // we could also use dh_responder
    let k = extract1 s (| g, gX, gY |) gZ in
    gY, k

/// Initiator computes DH secret material
assume val extractI: 
  #u: usage info ii -> 
  #i: id -> 
  #a: info ->
  s: salt ii u i a ->
  g: CommonDH.group ->
  x: CommonDH.keyshare g ->
  gY: CommonDH.share g ->
  secret ii u (Extract1 i (| g, CommonDH.pubshare x, gY |)) a
*)

/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
assume val extract2: 
  #u: usage info ii ->
  #i: id ->
  #a: info ->
  s: salt ii u i a -> 
  secret ii u (Extract2 i) a


/// module KeySchedule
/// composing them specifically for TLS

// not sure how to enforce label restrictions, e.g.
// val u_traffic: s:string { s = "ClientKey" \/ s = "ServerKey"} -> ip:ipkg -> pkg ip

let some_keylen: keylen = 32ul

inline_for_extraction
let u_default:  p:pkg ii & (ctx:info -> p.use)  = (| rp ii, (fun (a:info) -> some_keylen) |)

inline_for_extraction
let u_traffic: usage info ii = function 
  | "ClientKey" | "ServerKey" -> (| mp ii , (fun (a:info) -> a.aea) |)
  | _ -> u_default

// #set-options "--print_universes --print_implicits"

inline_for_extraction
let rec u_master_secret (n:nat ): Tot (usage info ii) (decreases (%[n; 0])) = function 
  | "traffic" -> (| pp ii u_traffic, (fun a -> a) |)
  | "resumption" -> if n > 0 then (| pskp ii (u_early_secret (n-1)), (fun (a:info) -> a)|) else (| rp ii, (fun (a:info) -> some_keylen) |)
  | _ -> u_default
and u_handshake_secret (n:nat): Tot (usage info ii) (decreases (%[n; 1])) = function 
  | "traffic" -> (| pp ii u_traffic , (fun (a:info) -> a) |)
  | "salt" -> (| saltp2 ii (u_master_secret n), (fun (a:info) -> a) |)
  | _ -> u_default
and u_early_secret (n:nat): Tot (usage info ii) (decreases (%[n;2])) = function
  | "traffic" -> (| pp ii u_traffic, (fun (a:info) -> a) |)
  | "salt" -> (| saltp1 ii (u_handshake_secret n), (fun (a:info) -> a) |)
  | _ -> u_default

/// Tot required... can we live with this integer indexing?
/// One cheap trick is to store a PSK only when it enables resumption.

/// Testing normalization works for a parametric depth
assume val depth:  n:nat {n > 1} 
let u: usage info ii = u_early_secret depth 
let i0 = Extract0 (Preshared 0)

/// Usability?

let a = { ha=SHA1; aea=AES_GCM256 }

let psk0: psk #ii #u (Preshared 0) a = create_psk (Preshared 0) a

let early_secret: secret ii u i0 a = extract0 psk0 

val early_traffic: secret ii u_traffic (Derived i0 "traffic") a
let early_traffic = derive a early_secret "traffic"

val k0: key #ii (Derived (Derived i0 "traffic") "ClientKey") AES_GCM256
let k0 = derive a early_traffic "ClientKey" 
let cipher  = encrypt k0 10

val salt1:  salt ii (u_handshake_secret depth) (Derived i0 "salt") a
let salt1  = derive a early_secret "salt"

let g = CommonDH.default_group
let x = initI g 
let gX = CommonDH.pubshare x
let gY: CommonDH.share g = admit()
let dhe_id: id_dhe = (| g, gX, gY |)

let i1 = Extract1 (Derived i0 "salt") dhe_id


(*
assume val g:element
let iX = genDH g
*)

val hs_secret : secret ii (u_handshake_secret depth) i1 a
// let hs_secret = extract1 salt1 42 
let hs_secret = extractI salt1 g x gY

val hs_traffic: secret ii u_traffic (Derived i1 "traffic") a
let hs_traffic = derive a hs_secret "traffic"

val k1: key #ii (Derived (Derived i1 "traffic") "ServerKey") AES_GCM256
let k1 = derive a hs_traffic "ServerKey" 
let cipher' = encrypt k1 11

val salt2:  salt ii (u_master_secret depth) (Derived i1 "salt") a
let salt2  = derive a hs_secret "salt"

let i2 = Extract2 (Derived i1 "salt")  
val master_secret: secret ii (u_master_secret depth) i2 a
let master_secret = extract2 salt2 

val rsk: psk #ii #(u_early_secret (depth - 1)) (Derived i2 "resumption") a

let i3 = Extract0 (Derived i2 "resumption")
let rsk = derive a master_secret "resumption" 
// #(u_master_secret depth ) #i2 
val next_early_secret: secret ii (u_early_secret (depth - 1)) i3 a
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
*)
