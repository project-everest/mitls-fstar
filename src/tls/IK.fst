module IK 

/// a standalone experiment modelling key derivation parametrically in
/// the use of the derived keys.
///
/// * captures nested derivations via bounded-recursive instantiation.
/// * applied to an extract/expand schedule (simplified from TLS 1.3)
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility and ideal-only indexes.
///
/// Not done yet: conditional idealization and erasure.

assume type lbytes (len:UInt32.t)
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
noeq type pkg (ip:ipkg) = | Pkg:
  use: Type0 -> 
  key: (ip.t -> use -> Type0) -> 
  len: (use -> UInt32.t) ->
  create: (i:ip.t -> u:use -> key i u) -> 
  coerce: (i:ip.t {~(ip.honest i)} -> u:use -> lbytes (len u) -> key i u) ->
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
type keylen = n:UInt32.t { UInt32.v n < 128 }
type raw  (#ip: ipkg) (i: Idx?.t ip) (len:keylen) = lbytes len
let create_raw (#ip: ipkg) (i: ip.t) (len:keylen): raw  i len = sample len
let coerce_raw (#ip: ipkg) (i: ip.t) (len:keylen) (r:lbytes len): raw i len = r
let rp (ip:ipkg): pkg ip = Pkg keylen raw (fun n -> n) create_raw coerce_raw

/// --------------------------------------------------------------------------------------------------
/// module Index

/// We provide an instance of ipkg to track key derivation (here using constant labels)
type label = string 

/// We expect this function to be fully applied at compile time.
type usage (a:Type0) (ip:ipkg) =  label -> p:pkg ip & (ctx:a -> p.use)

type id_dhe = nat // simplification: instead of the index, use  materials (g,X,Y)
type id_psk = nat // external application PSKs only; we may need a special PSK0 constructor too
type id = 
  | Zero // symbolic constant for absent extraction arguments
  | Preshared of id_psk  // external application PSKs only
  | Extract0: materials:id -> id
  | Extract1: salt:id -> materials: id_dhe -> id // do we need 2 cases?
  | Extract2: salt:id  -> id
  | Derived: id -> label -> id  

/// Using different constructors for different constructions; we don't
/// restrict index, but we only provide the key-level operations at
/// specific types.
///
/// TODO: extend Derived to take (and record) an optional hashed digest.
///
/// This form of indexing may be too global, e.g. extractions should
/// not depend on expansion; in principle, we could clip "Extracted"
/// to the extractor index.

let ii:ipkg = Idx id (fun _ -> true)

/// TODO maintain a monotonic safety table.  and enforce fresh
/// registration at creation/coercion time.
///
/// Try out on examples: we'll need a stateful invariant of the form
/// "I have used this secret to create exactly these keys". What out 


/// --------------------------------------------------------------------------------------------------
/// module KDF
/// 
/// we define a KDF parametric in both its usage and ipkg
/// We rely on type abstraction to separate secrets with different indexes
/// For soundness, we must also prevent external calls to create derived secrets.
type kdfa = | SHA1 | SHA2
type info = {ha:kdfa; aea:aeadAlg} (* runtime *) 
//type suse = a:info * usage info ii

let secret_len a = 
  match a.ha with 
  | SHA1 -> 8ul
  | SHA2 -> 16ul 
assume new type secret 
  (ip: ipkg) 
  (u: usage info ip)
  (i: ip.t) 
  (a: info) 

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).
 
/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.

val coerce: 
  ip: ipkg ->
  u: usage info ip ->
  i: ip.t ->
  a: info (* run-time *) -> 
  repr: lbytes (secret_len a) -> 
  secret ip u i a 
let coerce ip u i a repr = admit()

val create: 
  ip: ipkg ->
  u: usage info ip -> 
  i: ip.t ->
  a: info (* run-time *) ->
  secret ip u i a
let create ip u i a = 
  let raw = sample (secret_len a) in
  coerce ip u i a raw

let pp (ip:ipkg) (u: usage info ip): pkg ip = Pkg 
  info
  (secret ip u) 
  secret_len
  (create ip u) 
  (coerce ip u)

/// TODO consider separating pp packages more explicitly, so that we
/// can idealize them one at a time. (Having one proof step for each
/// nested level of key derivation seems unavoidable.)

let derived_key (u: usage info ii) (i: id) (v:label) (a: info) = 
  let (| pkg', derived_alg |) = u v in 
  pkg'.key (Derived i v) (derived_alg a)

val derive:
  #u: usage info ii ->
  #i: id ->
  a: info -> 
  k: secret ii u i a ->
  v: label ->
  derived_key u i v a 

let derive  #u #i a k v = 
  let (| pkg', derived_alg |) = u v in 
  let a' = derived_alg a in 
  if ii.honest (*safe*) i // (Derived i v) 
  then
    pkg'.create (Derived i v) a' //keybytes 
  else 
    let raw = sample (pkg'.len a') in 
    pkg'.coerce (Derived i v) a' raw

/// Reconsider packaging: should create take external randomness?
///
/// core idealized functionality, presumably called at most once on every v. 
/// full coercion is something different. 
/// otherwise, create suffices for all purposes.


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
assume val extract1:
  #u: usage info ii -> 
  #i: id ->
  #a: info -> 
  s: salt ii u i a ->
  materials: id_dhe -> 
  secret ii u (Extract1 i materials) a

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

let u_default:  p:pkg ii & (ctx:info -> p.use)  = (| rp ii, (fun (a:info) -> some_keylen) |)

let u_traffic: usage info ii = function 
  | "ClientKey" | "ServerKey" -> (| mp ii , (fun (a:info) -> a.aea) |)
  | _ -> u_default

// #set-options "--print_universes --print_implicits"

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

let psk0: psk #ii #u (Preshared 0) a = create_psk  (Preshared 0)

(* 
let early_secret: secret u ii i0 = extract0 psk0

val early_traffic: secret u_traffic ii (Derived i0 "traffic") 
let early_traffic = derive early_secret "traffic"

val k0: key #ii (Derived (Derived i0 "traffic") "ClientKey")
let k0 = derive early_traffic "ClientKey" 
let cipher  = encrypt k0 10

val salt1:  salt (u_handshake_secret depth) ii (Derived i0 "salt")
let salt1  = derive early_secret "salt"

let i1 = Extract1 (Derived i0 "salt") 42
val hs_secret : secret (u_handshake_secret depth) ii i1
let hs_secret = extract1 salt1 42 

val hs_traffic: secret u_traffic ii (Derived i1 "traffic")
let hs_traffic = derive hs_secret "traffic"

val k1: key #ii (Derived (Derived i1 "traffic") "ServerKey")
let k1 = derive hs_traffic "ServerKey" 
let cipher = encrypt k1 11

val salt2:  salt (u_master_secret depth) ii (Derived i1 "salt")
let salt2  = derive hs_secret "salt"

let i2 = Extract2 (Derived i1 "salt")
val master_secret: secret (u_master_secret depth) ii i2 
let master_secret = extract2 salt2 

val rsk: psk (u_early_secret (depth - 1)) ii (Derived i2 "resumption")  

let i3 = Extract0 (Derived i2 "resumption")
let rsk = derive #(u_master_secret depth ) #i2 master_secret "resumption" 

val next_early_secret: secret (u_early_secret (depth - 1)) ii i3 
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


TMP*)
