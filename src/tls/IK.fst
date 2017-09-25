module IK 

/// a standalone experiment modelling key derivation parametrically in
/// the use of the derived keys.
///
/// * captures nested derivations via bounded-recursive instantiation.
/// * applied to an extract/expand schedule (simplified from TLS 1.3)
/// * models partial key compromise, controlled by the adversary for each new key
///
/// Not done yet: conditional idealization and erasure; agility. 

type lbytes (len:UInt32.t)

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
  key: (Idx?.t ip -> Type0) -> 
  len: (Idx?.t ip -> UInt32.t) ->
  create: (i:Idx?.t ip -> key i) -> 
  coerce: (i:Idx?.t ip {~(Idx?.honest ip i)} -> lbytes (len i) -> key i) ->
  pkg ip

/// --------------------------------------------------------------------------------------------------
/// module Index

/// we provide an instance of ipkg to track key derivation (here using constant labels)
type label = string 
type usage = string -> ip:ipkg -> pkg ip

type id_dhe = nat // simplification: instead of the index, use  materials (g,X,Y)

type id_psk = nat // external application PSKs only; we may need a special PSK0 constructor too
type id = 
  | Zero // symbolic constant for absent extraction arguments
  | Preshared of id_psk  /// external application PSKs only
  | Extract0: materials:id -> id
  | Extract1: salt:id -> materials: id_dhe -> id
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
assume new type secret (u:usage) (ip: ipkg) (i: ip.t)

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).
 
/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.

val create: 
  u: usage -> 
  ip: ipkg ->
  i: ip.t ->
  secret u ip i
let create u ip i = admit()

val coerce: 
  u: usage -> 
  ip: ipkg ->
  i: Idx?.t ip ->
  repr: lbytes 32ul -> 
  secret u ip i
let coerce u ip i repr = admit()

let pp (u:usage) (ip:ipkg): pkg ip = Pkg 
  (secret u ip) 
  (fun _ -> 32ul) 
  (create u ip) 
  (coerce u ip)

/// TODO consider separating pp packages more explicitly, so that we
/// can idealize them one at a time. (Having one proof step for each
/// nested level of key derivation seems unavoidable.)

val derive:
  #u:usage ->
  #i: id -> 
  k: secret u ii i ->
  v: label ->
  (u v ii).key  (Derived i v)  

let derive #u #i k v = 
  let pkg = u v ii in
  if ii.honest (*safe*) i // (Derived i v) 
  then
    pkg.create (Derived i v) //keybytes 
  else 
    let repr: lbytes (pkg.len (Derived i v)) = admit() in 
    pkg.coerce (Derived i v) repr

/// Reconsider packaging: should create take external randomness?
///
/// core idealized functionality, presumably called at most once on every v. 
/// full coercion is something different. 
/// otherwise, create suffices for all purposes.


/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
type psk (expu: usage) (ip: ipkg) (i: ip.t)

assume val create_psk: 
  #expu: usage -> 
  #ip: ipkg -> 
  i: ip.t -> 
  psk expu ip i 

assume val coerce_psk: 
  #expu: usage -> 
  #ip: ipkg -> 
  i: ip.t -> 
  raw: lbytes 16ul -> 
  psk expu ip i 

let pskp (expu:usage) (ip:ipkg): pkg ip = Pkg 
  (psk expu ip)
  (fun _ -> 16ul) 
  create_psk 
  coerce_psk

/// Derived salt; note it is already indexed by the usage of the
/// following extension.
type salt (expu: usage) (ip:ipkg) (i: ip.t) 

assume val create_salt: 
  #expu: usage -> 
  #ip: ipkg -> 
  i: ip.t -> 
  salt expu ip i 

assume val coerce_salt: 
  #expu: usage ->
  #ip: ipkg ->
  i: ip.t ->
  raw: lbytes 16ul ->
  salt expu ip i 

let saltp1 (expu:usage) (ip:ipkg): pkg ip = Pkg 
  (salt expu ip)
  (fun _ -> 16ul) 
  create_salt 
  coerce_salt

let saltp2 (expu:usage) (ip:ipkg): pkg ip = Pkg 
  (salt expu ip)
  (fun _ -> 16ul) 
  create_salt 
  coerce_salt

/// HKDF.Extract(key=0, materials=k) idealized as a single-use PRF,
/// possibly customized on the distribution of k.
assume val extract0:
  #expu: usage ->
  #i: id ->
  k: psk expu ii i -> 
  secret expu ii (Extract0 i)

/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-bit
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.
assume val extract1:
  #expu: usage -> 
  #i: id ->
  s: salt expu ii i ->
  materials: id_dhe -> 
  secret expu ii (Extract1 i materials)

/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
assume val extract2: 
  #expu: usage ->
  #i: id ->
  s: salt expu ii i -> 
  secret expu ii (Extract2 i)


/// module Raw
/// a default functionality (no idealization);
/// for modelling, we could also provide a "leak" function
type raw  (#ip: ipkg) (i: Idx?.t ip) = list nat 
let create_raw (#ip: ipkg) (i: Idx?.t ip): raw  i  = [1;2;3] // should sample instead
let coerce_raw (#ip: ipkg) (i: Idx?.t ip) _ : raw i  = [1;2;3] // should sample instead
let rp (ip:ipkg): pkg ip = Pkg raw (fun _ -> 16ul) create_raw coerce_raw


/// module AEAD
/// Some other sample functionality,
/// with a different concrete key representation
assume new type key (#ip: ipkg) (i: Idx?.t ip) // abstraction required for indexing
assume val coerce_key: #ip: ipkg -> i: Idx?.t ip -> lbytes 20ul -> key i 
assume val dummy: lbytes 20ul
let create_key (#ip: ipkg) (i: Idx?.t ip) : key i = coerce_key i dummy (* strange bug with coerce *)
let mp (ip:ipkg): pkg ip = Pkg key (fun _ -> 20ul) create_key coerce_key

val encrypt: #ip:ipkg -> #i:Idx?.t ip -> k: key i -> nat -> nat 
let encrypt #ip #i k v = v + 1


/// module KeySchedule
/// composing them specifically for TLS

// not sure how to enforce label restrictions, e.g.
// val u_traffic: s:string { s = "ClientKey" \/ s = "ServerKey"} -> ip:ipkg -> pkg ip
 
let u_traffic = function 
  | "ClientKey" | "ServerKey" -> mp
  | _ -> rp 

// #set-options "--print_universes --print_implicits"

let rec u_master_secret (n:nat ): Tot usage (decreases (%[n; 0])) = function 
  | "traffic" -> pp u_traffic 
  | "resumption" -> if n > 0 then pskp (u_early_secret (n-1)) else rp 
  | _ -> rp
and u_handshake_secret (n:nat): Tot usage (decreases (%[n; 1])) = function 
  | "traffic" -> pp u_traffic 
  | "salt" -> saltp2 (u_master_secret n) 
  | _ -> rp
and u_early_secret (n:nat): Tot usage (decreases (%[n;2])) = function
  | "traffic" -> pp u_traffic
  | "salt" -> saltp1 (u_handshake_secret n) 
  | _ -> rp 

/// Tot required... can we live with this integer indexing?
/// One cheap trick is to store a PSK only when it enables resumption.

/// Testing normalization works for a parametric depth
assume val depth:  n:nat {n > 1} 
let u: usage = u_early_secret depth 
let i0 = Extract0 (Preshared 0)

/// Usability?
let psk0: psk u ii (Preshared 0) = create_psk  (Preshared 0)
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
