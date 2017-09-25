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
  t: Type -> 
  honest: (t -> bool) ->  
  ipkg

/// Keyed functionality define Key packages, parametric in their
/// indexes, but concrete on their key randomness; instances may have
/// any number of other functions (such a leak, for instance).
noeq type pkg (ip:ipkg) = | Pkg:
  key: (Idx?.t ip -> Type) -> 
  len: (Idx?.t ip -> UInt32.t) ->
  create: (i:Idx?.t ip -> key i) -> 
  coerce: (i:Idx?.t ip {~(Idx?.honest ip i)} -> lbytes (len i) -> key i) ->
  pkg ip


/// --------------------------------------------------------------------------------------------------
/// module Index

/// we provide an instance of ipkg to track key derivation (here using constant labels)
type label = string 
type usage = string -> ip:ipkg -> pkg ip
// derivation usage; 
// 17-09-22 could be just a function too. 

// type extract_usage: ip:ipkg -> pkg ip 

type id_dhe = nat 
type id_psk = nat // external application PSKs only; we may need a special PSK0 constructor too
and id = 
  | Zero // symbolic constant for absent extraction arguments
  | Preshared of id_psk  /// external application PSKs only
  | Extract0: materials:id -> id
  | Extract1: salt:id -> materials: id_dhe -> id
  | Extract2: salt:id  -> id
  | Derived: id -> label -> id  
///
/// We could merge some cases above
/// 
/// Possible extensions:
/// Derived0;
/// Derived2 with label + hashed digest.
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
/// Derived makes us non-parametric in ii
///
/// core idealized functionality, presumably called at most once on every v. 
/// full coercion is something different. 
/// otherwise, create suffices for all purposes.
///
/// proof idea: once we idealize PRF, we know the derive samples 


/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)

type psk (expu: usage) (ip: ipkg) (i: ip.t)
type salt (expu: usage) (ip:ipkg) (i: ip.t) 

assume val create_psk: 
  #expu: usage -> 
  #ip: ipkg -> 
  i: ip.t -> 
  psk expu ip i 
  
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

assume val extract0:
  #expu: usage ->
  #i: id ->
  k: psk expu ii i -> 
  secret expu ii (Extract0 i)

assume val extract1:
  #expu: usage -> 
  #i: id ->
  s: salt expu ii i ->
  materials: id_dhe -> 
  secret expu ii (Extract1 i materials)

assume val extract2: 
  #expu: usage ->
  #i: id ->
  s: salt expu ii i -> 
  secret expu ii (Extract2 i)
  


/// module Raw
/// a default functionality (no idealization)
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
///
let u_traffic: usage = function 
  | "ClientKey" | "ServerKey" -> mp
  | _ -> rp 

let rec u_early_secret (n:nat): usage = 
  function 
  | "traffic" -> pp u_traffic 
  | "salt" -> saltp1 (
    function 
      | "traffic" -> pp u_traffic
      | "salt" -> saltp2 (
        function
          | "traffic" -> pp u_traffic 
          | "resumption" -> if n > 0 then pp (u_early_secret (n-1)) else rp 
          | _ ->rp ) 
      | _ -> rp )
  | _ -> rp

(* can't get the universes right
let rec u_master_secret (n:nat ): usage u#0 u#1= function 
  | "traffic" -> pp u_traffic 
  | "resumption" -> if n > 0 then pp (u_early_secret (n-1)) else rp 
  | _ -> rp
and u_handshake_secret (n:nat): usage u#0 u#1 = function 
  | "traffic" -> pp u_traffic 
  | "salt" -> saltp2 (u_master_secret n) 
  | _ -> rp
and u_early_secret (n:nat): usage u#0 u#1 = function
  | "traffic" -> pp u_traffic
  | "salt" -> saltp1 (u_handshake_secret n) 
  | _ -> rp 
*)

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
let cipher  = encrypt k0 42

// this is not actually working
//val salt1:  salt _ ii (Derived i0 "salt")

let salt1  = derive early_secret "salt"
let hs_secret = extract1 salt1 42 
// let handshake_traffic = derive hs_secret "traffic"

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
