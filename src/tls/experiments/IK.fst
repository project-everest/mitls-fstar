module IK

(*! 17-12-08 THIS FILE IS NOT USED ANYMORE *)

/// Not done yet:
///
/// * define/review all idealization flags. How are they accessed?
///
/// * reliance on u_of_i in DH extraction (intuitive but hard to code)
///
/// * extraction: ensure all strongly-dependent types disappear and
///   (concretely) the key schedule directly allocates all key
///   instances.
///
/// * usage restriction for KDFs, based on a generalization of wellformed_id
///   (starting with an example of hashed-log derivation)
///
/// Note also that we support rather static agility and usages; while
/// this is sufficient for TLS, we might enable more details to be
/// bound at derivation-time as part of the derivation context.

open Mem

module MH = FStar.Monotonic.Heap
module HS = FStar.HyperStack
let model = Flags.model

// temporary imports

type bytes = FStar.Bytes.bytes
let lbytes (len:UInt32.t) = FStar.Bytes.lbytes (UInt32.v len)

let sample (len:UInt32.t): ST (lbytes len)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 -> h0 == h1)
  = CoreCrypto.random (UInt32.v len)

include Pkg 
include Idx 



/// Try out on examples: we may need a stateful invariant of the form
/// "I have used this secret to create exactly these keys".

/// We expect this function to be fully applied at compile time,
/// returning a package and a algorithm-derivation function to its
/// agility parameter (to be usually applied at run-time).

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





// not sure how to enforce label restrictions, e.g.
// val u_traffic: s:string { s = "ClientKey" \/ s = "ServerKey"} -> ip:ipkg -> pkg ip

let some_keylen: keylen = 32ul
let get_keylen (i:id) = some_keylen

(* -- 08/12/17: see middle of the file for up to date usage example

inline_for_extraction
let u_default: usage = fun lbl -> rp ii get_keylen

//17-11-15 rename to aeadAlg_of_id ?
assume val get_aeadAlg: i:id -> aeadAlg
let derive_aea
  (lbl:label) (i:id)
  (a:info{wellformed_id (Derive i lbl Expand)}):
  (a':aeadAlg{a' == get_aeadAlg (Derive i lbl Expand)})
=
  //fixme! should be extracted from a
  get_aeadAlg (Derive i lbl Expand)

inline_for_extraction
let u_traffic: usage =
  fun (lbl:label) ->
  match lbl with
  | "ClientKey" | "ServerKey" -> mp ii get_aeadAlg
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

let labels = list label

(*
let psk_tables depth = ...
let pskp n u =
  memoization (local_pskp n u) psk_tables.[n]
  *)

// 17-10-20 this causes an extraction-time loop, as could be expected.
inline_for_extraction
let rec u_master_secret (n:nat ): Tot usage (decreases (%[n; 0])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "resumption" -> if n > 0
                   then pskp (u_early_secret (n-1))
                   else u_default lbl
  | _            -> u_default lbl
and u_handshake_secret (n:nat): Tot usage (decreases (%[n; 1])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "salt"       -> saltp2 (u_master_secret n)
  | _            -> u_default lbl
and u_early_secret (n:nat): Tot usage (decreases (%[n;2])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "salt"       -> saltp (u_handshake_secret n)
  | _            -> u_default lbl
/// Tot required... can we live with this integer indexing?
/// One cheap trick is to store a PSK only when it enables resumption.

//17-11-16 these functions suffice to implement `i_to_u`, but
// - this may be too late to be useful
// - this feel like writing twice the same code... refactor?

let rec f_master_secret (n:nat) (labels: list label): Tot usage (decreases (%[n; 0])) =
  match labels with
  | [] -> u_master_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "resumption" ->
      if n > 0 then f_early_secret (n-1) labels else u_default
    | _ -> u_default
and f_handshake_secret (n:nat) (labels: list label): Tot usage (decreases (%[n; 1])) =
  match labels with
  | [] -> u_handshake_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "salt" -> f_master_secret n labels
    | _ -> u_default
and f_early_secret (n:nat) (labels: list label): Tot usage (decreases (%[n;2])) =
  match labels with
  | [] -> u_early_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "salt" -> f_handshake_secret n labels
    | _ -> u_default

let _: unit =
  assert(f_master_secret 3 ["resumption";"salt"] == u_handshake_secret 2)




(* not necessary?

We can write a List.fold on sequences of labels that yields the derived u.

u returns a package (not the next u)
we have a (partial, recursive) function from u to u'

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
let u: usage = u_early_secret depth

let gen_pskid a : St (n:nat{registered (Preshared a n)}) = admit()

val ks: unit -> St unit
let ks() =
  let pskctr = gen_pskid Hashing.Spec.SHA1 in
  let ipsk: regid = Preshared Hashing.Spec.SHA1 pskctr in
  let a = Info Hashing.Spec.SHA1 None in

  let psk0 : ext0 u ipsk = create_psk ipsk a in
  let i0 : regid = Derive ipsk "" Extract in
  let early_secret : secret u i0 = extract0 psk0 a in

  let (| _, et |) = derive early_secret a "traffic" Expand a in
  let i_traffic0 : regid = Derive i0 "traffic" Expand in
  let a_traffic0 = Info Hashing.Spec.SHA1 None in
  let early_traffic : secret u_traffic i_traffic0 = et in

  let aea_0rtt = derive_aea "ClientKey" i_traffic0 a in
  let (| _, ae0 |) = derive early_traffic a "ClientKey" Expand aea_0rtt in
  let i_0rtt : regid = Derive i_traffic0 "ClientKey" Expand in
  let k0: key ii get_aeadAlg i_0rtt = ae0 in
  let cipher  = encrypt k0 10 in

  let (| _, s1 |) = derive early_secret a "salt" Expand a in
  let i_salt1: regid = Derive i0 "salt" Expand in
  let salt1: salt (u_handshake_secret depth) i_salt1 = s1 in

  let g = CommonDH.default_group in
  let x = initI g in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in

  let (| i_gY, hs1 |) = extractR salt1 a gX in
  let (| _, gY |) = i_gY in
  let i1 : regid = Derive i_salt1 "" (ExtractDH (IDH gX gY)) in

  // FIXME(adl) This requires a proof that u_of_i (dfst i_gY) == u_handshake_secret depth
  //assume(peer_instance i_gY == secret (u_handshake_secret depth) i1);
  let hs_secret: secret (u_handshake_secret depth) i1 = admit() in

  let (| _, hst |) = derive hs_secret a "traffic" Expand a in
  let i_traffic1: regid = Derive i1 "traffic" Expand  in
  let hs_traffic: secret u_traffic i_traffic1 = hst in

  let aea_1rtt = derive_aea "ServerKey" i_traffic1 a in
  let (| _, ae1 |) = derive hs_traffic a "ServerKey" Expand aea_1rtt in
  let i_1rtt : regid = Derive i_traffic1 "ServerKey" Expand in
  let k1: key ii get_aeadAlg i_1rtt = ae1 in

  let cipher  = encrypt k1 11 in

  let (| _, s2 |) = derive hs_secret a "salt" Expand a in
  let i_salt2: regid = Derive i1 "salt" Expand in
  let salt2 : salt2 (u_master_secret depth) i_salt2 = s2 in

  let i2 : regid = Derive i_salt2 "" Extract in
  let master_secret: secret (u_master_secret depth) i2 = extract2 #(u_master_secret depth) #i_salt2 salt2 a in
  let i3: regid = Derive i2 "resumption" Expand in

  let rsk: ext0 (u_early_secret (depth - 1)) i3 = derive master_secret a "resumption" Expand a in
  let i4: regid = Derive i3 "" Extract in
  let next_early_secret: secret (u_early_secret (depth - 1)) i4 = extract0 rsk a in
  ()
--- *)
