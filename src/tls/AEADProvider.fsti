module AEADProvider

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes

open Mem
open TLSConstants
// open TLSInfo
open FStar.UInt32

module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = EverCrypt
module LB = LowStar.Buffer
module CI = Crypto.Indexing
module Plain = Crypto.Plain
module CB = Crypto.Symmetric.Bytes

let discard (b:bool) : ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print (s:string) : ST unit (requires fun _ -> True) (ensures (fun h0 _ h1 -> h0 == h1)) =
  discard (IO.debug_print_string ("AEP| "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1)) =
  if DebugFlags.debug_AEP then print else (fun _ -> ())

(***********************************************************************)

type id = i:TLSInfo.id{~(TLSInfo.PlaintextID? i) /\ AEAD? (TLSInfo.aeAlg_of_id i)}
let alg (i:id): aeadAlg = let AEAD aead _ = TLSInfo.aeAlg_of_id i in aead

//18-09-04  unclear what's shadowing alg below
let alg' (i:id): aeadAlg = let AEAD aead _ = TLSInfo.aeAlg_of_id i in aead

let evercrypt_aeadAlg_option_of_aead_cipher : aeadAlg -> option EverCrypt.aead_alg =
  let open EverCrypt in 
  function
  | AES128_GCM        -> Some AES128_GCM
  | AES256_GCM        -> Some AES256_GCM
  | CHACHA20_POLY1305 -> Some CHACHA20_POLY1305
  | _                 -> None
let aeadAlg_for_evercrypt (a:aeadAlg{Some? (evercrypt_aeadAlg_option_of_aead_cipher a)})
  : EverCrypt.aead_alg
  = Some?.v (evercrypt_aeadAlg_option_of_aead_cipher a)

// Real IVs must be created with the internal
// salting function below.
let iv_length i = 12 // CC.aeadRealIVSize (alg i)
val iv (i:id) : Tot Type0

val coerce_iv (i:id) (b:lbytes (iv_length i)) : Tot (iv i)

let aead_provider_key_length i = UInt32.v (EverCrypt.aead_keyLen(alg i))

// Salt is the static part of IVs
let salt_length (i:id) =
  match TLSInfo.pv_of_id i with
  | TLS_1p3 -> iv_length i
  | _ ->
    let open EverCrypt in 
    match alg' i with
    | AES128_GCM
    | AES128_CCM
    | AES128_CCM8
    | AES256_GCM
    | AES256_CCM
    | AES256_CCM8       ->  4
    | CHACHA20_POLY1305 -> 12

// Length of the explicit (sent on wire) IV
let explicit_iv_length (i:id) =
  match TLSInfo.pv_of_id i with
  | TLS_1p3 -> 0
  | _ ->
    let open EverCrypt in 
    match alg' i with
    | AES128_GCM  
    | AES128_CCM  
    | AES128_CCM8 
    | AES256_GCM  
    | AES256_CCM  
    | AES256_CCM8       -> 8
    | CHACHA20_POLY1305 -> 0

type key  (i:id) = lbytes (aead_provider_key_length i)
type salt (i:id) = lbytes (salt_length i)

let state (i:id) (r:rw) =
    EverCrypt.aead_state * (key i * salt i)

let salt_of_state #i #r (s:state i r) : salt i = snd (snd s)
let key_of_state #i #r (s:state i r) : key i = fst (snd s)

type writer i = s:state i Writer
type reader i = s:state i Reader

let region #i #rw (s:state i rw) = tls_region
let log_region #i #rw (s:state i rw) = tls_region

let noncelen (i:id) =
  match (TLSInfo.pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, EverCrypt.CHACHA20_POLY1305) ->
    iv_length i
  | _ -> (iv_length i) - (salt_length i)

type nonce i = lbytes (noncelen i)
 
val create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i): Tot (i:iv i)

(* Necessary for injectivity of the nonce-to-IV construction in TLS 1.3 *)
val lemma_nonce_iv (#i:id) (#rw:rw) (st:state i rw) (n1:nonce i) (n2:nonce i)
  : Lemma (create_nonce st n1 == create_nonce st n2 ==> n1 = n2)

let genPost (#i:id) (parent:rgn) h0 (w:writer i) h1 =
  modifies_none h0 h1

val gen (i:id) (r:rgn) : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (genPost r))

val leak (#i:id) (#rw:rw) (st:state i rw)
  : ST (key i * salt i)
  (requires (fun h0 -> ~(TLSInfo.authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
val genReader (parent:rgn) (#i:id) (st:writer i) : ST (reader i)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

val coerce (i:id) (r:rgn) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> ~(TLSInfo.authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

type plainlen = n:nat{n <= max_TLSPlaintext_fragment_length}
(* irreducible *)
type plain (i:id) (l:plainlen) = b:lbytes l
let repr (#i:id) (#l:plainlen) (p:plain i l) : Tot (lbytes l) = p

let adlen i = match TLSInfo.pv_of_id i with
  | TLS_1p3 -> 0 | _ -> 13
type adata i = lbytes (adlen i)

//18-09-04 consider switching to UInt32
let taglen i = UInt32.v (EverCrypt.aead_tagLen (alg i))
let cipherlen i (l:plainlen) : n:nat{n >= taglen i} = l + taglen i
type cipher i (l:plainlen) = lbytes (cipherlen i l)

open EverCrypt.Helpers
module LM = LowStar.Modifies

val from_bytes (b:bytes{length b <> 0}) : StackInline uint8_p
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 ->
    LB.(modifies loc_none h0 h1) /\
    LB.live h1 buf /\
    LB.unused_in buf h0 /\
    LB.length buf = length b /\
    Bytes.reveal b `Seq.equal` LB.as_seq h1 buf))

val encrypt (#i:id) (#l:plainlen) (w:writer i) (iv:iv i) (ad:adata i) (plain:plain i l)
  : ST (cipher:cipher i l)
       (requires (fun h -> True))
       (ensures (fun h0 cipher h1 -> modifies_none h0 h1))

val decrypt (#i:id) (#l:plainlen) (st:reader i) (iv:iv i) (ad:adata i) (cipher:cipher i l)
  : ST (co:option (plain i l))
       (requires (fun _ -> True))
//  (requires (fun _ ->
//    FStar.UInt.size (length ad) 32
//    /\ FStar.UInt.size (length cipher) 32
//    /\ length cipher >= CC.aeadTagSize (alg i))
       (ensures (fun h0 plain h1 -> modifies_none h0 h1))

(*
/// Agility:
/// - for AEAD, we need a pair of algorithms for the cipher and for UFCMA---use Crypto.Indexing.fsti;
/// - for StreamAE, we additionallly need the PV (to control the length of the static IV).
///
/// We keep these parameters in AEADProvider and StreamAE instances, respectively.

type aeadAlg // fixme.

// TODO: add the two regions of AEAD.fsti, used only ideally (hence coerce is ~pure)
type info (ip: ipkg) (aeadAlg_of_i: i:ip.IK.t -> aeadAlg) (i:ip.t) = a:aeadAlg {a = aeadAlg_of_i i}

open IK
unfold let localpkg
  (ip: ipkg)
  (aeadAlg_of_i: i:ip.IK.t -> aeadAlg)
  :
  p: IK.local_pkg ip {IK.LocalPkg?.info #ip p == info1 ip ha_of_i good_of_i}
=
    IK.LocalPkg
      (fun (i:ip.IK.t {ip.IK.registered i}) -> writer ip i)
      (info ip aeadAlg_of_i)
      (fun #_ u -> aeadLen u)
      Flags.ideal_aead
      // local footprint
      (fun #i (k:writer ip i) -> Set.empty (*17-11-24 regions for the PRF and the log *)  )
      // local invariant
      (fun #_ k h -> True)
      (fun r i h0 k h1 -> ())
      // create/coerce postcondition
      (fun #i u k h1 -> k.u == u (*17-11-24  /\ fresh_subregion (region k) u.parent h0 h1 *) )
      (fun #i u k h1 r h2 -> ())
      (create ip aeadAlg_of_i)
      (coerceT ip aeadAlg_of_i)
      (coerce ip aeadAlg_of_i)

let mk_pkg (ip:ipkg) (aeadAlg_of_i: ip.t -> aeadAlg): ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
    //17-12-01 we also need freshness and emptyness of the new table + local packaging
    modifies_mem_table p.define_table h0 h1 /\
    p.package_invariant h1)
=
  memoization_ST #ip (localpkg ip aeadAlg_of_i)

// we may want to provide TLS-specific encrypt, decrypt... partially applied e.g. [encrypt ii aeadAlg_of_i]


unfold let localpkg_IV
// TODO adapting local_raw_pkg

// TODO ensure the flag is set only when multiplexing to the verified implementation
*)
