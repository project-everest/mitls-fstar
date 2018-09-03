module AEADProvider

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes

open Mem
open TLSConstants
open TLSInfo
open FStar.UInt32

module HS = FStar.HyperStack
module CC = CoreCrypto
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

type id = i:id{~(PlaintextID? i) /\ AEAD? (aeAlg_of_id i)}
let alg (i:id) :aeadAlg = let AEAD aead _ = aeAlg_of_id i in aead
let evercrypt_aeadAlg_option_of_aead_cipher : aeadAlg -> option EverCrypt.aead_alg =
  function
  | CoreCrypto.AES_128_GCM -> Some EverCrypt.AES128_GCM
  | CoreCrypto.AES_256_GCM -> Some EverCrypt.AES256_GCM
  | CoreCrypto.CHACHA20_POLY1305 -> Some EverCrypt.CHACHA20_POLY1305
  | _ -> None
let aeadAlg_for_evercrypt (a:aeadAlg{Some? (evercrypt_aeadAlg_option_of_aead_cipher a)})
  : EverCrypt.aead_alg
  = Some?.v (evercrypt_aeadAlg_option_of_aead_cipher a)

// Real IVs must be created with the internal
// salting function below.
let iv_length i = CC.aeadRealIVSize (alg i)
abstract type iv (i:id) = lbytes (iv_length i)
let key_length i = CC.aeadKeySize (alg i)

// Salt is the static part of IVs
let salt_length (i:id) =
  match pv_of_id i with
  | TLS_1p3 -> iv_length i
  | _ ->
    match alg i with
    | CC.AES_128_GCM       -> 4
    | CC.AES_128_CCM       -> 4
    | CC.AES_128_CCM_8     -> 4
    | CC.AES_256_GCM       -> 4
    | CC.AES_256_CCM       -> 4
    | CC.AES_256_CCM_8     -> 4
    | CC.CHACHA20_POLY1305 -> 12

// Length of the explicit (sent on wire) IV
let explicit_iv_length (i:id) =
  match pv_of_id i with
  | TLS_1p3 -> 0
  | _ ->
    match alg i with
    | CC.AES_128_GCM       -> 8
    | CC.AES_128_CCM       -> 8
    | CC.AES_128_CCM_8     -> 8
    | CC.AES_256_GCM       -> 8
    | CC.AES_256_CCM       -> 8
    | CC.AES_256_CCM_8     -> 8
    | CC.CHACHA20_POLY1305 -> 0

type key  (i:id) = lbytes (key_length i)
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
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    iv_length i
  | _ -> (iv_length i) - (salt_length i)

type nonce i = lbytes (noncelen i)

let coerce_iv (i:id) (b:lbytes (iv_length i)) : Tot (iv i) = b

let create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i)
  : Tot (i:iv i) =
  let salt = salt_of_state st in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    xor_ #(iv_length i) n salt
  | _ ->
    salt @| n

(* Necessary for injectivity of the nonce-to-IV construction in TLS 1.3 *)
#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --admit_smt_queries true"
let lemma_nonce_iv (#i:id) (#rw:rw) (st:state i rw) (n1:nonce i) (n2:nonce i)
  : Lemma (create_nonce st n1 = create_nonce st n2 ==> n1 = n2)
  =
  let salt = salt_of_state st in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    xor_idempotent (FStar.UInt32.uint_to_t (iv_length i)) n1 salt;
    xor_idempotent (FStar.UInt32.uint_to_t (iv_length i)) n2 salt
  | _ ->
    if (salt @| n1) = (salt @| n2) then
      () //lemma_append_inj salt n1 salt n2 //TODO bytes NS 09/27
#reset-options

let genPost (#i:id) (parent:rgn) h0 (w:writer i) h1 =
  modifies_none h0 h1

#set-options "--max_fuel 0 --max_ifuel 1"
let gen (i:id) (r:rgn) : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (genPost r))
  =
  push_frame ();
  let salt : salt i = Random.sample (salt_length i) in
  let klen = CC.aeadKeySize (alg i) in
  assume (FStar.UInt.size klen 32);
  let kv: key i = Random.sample klen in
  let len32 = UInt32.uint_to_t klen in
  let kvb = LB.alloca 0uy len32 in
  FStar.Bytes.store_bytes kv kvb;
  let h = get () in
  assume (Some? (evercrypt_aeadAlg_option_of_aead_cipher (alg i)));
  assume (EverCrypt.Specs.aead_create_pre h); //effectively False
  let st = EverCrypt.aead_create (aeadAlg_for_evercrypt (alg i)) kvb in
  let res : state i Writer = st, (kv, salt) in
  let h1 = get () in
  pop_frame ();
  res

let leak (#i:id) (#rw:rw) (st:state i rw)
  : ST (key i * salt i)
  (requires (fun h0 -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  snd st

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --admit_smt_queries true"
let genReader (parent:rgn) (#i:id) (st:writer i) : ST (reader i)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let (s, k) = st in
  (s, k) <: reader i
#reset-options

#reset-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let coerce (i:id) (r:rgn) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  push_frame ();
  dbg ("COERCE(K="^(hex_of_bytes k)^", SIV="^(hex_of_bytes s)^")");
  assume (~ (Flag.prf i));
  assume(false);
  let len = length k in
  let len32 = FStar.UInt32.uint_to_t len in
  let kvb = LB.alloca 0uy len32 in
  FStar.Bytes.store_bytes k kvb;
  let st = EverCrypt.aead_create (aeadAlg_for_evercrypt (alg i)) kvb in
  pop_frame ();
  st, (k,s)
#reset-options

type plainlen = n:nat{n <= max_TLSPlaintext_fragment_length}
(* irreducible *)
type plain (i:id) (l:plainlen) = b:lbytes l
let repr (#i:id) (#l:plainlen) (p:plain i l) : Tot (lbytes l) = p

let adlen i = match pv_of_id i with
  | TLS_1p3 -> 0 | _ -> 13
type adata i = lbytes (adlen i)

let taglen i = CC.aeadTagSize (alg i)
let cipherlen i (l:plainlen) : n:nat{n >= taglen i} = l + taglen i
type cipher i (l:plainlen) = lbytes (cipherlen i l)

open EverCrypt.Helpers
module LM = LowStar.Modifies

#set-options "--max_fuel 0 --max_ifuel 0"
let from_bytes (b:bytes{length b <> 0}) : StackInline uint8_p
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 ->
    LB.(modifies loc_none h0 h1) /\
    LB.live h1 buf /\
    LB.unused_in buf h0 /\
    LB.length buf = length b /\
    Bytes.reveal b `Seq.equal` LB.as_seq h1 buf))
  =
  let h0 = get () in
  let len = FStar.UInt32.uint_to_t (length b) in
  let lb = LB.alloca 0uy len in
  FStar.Bytes.store_bytes b lb;
  let h1 = get () in
  LB.(modifies_only_not_unused_in loc_none h0 h1);
  lb

#set-options "--admit_smt_queries true"
let encrypt (#i:id) (#l:plainlen) (w:writer i) (iv:iv i) (ad:adata i) (plain:plain i l)
  : ST (cipher:cipher i l)
       (requires (fun h -> True))
       (ensures (fun h0 cipher h1 -> modifies_none h0 h1))
  =
  push_frame ();
  let adlen = uint_to_t (length ad) in
  let plainlen = uint_to_t l in
  let taglen = uint_to_t (taglen i) in
  let cipherlen = plainlen +^ taglen in
  let ad = from_bytes ad in
  let cipher_tag = LB.alloca 0uy cipherlen in
  let cipher = LB.sub cipher_tag 0ul plainlen in
  let tag = LB.sub cipher_tag plainlen taglen in
  let iv = from_bytes iv in
  let plain =
    if not (TLSInfo.safeId i)
    then from_bytes plain
    else LB.alloca 0uy plainlen
  in
  EverCrypt.aead_encrypt (fst w) iv ad adlen plain plainlen cipher tag;
  let cipher_tag_res = FStar.Bytes.of_buffer cipherlen cipher_tag in
  pop_frame();
  cipher_tag_res

let decrypt (#i:id) (#l:plainlen) (st:reader i) (iv:iv i) (ad:adata i) (cipher:cipher i l)
  : ST (co:option (plain i l))
       (requires (fun _ -> True))
//  (requires (fun _ ->
//    FStar.UInt.size (length ad) 32
//    /\ FStar.UInt.size (length cipher) 32
//    /\ length cipher >= CC.aeadTagSize (alg i))
       (ensures (fun h0 plain h1 -> modifies_none h0 h1))
  =
  push_frame();
  let iv = from_bytes iv in
  let adlen = uint_to_t (length ad) in
  let ad = from_bytes ad in
  let plainlen = uint_to_t l in
  let taglen = uint_to_t (taglen i) in
  let cipher_tag_buf = from_bytes cipher in
  let cipher = LB.sub cipher_tag_buf 0ul plainlen in
  let tag = LB.sub cipher_tag_buf plainlen taglen in
  let plain = LB.alloca 0uy plainlen in
  let ok = EverCrypt.aead_decrypt (fst st) iv ad adlen plain plainlen cipher tag in
  let ret =
    if ok = 1ul
    then Some (FStar.Bytes.of_buffer plainlen plain)
    else None
  in
  pop_frame();
  ret

  (*
  let r =
    if debug then
      let ivh = hex_of_bytes iv in
      let adh = hex_of_bytes ad in
      let ch = hex_of_bytes cipher in
      let ph =
        match plain with
        | None -> "FAIL"
        | Some p -> hex_of_bytes p
        in
      IO.debug_print_string ((prov())^": DECRYPT[IV="^ivh^",AD="^adh^",C="^ch^"] = "^ph^"\n")
    else false in
  if r then plain else plain
 *)


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
