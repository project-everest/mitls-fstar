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

let iv (i:id) = lbytes (iv_length i)

let coerce_iv i b = b

#reset-options "--using_facts_from '* -LowParse.Spec.Base' --z3rlimit 32"
 
let create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i): Tot (i:iv i) =
  let salt = salt_of_state st in
  match (TLSInfo.pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, EverCrypt.CHACHA20_POLY1305) ->
    xor_ #(iv_length i) n salt
  | _ ->
    assert(Bytes.length salt + Bytes.length n = iv_length i);
    salt @| n

(* Necessary for injectivity of the nonce-to-IV construction in TLS 1.3 *)
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --admit_smt_queries true"
let lemma_nonce_iv (#i:id) (#rw:rw) (st:state i rw) (n1:nonce i) (n2:nonce i)
  : Lemma (create_nonce st n1 = create_nonce st n2 ==> n1 = n2)
  =
  let salt = salt_of_state st in
  match (TLSInfo.pv_of_id i, alg' i) with
  | (TLS_1p3, _) | (_, EverCrypt.CHACHA20_POLY1305) ->
    xor_idempotent (UInt32.uint_to_t (iv_length i)) n1 salt;
    xor_idempotent (UInt32.uint_to_t (iv_length i)) n2 salt
  | _ ->
    if (salt @| n1) = (salt @| n2) then
      () //lemma_append_inj salt n1 salt n2 //TODO bytes NS 09/27
#pop-options

#set-options "--max_fuel 0 --max_ifuel 1"
let gen (i:id) (r:rgn) : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (genPost r))
  =
  assume False;//18-09-03 
  push_frame ();
  let salt : salt i = Random.sample (salt_length i) in
  let klen = UInt32.v (EverCrypt.aead_keyLen (alg i)) in
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
  (requires (fun h0 -> ~(TLSInfo.authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  snd st

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --admit_smt_queries true"
let genReader (parent:rgn) (#i:id) (st:writer i) : ST (reader i)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let (s, k) = st in
  (s, k) <: reader i
#pop-options

#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let coerce (i:id) (r:rgn) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> ~(TLSInfo.authId i)))
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
#pop-options

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
  dbg ("ENCRYPT[N="^(hex_of_bytes iv)^",AD="^(hex_of_bytes ad)^"]");
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
  dbg ("DECRYPT[N="^(hex_of_bytes iv)^",AD="^(hex_of_bytes ad)^"]");
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
