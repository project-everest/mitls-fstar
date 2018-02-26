module AEADProvider

open FStar.HyperStack
open FStar.Seq
open FStar.Bytes

open TLSConstants
open TLSInfo
open FStar.UInt32

module CC = CoreCrypto
module OAEAD = AEADOpenssl

type provider =
  | OpenSSLProvider

let use_provider () : Tot provider =
  OpenSSLProvider
let debug = false

let prov() =
  match use_provider() with
  | OpenSSLProvider -> "OpenSSLProvider"

(***********************************************************************)

type id = i:id{~(PlaintextID? i) /\ AEAD? (aeAlg_of_id i)}
let alg (i:id) = let AEAD aead _ = aeAlg_of_id i in aead

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

noeq type state (i:id) (r:rw) =
| OpenSSL: st:OAEAD.state i r -> salt:salt i -> state i r

type writer i = s:state i Writer
type reader i = s:state i Reader

let noncelen (i:id) =
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    iv_length i
  | _ -> (iv_length i) - (salt_length i)

type nonce i = lbytes (noncelen i)

let coerce_iv (i:id) (b:lbytes (iv_length i)) : Tot (iv i) = b

let create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i)
  : Tot (i:iv i) =
  let salt : salt i = match st with
    | OpenSSL _ s -> s in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    xor (iv_length i) n salt
  | _ ->
    let r = salt @| n in
    lemma_len_append salt n; r

(* Necessary for injectivity of the nonce-to-IV construction in TLS 1.3 *)
assume val lemma_xor_idempotent: n:nat -> b1:lbytes n -> b2:lbytes n ->
  Lemma (xor n b2 (xor n b1 b2) = b1)

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let lemma_nonce_iv (#i:id) (#rw:rw) (st:state i rw) (n1:nonce i) (n2:nonce i)
  : Lemma (create_nonce st n1 = create_nonce st n2 ==> n1 = n2)
  =
  let salt : salt i = match st with
    | OpenSSL _ s -> s in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    lemma_xor_idempotent (iv_length i) n1 salt;
    lemma_xor_idempotent (iv_length i) n2 salt
  | _ ->
    if (salt @| n1) = (salt @| n2) then
      lemma_append_inj salt n1 salt n2

type empty_log (#i:id) (#rw:rw) (st:state i rw) h =
  (match st with
  | OpenSSL s _ -> OAEAD.empty_log s h) // TODO

let region (#i:id) (#rw:rw) (st:state i rw) =
  (match st with
  | OpenSSL st _ -> OAEAD.State?.region st) // TODO

let log_region (#i:id) (#rw:rw) (st:state i rw) =
  match st with
  | OpenSSL st _ -> OAEAD.State?.log_region st

let st_inv (#i:id) (#rw:rw) (st:state i rw) h =
  match st with
  | OpenSSL st _ -> True

let genPost (#i:id) (parent:rgn) h0 (w:writer i) h1 =
  modifies_none h0 h1 /\
  extends (region w) parent /\
  fresh_region (region w) h0 h1 /\
  color (region w) = color parent /\
  empty_log w h1 /\
  st_inv w h1

let gen (i:id) (r:rgn) : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (genPost r))
  =
  let salt : salt i = CC.random (salt_length i) in
  match use_provider() with
  | OpenSSLProvider ->
    let st : OAEAD.state i Writer = OAEAD.gen r i in
    OpenSSL st salt

let leak (#i:id) (#rw:rw) (st:state i rw)
  : ST (key i * salt i)
  (requires (fun h0 -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  match st with
  | OpenSSL st s -> (OAEAD.leak st, s)

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
let genReader (parent:rgn) (#i:id) (st:writer i) : ST (reader i)
  (requires (fun h -> HyperStack.disjoint parent (region st)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  match st with
  | OpenSSL w salt ->
    // CoreCrypto state is in an external region
    OpenSSL (OAEAD.genReader parent w) salt

let coerce (i:id) (r:rgn) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let w =
    match use_provider() with
    | OpenSSLProvider ->
      OpenSSL (OAEAD.coerce r i k) s
    in
  let r =
    if debug then
      IO.debug_print_string ((prov())^": COERCE(K="^(hex_of_bytes k)^")\n")
    else false in
  if r then w else w

type plainlen = n:nat{n <= max_TLSPlaintext_fragment_length}
(* irreducible *) type plain (i:id) (l:plainlen) = b:lbytes l
let repr (#i:id) (#l:plainlen) (p:plain i l) : Tot (lbytes l) = p

let adlen i = match pv_of_id i with
  | TLS_1p3 -> 0 | _ -> 13
type adata i = lbytes (adlen i)

let taglen i = CC.aeadTagSize (alg i)
let cipherlen i (l:plainlen) : n:nat{n >= taglen i} = l + taglen i
type cipher i (l:plainlen) = lbytes (cipherlen i l)

type fresh_iv (#i:id{authId i}) (w:writer i) (iv:iv i) h =
  (match w with
  | OpenSSL st _ -> OAEAD.fresh_iv #i st iv h)

let logged_iv (#i:id{authId i}) (#l:plainlen) (#rw:rw) (s:state i rw) (iv:iv i)
              (ad:adata i) (p:plain i l) (c:cipher i l) h =
  (match s with
  | OpenSSL st _ -> OAEAD.logged_iv #i #rw st iv (OAEAD.Entry ad p c) h
  | _ -> True)

// ADL Jan 3: PlanA changes TODO
#set-options "--lax"

let encrypt (#i:id) (#l:plainlen) (w:writer i) (iv:iv i) (ad:adata i) (plain:plain i l)
  : ST (cipher:cipher i l)
  (requires (fun h ->
    st_inv w h /\
    (authId i ==> (Flag.prf i /\ fresh_iv #i w iv h)) /\
    FStar.UInt.size (length ad) 32 /\ FStar.UInt.size l 32))
  (ensures (fun h0 cipher h1 -> modifies_one (log_region w) h0 h1))
  =
  let cipher =
    match w with
    | OpenSSL st _ -> OAEAD.encrypt st iv ad plain
  in
  cipher

  (*
  let r =
    if debug then
      let ivh = hex_of_bytes iv in
      let adh = hex_of_bytes ad in
      let ph = hex_of_bytes plain in
      let ch = hex_of_bytes cipher in
      IO.debug_print_string ((prov())^": ENC[IV="^ivh^",AD="^adh^",PLAIN="^ph^"] = "^ch^"\n")
    else false in
  if r then cipher else cipher
*)

let decrypt (#i:id) (#l:plainlen) (st:reader i) (iv:iv i) (ad:adata i) (cipher:cipher i l)
  : ST (co:option (plain i l))
  (requires (fun _ -> True))
//  (requires (fun _ ->
//    FStar.UInt.size (length ad) 32
//    /\ FStar.UInt.size (length cipher) 32
//    /\ length cipher >= CC.aeadTagSize (alg i))
  (ensures (fun h0 plain h1 ->
    modifies_none h0 h1
  ))
  =
  let plain =
    match st with
    | OpenSSL st _ -> OAEAD.decrypt st iv ad cipher
    in
  plain

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
