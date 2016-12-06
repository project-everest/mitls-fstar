(*--build-config
options:--use_hints --fstar_home ../../../FStar --detail_errors --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module AEADProvider

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes

open TLSConstants
open TLSInfo
open FStar.UInt32

module Plain = Crypto.Plain
module CC = CoreCrypto
module CAEAD = LowCProvider
module AE = Crypto.AEAD
module CB = Crypto.Symmetric.Bytes
module OAEAD = AEADOpenssl

type provider =
  | OpenSSLProvider
  | LowProvider
  | LowCProvider

let use_provider () : Tot provider =
  OpenSSLProvider
let debug = false

let prov() =
  match use_provider() with
  | OpenSSLProvider -> "OpenSSLProvider"
  | LowCProvider -> "LowCProvider"
  | LowProvider -> "LowProvider"

type u32 = FStar.UInt32.t

(**
Functions to go back and forth between Platform.Bytes Buffers
**)
#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val to_bytes: l:nat -> buf:CB.lbuffer l -> STL (b:bytes{length b = l})
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 s h1 -> h0 == h1 ))
let rec to_bytes l buf =
  if l = 0 then empty_bytes
  else
    let b = UInt8.v (Buffer.index buf 0ul) in
    let s = abyte (Char.char_of_int b) in
    let t = to_bytes (l - 1) (Buffer.sub buf 1ul (uint_to_t (l-1))) in
    let r = s @| t in
    (lemma_len_append s t; r)

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val store_bytes: len:nat -> buf:CB.lbuffer len -> i:nat{i <= len} -> b:bytes{length b = len} -> STL unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1))
let rec store_bytes len buf i s =
  if i < len then
    let () = Buffer.upd buf (uint_to_t i) (UInt8.uint_to_t (Char.int_of_char (index s i))) in
    store_bytes len buf (i + 1) s

val from_bytes: b:bytes{FStar.UInt.fits (length b) 32} -> StackInline (CB.lbuffer (length b))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> Buffer.modifies_0 h0 h1 /\ Buffer.live h1 r ))
let from_bytes b =
  let buf = Buffer.create 0uy (uint_to_t (length b)) in
  store_bytes (length b) buf 0 b;
  buf

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
| LowC: st:CAEAD.aead_state -> key:key i -> salt:salt i -> state i r
| LowLevel: st:Crypto.AEAD.Invariant.state i (Crypto.Indexing.rw2rw r) -> salt:salt i -> state i r

type writer i = s:state i Writer
type reader i = s:state i Reader

let noncelen (i:id) =
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    iv_length i
  | _ -> (iv_length i) - (salt_length i)

type nonce i = lbytes (noncelen i)

let create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i)
  : Tot (i:iv i) =
  let salt : salt i = match st with
    | OpenSSL _ s -> s
    | LowLevel _ s -> s
    | LowC _ _ s -> s in
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
    | OpenSSL _ s -> s
    | LowLevel _ s -> s
    | LowC _ _ s -> s in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    lemma_xor_idempotent (iv_length i) n1 salt;
    lemma_xor_idempotent (iv_length i) n2 salt
  | _ ->
    if (salt @| n1) = (salt @| n2) then
      lemma_append_inj salt n1 salt n2

type empty_log (#i:id) (#rw:rw) (st:state i rw) h =
  (match st with
  | OpenSSL s _ -> OAEAD.empty_log s h
  | LowC st _ _ -> True // TODO
  | LowLevel st _ -> True) // TODO

let region (#i:id) (#rw:rw) (st:state i rw) =
  (match st with
  | OpenSSL st _ -> OAEAD.State?.region st
  | LowC st _ _ -> tls_region // TODO
  | LowLevel st _ -> tls_region) // TODO

let log_region (#i:id) (#rw:rw) (st:state i rw) =
  match st with
  | OpenSSL st _ -> OAEAD.State?.log_region st
  | LowC st _ _ -> root
  | LowLevel st _ -> root

let genPost (#i:id) (parent:rgn) h0 (w:writer i) h1 =
  modifies_none h0 h1 /\
  extends (region w) parent /\
  stronger_fresh_region (region w) h0 h1 /\
  color (region w) = color parent /\
  empty_log w h1

let gen (i:id) (r:rgn) : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (genPost r))
  =
  match use_provider() with
  | OpenSSLProvider ->
    let salt : salt i = CC.random (salt_length i) in
    let st : OAEAD.state i Writer = OAEAD.gen r i in
    OpenSSL st salt
  | LowCProvider ->
    assume false; // TODO
    let kv: key i = CC.random (CC.aeadKeySize (alg i)) in
    let salt: salt i = CC.random (salt_length i) in
    let st = CAEAD.aead_create (alg i) kv in
    LowC st kv salt
  | LowProvider ->
    assume false; // TODO
    let salt : salt i = CC.random (salt_length i) in
    let st = AE.gen i r in
    LowLevel st salt

let leak (#i:id{~(Flag.prf i)}) (#rw:rw) (st:state i rw)
  : ST (key i * salt i)
  (requires (fun h0 -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  match st with
  | OpenSSL st s -> (OAEAD.leak st, s)
  | LowC st k s -> (k, s)
  | LowLevel st s ->
    assume (false);
    let k = AE.leak st in
    (to_bytes (key_length i) k, s)

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
let genReader (parent:rgn) (#i:id) (st:writer i) : ST (reader i)
  (requires (fun h -> HyperHeap.disjoint parent (region st)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  match st with
  | OpenSSL w salt ->
    // CoreCrypto state is in an external region
    OpenSSL (OAEAD.genReader parent w) salt
  | LowLevel st salt ->
    assume false;
    let st' : Crypto.AEAD.Invariant.state i Crypto.Indexing.Reader = AE.genReader st in
    LowLevel st' salt
  | LowC st k s ->
    assume false;
    LowC st k s


let coerce (i:id) (r:rgn) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let w =
    match use_provider() with
    | OpenSSLProvider ->
      OpenSSL (OAEAD.coerce r i k) s
    | LowCProvider ->
      let st = CAEAD.aead_create (alg i) k in
      LowC st k s
    | LowProvider ->
      let st = AE.coerce i r (from_bytes k) in
      LowLevel st s
    in
  let r =
    if debug then
      IO.debug_print_string ((prov())^": COERCE(K="^(hex_of_bytes k)^")\n")
    else false in
  if r then w else w

type plainlen = n:nat{n <= max_TLSPlaintext_fragment_length}
(* irreducible *) type plain (i:id) (l:plainlen) = lbytes l
let repr (#i:id) (#l:plainlen) (p:plain i l) : Tot (lbytes l) = p

let adlen i = match pv_of_id i with
  | TLS_1p3 -> 0 | _ -> 13
type adata i = lbytes (adlen i)

let taglen i = CC.aeadTagSize (alg i)
let cipherlen i (l:plainlen) : n:nat{n >= taglen i} = l + taglen i
type cipher i (l:plainlen) = lbytes (cipherlen i l)

type fresh_iv (#i:id{authId i}) (w:writer i) (iv:iv i) h =
  (match w with
  | OpenSSL st _ -> OAEAD.fresh_iv #i st iv h
  | _ -> True)

let logged_iv (#i:id{authId i}) (#l:plainlen) (#rw:rw) (s:state i rw) (iv:iv i)
              (ad:adata i) (p:plain i l) (c:cipher i l) h =
  (match s with
  | OpenSSL st _ -> OAEAD.logged_iv #i #rw st iv (OAEAD.Entry ad p c) h
  | _ -> True)

let encrypt (#i:id) (#l:plainlen) (w:writer i) (iv:iv i) (ad:adata i) (plain:plain i l)
  : ST (cipher:cipher i l)
  (requires (fun _ ->
    FStar.UInt.size (length ad) 32 /\ FStar.UInt.size l 32))
  (ensures (fun h0 cipher h1 -> True))
  =
  let cipher =
    match w with
    | OpenSSL st _ -> OAEAD.encrypt st iv ad plain
    | LowC st _ _ -> CAEAD.aead_encrypt st iv ad plain
    | LowLevel st _ ->
      let iv = CB.load_uint128 12ul (from_bytes iv) in
      let adlen = uint_to_t (length ad) in
      let ad = from_bytes ad in
      let plainlen = uint_to_t l in
      let cipherlen = uint_to_t (cipherlen i l) in
      let plainbuf = from_bytes plain in
      let plainba = CB.load_bytes plainlen plainbuf in
      let plainrepr = Plain.make #i l plainba in
      let plain = Plain.create i 0uy plainlen in
      Plain.store plainlen plain plainrepr;
      let cipher = Buffer.create 0uy cipherlen in
      AE.encrypt i st iv adlen ad plainlen plain cipher;
      to_bytes l cipher
    in
  let r =
    if debug then
      let ivh = hex_of_bytes iv in
      let adh = hex_of_bytes ad in
      let ph = hex_of_bytes plain in
      let ch = hex_of_bytes cipher in
      IO.debug_print_string ((prov())^": ENC[IV="^ivh^",AD="^adh^",PLAIN="^ph^"] = "^ch^"\n")
    else false in
  if r then cipher else cipher

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
    | LowC st _ _ -> CAEAD.aead_decrypt st iv ad cipher
    | LowLevel st _->
      let ivlen = uint_to_t (iv_length i) in
      let iv = CB.load_uint128 ivlen (from_bytes iv) in
      let adlen = uint_to_t (length ad) in
      let ad = from_bytes ad in
      let plainlen = uint_to_t l in
      let cbuf = from_bytes cipher in
      let plain = Plain.create i 0uy plainlen in
      if AE.decrypt i st iv adlen ad plainlen plain cbuf then
        Some (to_bytes l (Plain.bufferRepr #i plain))
      else None
    in
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
