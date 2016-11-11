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

// The purpose of this module is to provinde a unified interface
// for the CoreCrypto and low-level implementations of AEAD
// This file is TLS version-agnostic. To deal with the different
// treatment of implicit nonces, we provide a version-specific
// nonce computation function

// For now static flag
type provider =
  | CCProvider
  | LowProvider
  | LowCProvider

let use_provider () : Tot provider =
  LowCProvider
let debug = false

type u32 = FStar.UInt32.t

(**
Functions to go back and forth between Platform.Bytes Buffers
**)

val to_bytes: l:u32 -> buf:CB.lbuffer (v l) -> STL (b:bytes{length b = v l})
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 s h1 -> h0 == h1 ))
let rec to_bytes l buf =
  if l = 0ul then empty_bytes else
  let b = UInt8.v (Buffer.index buf 0ul) in
  let s = abyte (Char.char_of_int b) in
  let t = to_bytes (l -^ 1ul) (Buffer.sub buf 1ul (l -^ 1ul)) in
  s @| t

val store_bytes: len:u32 -> buf:CB.lbuffer (v len) -> i:u32 {i <=^ len} -> b:bytes{length b = v len} -> STL unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1))

let rec store_bytes len buf i s =
  if i <^ len then (
  Buffer.upd buf i (UInt8.uint_to_t (Char.int_of_char (index s (v i))));
  store_bytes len buf (i +^ 1ul) s )

val from_bytes: len:u32 -> bytes -> StackInline (CB.lbuffer (v len))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> Buffer.modifies_0 h0 h1 /\ Buffer.live h1 r ))
let from_bytes len b =
  let buf = Buffer.create 0uy len in
  (if length b = v len then store_bytes len buf 0ul b);
  buf

(***********************************************************************)

type id = i:id{~(is_PlaintextID i) /\ is_AEAD (aeAlg_of_id i)}
let alg i = let AEAD aead _ = aeAlg_of_id i in aead

// Real IVs must be created with the internal
// salting function below.
let iv_length i = CC.aeadRealIVSize (alg i)
abstract type iv (i:id) = lbytes (iv_length i)

let key_length i = CC.aeadKeySize (alg i)

// Salt is the static part of IVs
let salt_length i =
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
let explicit_iv_length i =
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
| CoreCrypto: key:key i -> salt:salt i -> state i r
| LowC: st:CAEAD.aead_state -> key:key i -> salt:salt i -> state i r
| LowLevel: st:Crypto.AEAD.Invariant.state i (Crypto.Indexing.rw2rw r) -> salt:salt i -> state i r

let noncelen i =
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    iv_length i
  | _ -> (iv_length i) - (salt_length i)

type nonce i = lbytes (noncelen i)

let create_nonce (#i:id) (#rw:rw) (s:state i rw) (n:nonce i) : Tot (iv i) =
  let salt = match s with
    | CoreCrypto _ s -> s
    | LowLevel _ s -> s
    | LowC _ _ s -> s in
  match (pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, CC.CHACHA20_POLY1305) ->
    xor (iv_length i) n salt
  | _ ->
    salt @| n

let gen (i:id) (r:rid)
  : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
  =
  match use_provider() with
  | CCProvider ->
    let kv : key i = CC.random (CC.aeadKeySize (alg i)) in
    let salt : salt i = CC.random (salt_length i) in
    CoreCrypto kv salt
  | LowCProvider ->
    let kv: key i = CC.random (CC.aeadKeySize (alg i)) in
    let salt: salt i = CC.random (salt_length i) in
    let st = CAEAD.aead_create (alg i) kv in
    LowC st kv salt
  | LowProvider ->
    let salt : salt i = CC.random (salt_length i) in
    let st = AE.gen i r in
    LowLevel st salt

let leak (#i:id{~(authId i)}) (#rw:rw) (st:state i rw)
  : ST (key i * salt i)
  (requires (fun h0 -> ~(authId i)))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
  =
  match st with
  | CoreCrypto k s -> (k, s)
  | LowC st k s -> (k, s)
  | LowLevel st s ->
    let k = AE.leak st in
    let ks = uint_to_t (CC.aeadKeySize (alg i)) in
    (to_bytes ks k, s)

// ADL TODO
// There is an issue connecting the stateful encryption in miTLS
// to the low-level crypto which currently shares the region between
// the reader and writer (this is not sound for some buffers in that
// region, for instance, the writer may write the the reader's key buffer)
let genReader (#i:id) (st:state i Writer)
  : ST (state i Reader)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
  =
  match use_provider() with
  | LowProvider ->
    let LowLevel st salt = st in
    let st' : Crypto.AEAD.Invariant.state i Crypto.Indexing.Reader = AE.genReader st in
    LowLevel st' salt
  | LowCProvider ->
    let LowC st k s = st in
    LowC st k s
  | CCProvider ->
    // CoreCrypto state is in an external region
    let CoreCrypto k s = st in
    CoreCrypto k s

let coerce (i:id) (r:rid) (k:key i) (s:salt i)
  : ST (state i Writer)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
  =
  match use_provider() with
  | CCProvider ->
    CoreCrypto k s
  | LowCProvider ->
    let st = CAEAD.aead_create (alg i) k in
    LowC st k s
  | LowProvider ->
    let ks = uint_to_t (CC.aeadKeySize (alg i)) in
    let st = AE.coerce i r (from_bytes ks k) in
    LowLevel st s

let encrypt (i:id) (st:state i Writer) (iv:iv i) (ad:bytes) (plain:bytes)
  : ST (cipher:bytes)
  (requires (fun _ ->
    FStar.UInt.size (length ad) 32 /\ FStar.UInt.size (length plain) 32))
  (ensures (fun h0 cipher h1 -> modifies Set.empty h0 h1 /\
    length cipher = length plain + CC.aeadTagSize (alg i)))
  =
  match use_provider() with
  | CCProvider ->
    let CoreCrypto key _ = st in
    let cipher = CC.aead_encrypt (alg i) key iv ad plain in
    let r =
      if debug then
        let kh = hex_of_bytes key in
        let ivh = hex_of_bytes iv in
        let adh = hex_of_bytes ad in
        let ph = hex_of_bytes plain in
        let ch = hex_of_bytes cipher in
        IO.debug_print_string ("CCProvider: ENCRYPT[K="^kh^",IV="^ivh^",AD="^adh^",PLAIN="^ph^"] = "^ch^"\n")
      else false in
    if r then cipher else cipher
  | LowCProvider ->
    let LowC st k s = st in
     CAEAD.aead_encrypt st iv ad plain
  | LowProvider ->
    let LowLevel st salt = st in
    let ivlen = uint_to_t (iv_length i) in
    let iv = from_bytes ivlen iv in
    let iv = CB.load_uint128 ivlen iv in
    let adlen = uint_to_t (length ad) in
    let plainlen = uint_to_t (length plain) in
    let cipherlen = uint_to_t (length plain + CC.aeadTagSize (alg i)) in
    let ad = from_bytes adlen ad in
    let plainbuf = from_bytes plainlen plain in
    let plainba = CB.load_bytes plainlen plainbuf in
    let plainrepr = Plain.make #i (length plain) plainba in
    let plain = Plain.create i 0uy plainlen in
    Plain.store plainlen plain plainrepr;
    let cipher = Buffer.create 0uy cipherlen in
    AE.encrypt i st iv adlen ad plainlen plain cipher;
    let cipher = to_bytes cipherlen cipher in
    cipher

let decrypt (i:id) (st:state i Reader) (iv:iv i) (ad:bytes) (cipher:bytes)
  : ST (co:option bytes)
  (requires (fun _ -> True))
//  (requires (fun _ ->
//    FStar.UInt.size (length ad) 32
//    /\ FStar.UInt.size (length cipher) 32
//    /\ length cipher >= CC.aeadTagSize (alg i))
  (ensures (fun h0 plain h1 -> modifies Set.empty h0 h1 /\
    is_Some plain ==> length cipher = length (Some.v plain) + CC.aeadTagSize (alg i)
  ))
  =
  match use_provider() with
  | CCProvider ->
    let CoreCrypto key _ = st in
    let plain = CC.aead_decrypt (alg i) key iv ad cipher in
    let r =
      if debug then
        let kh = hex_of_bytes key in
        let ivh = hex_of_bytes iv in
        let adh = hex_of_bytes ad in
        let ch = hex_of_bytes cipher in
        IO.debug_print_string ("CCProvider: DECRYPT[K="^kh^",IV="^ivh^",AD="^adh^",C="^ch^"] = "^(if is_Some plain then hex_of_bytes (Some.v plain) else "FAIL")^"\n")
      else false in
    if r then plain else plain
  | LowCProvider ->
    let LowC st _ _ = st in
    CAEAD.aead_decrypt st iv ad cipher
  | LowProvider ->
    let LowLevel st salt = st in
    let ivlen = uint_to_t (iv_length i) in
    let iv = from_bytes ivlen iv in
    let iv = CB.load_uint128 ivlen iv in 
    let adlen = uint_to_t (length ad) in
    let cipherlen = uint_to_t (length cipher) in
    let plainlen = uint_to_t (length cipher - CC.aeadTagSize (alg i)) in
    let ad = from_bytes adlen ad in
    let cbuf = from_bytes cipherlen cipher in
    let plain = Plain.create i 0uy plainlen in
    if AE.decrypt i st iv adlen ad plainlen plain cbuf then
      let plain = to_bytes plainlen (Plain.bufferRepr #i plain) in
      let r =
        if debug then
          let ph = hex_of_bytes plain in
          let ch = hex_of_bytes cipher in
          IO.debug_print_string ("LowProvider: decrypt[C="^ch^"] = "^ph^"\n")
        else false in
      (if r then Some plain else Some plain) // Outsmarting the Tot inliner
    else None

