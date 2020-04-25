module ConnectionTable_Aux

module AE = Crypto.AEAD
module B = LowStar.Buffer
module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap
module S = Spec.Agile.AEAD
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let connection_id = UInt8.t

let configuration = UInt32.t

let alg = S.AES128_GCM

let cookie = c:AE.cipher_p alg
  {B.length c == 64 + AE.iv_length + S.tag_length alg}

let cookie_rgn = Mem.tls_define_region
let table_rgn  = Mem.tls_tables_region
let other_rgn  = Mem.tls_psk_region

let random = Seq.lseq UInt8.t 32

let id_of_random (r:random) : connection_id =
  Seq.index r 0

noeq
type client_hello =
  | CH1: random -> client_hello
  | CH2: random -> ck:cookie{B.frameOf ck == other_rgn} -> client_hello

let ch_random = function
  | CH1 r -> r
  | CH2 r _ -> r
  
let has_cookie = CH2?

let get_cookie (ch:client_hello{has_cookie ch}) =
  let CH2 _ cookie = ch in
  cookie

let ch_of_cookie (ch:client_hello{has_cookie ch}) =
  let CH2 random _ = ch in
  CH1 random

val ch_compatible: ch:client_hello -> cfg:configuration -> bool

let rgn = table_rgn

let model = Flags.model && Flags.ideal_AEAD

let maybe_id = if model then connection_id else unit

noeq
type connection =
  | Init: cfg:configuration -> connection
  | Sent_HRR: ch:client_hello -> connection
  | Sent_ServerHello: ch:client_hello -> id1:maybe_id -> connection
  | Complete: ch:client_hello -> id1:maybe_id -> connection

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Init _, Sent_HRR _ -> True
  | Init _, Sent_ServerHello _ _ -> True
  | Sent_ServerHello ch id1, Complete ch' id1' -> ch == ch' /\ id1 == id1'
  | _, _ -> False

let rel : Preorder.preorder connection = FStar.ReflexiveTransitiveClosure.closure step

// Store the ID rather than making it a parameter?
let connection_ref (id:maybe_id) = 
  r:HST.mmmref connection rel{HS.frameOf r `HS.extends` rgn}

// References to connections live in pairwise disjoint regions
val minv (m:T.partial_dependent_map maybe_id connection_ref) : Type0

unfold
let _connection_table = T.t rgn maybe_id connection_ref minv

unfold
let connection_table = if model then _connection_table else unit


inline_for_extraction noextract
val empty: m: T.imap maybe_id connection_ref minv{m == T.empty}

val inv: _connection_table -> HS.mem -> Type0

val framing: h0: HS.mem -> t:_connection_table -> l:B.loc -> h1:HS.mem -> Lemma
  (requires B.modifies l h0 h1 /\ 
            B.loc_disjoint l (B.loc_all_regions_from true rgn) /\
            h0 `HS.contains` t /\
            (forall a rel (r:HS.mreference a rel). 
              HS.frameOf r `HS.extends` table_rgn ==> 
              h1 `HS.contains` r ==> h0 `HS.contains` r) /\
            inv t h0)
  (ensures  inv t h1)

inline_for_extraction
val alloc: unit -> HST.ST connection_table
  (requires fun _ ->
    if model then HST.witnessed (HST.region_contains_pred rgn)
    else True)
  (ensures  fun h0 t h1 -> 
    if model then HST.ralloc_post #_ #T.grows rgn empty h0 t h1 /\ inv t h1
    else h0 == h1)

val table : connection_table 

let cookie_phi s = 
  Seq.length s >= 32 /\
  (if model then
    let random = Seq.slice s 0 32 in
    let id = id_of_random random in
    let t:_connection_table = table in
    HST.token_p t (fun h -> 
      T.defined t id h /\
      (let c = T.value_of t id h in
      HST.token_p c (fun h' -> 
        Sent_HRR? (HS.sel h' c) /\
        CH1 random == Sent_HRR?.ch (HS.sel h' c))))
   else True)
