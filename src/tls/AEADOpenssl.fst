(*--build-config
options:--use_hints --fstar_home ../../../FStar --detail_errors --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module AEADOpenssl

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes
open CoreCrypto

open TLSConstants
open TLSInfo

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef

type id = i:id{~(is_PlaintextID i) /\ is_AEAD (aeAlg_of_id i)}
let alg (i:id) = AEAD._0 (aeAlg_of_id i)

let keylen i = aeadKeySize (alg i)
let taglen i = aeadTagSize (alg i)
let ivlen i = aeadRealIVSize (alg i)

type key (i:id) = lbytes (keylen i)
type iv  (i:id) = lbytes (ivlen i)

// ADL: experimental style for plaintexts
// Built-in plaintext abstraction using "irreductible"
// (to simulate abstract plaintexts within the same module)
type plainlen = n:nat{n <= max_TLSPlaintext_fragment_length}
(* irreducible *) type plain (i:id) (l:plainlen) = lbytes l
let repr (#i:id) (#l:plainlen) (p:plain i l) : Tot (lbytes l) = p

// Additional data
let adlen i = match pv_of_id i with
  | TLS_1p3 -> 0 | _ -> 13
type adata i = lbytes (adlen i)

// Ciphertexts
let cipherlen i (l:plainlen) : n:nat{n >= taglen i} = l + taglen i
type cipher i (l:plainlen) = lbytes (cipherlen i l)

// Log
type entry (#i:id) (iv:iv i) =
  | Entry:
    #l:plainlen  ->
    ad:adata i   ->
    p:plain i l  ->
    c:cipher i l ->
    entry iv

type no_inv m = True
let ideal_log (r:rgn) (i:id) = MM.t r (iv i) entry no_inv
let log_ref (r:rgn) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:rgn) (#i:id) (l:log_ref r i{authId i})
 : Tot (ideal_log r i) = l

type logrgn (r:rgn) (rw:rw) =
  logr:rgn{
    if rw = Writer then logr = r
    else HyperHeap.disjoint r logr}

noeq type state (i:id) (rw:rw) =
  | State:
    #region: rgn ->
    #log_region: logrgn region rw ->
    key: key i ->
    log: log_ref log_region i ->
    state i rw

type empty_log (#i:id) (#rw:rw) (st:state i rw) h =
  authId i ==>
    (MR.m_contains (ilog st.log) h /\
     MR.m_sel h (ilog st.log) == MM.empty_map (iv i) entry)

type writer i = s:state i Writer
type reader i = s:state i Reader

let genPost (#i:id) (parent:rgn) h0 (w:writer i) h1 =
  modifies Set.empty h0 h1 /\
  extends w.region parent /\
  stronger_fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  empty_log w h1

#set-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val gen: parent:rgn -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let gen parent i =
  let kv : key i = CoreCrypto.random (keylen i) in
  let writer_r = new_region parent in
  cut (is_eternal_region writer_r);
  if authId i then
    let log : ideal_log writer_r i = MM.alloc #writer_r #(iv i) #entry #no_inv in
    let w : writer i = State #i #Writer #writer_r #writer_r kv log in w
  else
    let w : writer i = State #i #Writer #writer_r #writer_r kv () in w

// A reader r peered with the writer w
type peered (#i:id) (w:writer i) =
  r:reader i{
   w.key = r.key /\
   r.log_region = w.region /\
   eq2 #(log_ref w.region i) w.log r.log
  }

val genReader: parent:rgn -> #i:id -> w:writer i -> ST (peered w)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region))
  (ensures (fun h0 r h1 ->
    modifies Set.empty h0 h1 /\
    extends r.region parent /\
    color r.region = color parent /\
    stronger_fresh_region r.region h0 h1))
let genReader parent #i w =
  let reader_r = new_region parent in
  if authId i then
    let log : ideal_log w.region i = w.log in
    State #i #Reader #reader_r #w.region w.key log
  else
    State #i #Reader #reader_r #w.region w.key ()

val coerce: parent:rgn -> i:id{~(authId i)} -> kv:key i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let coerce parent i kv =
  let writer_r = new_region parent in
  State #i #Writer #writer_r #writer_r kv ()

val leak: #i:id -> #role:rw -> state i role -> ST (key i)
  (requires (fun h0 -> ~(authId i)))
  (ensures  (fun h0 r h1 -> modifies_none h0 h1))
let leak #i #role s = State.key s

val encrypt:
  #i:id ->
  #l:plainlen ->
  e:writer i ->
  iv:iv i ->
  ad:adata i ->
  p:plain i l ->
  ST (cipher i l)
  (requires (fun h0 ->
    // Do not encrypt twice with the same IV
    (authId i ==> is_None (MM.sel (MR.m_sel h0 (ilog e.log)) iv))
  ))
  (ensures (fun h0 c h1 ->
    modifies_one e.log_region h0 h1 /\
    (authId i ==> MR.witnessed (MM.contains (ilog e.log) iv (Entry ad p c)))
  ))

let encrypt #i #l e iv ad p =
  if authId i then
    begin
      let log = ilog e.log in
      MR.m_recall log;
      let c = CoreCrypto.random (cipherlen i l) in
      MM.extend log iv (Entry ad p c);
      c
    end
  else
    aead_encrypt (alg i) (State.key e) iv ad (repr p)

val decrypt:
  #i:id ->
  #l:plainlen ->
  d:reader i ->
  iv:iv i ->
  ad:adata i ->
  c:cipher i l ->
  ST (option (plain i l))
  (requires (fun h0 -> True))
  (ensures  (fun h0 res h1 ->
     modifies Set.empty h0 h1 /\
     ((authId i /\ is_Some res) ==>
       MR.witnessed (MM.contains (ilog d.log) iv (Entry ad (Some.v res) c)))
  ))

let decrypt #i #l d iv ad c =
  if authId i then
   begin
    let log = ilog d.log in
    MR.m_recall log;
    match MM.lookup log iv with
    | None -> None
    | Some (Entry ad' p c') ->
      if ad' = ad && c' = c then
       begin
        cut (MR.witnessed (MM.contains log iv (Entry ad p c)));
        Some p
       end
      else None
   end
  else
    match aead_decrypt (alg i) (State.key d) iv ad c with
    | Some p -> assert (length p + aeadTagSize (alg i) = length c); Some p
    | None -> None
