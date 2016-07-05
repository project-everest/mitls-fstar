module StreamAE

// Authenticated encryption for a stream of variable-length plaintexts.
// Concretely, we use AES_GCM but any other algorithm would do.

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open StreamPlain
open MonotoneSeq
open FStar.Monotonic.RRef

module HH = FStar.HyperHeap

type id = i:id { pv_of_id i = TLS_1p3 /\ is_AEAD (aeAlg_of_id i) }

let alg (i:id) : CoreCrypto.aead_cipher = AEAD._0 (aeAlg_of_id i)

let ltag i : nat = CoreCrypto.aeadTagSize (alg i)

let cipherLen i (l:plainLen) : nat = l + ltag i

type cipher i (l:plainLen) = lbytes (cipherLen i l)

// will require proving before decryption
let lenCipher i (c:bytes { ltag i <= length c }) : nat = length c - ltag i

type entry (i:id) =
  | Entry: l:plainLen -> c:cipher i l -> p:plain i l -> entry i

private inline let min (a:int) (b:int) = if a < b then a else b
private inline let max (a:int) (b:int) = if a < b then b else a

// The length of the per-record nonce (iv_length) is set to max(8 bytes, N_MIN)
// for the AEAD algorithm (see [RFC5116] Section 4)
let iv_length i = max 8 (CoreCrypto.aeadRealIVSize (alg i))

// key materials 
type key (i:id) = lbytes (CoreCrypto.aeadKeySize (alg i)) 
type iv  (i:id) = lbytes (iv_length i)

let ideal_log (r:rid) (i:id) = MonotoneSeq.log_t r (entry i)

let log_ref (r:rid) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:rid) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) =
  l

let ideal_ctr (#l:rid) (r:rid) (i:id) (log:ideal_log l i) : Tot Type0 =
  MonotoneSeq.counter r log (aeadRecordIVSize (alg i))
  // An increasing counter, at most min(length log, 2^64-1)
  
let concrete_ctr (r:rid) (i:id) : Tot Type0 = 
  m_rref r seqn_t increases

let seqn_ref (#l:rid) (r:rid) (i:id) (log:log_ref l i) : Tot Type0 = 
  if authId i   
  then ideal_ctr r i (log <: ideal_log l i)
  else m_rref r seqn_t increases

let ctr (#l:rid) (#r:rid) (#i:id) (#log:log_ref l i) (c:seqn_ref r i log)
  : Tot (m_rref r (if authId i 
		   then counter_val #l #(entry i) r log (aeadRecordIVSize (alg i)) 
		   else seqn_t) 
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
type state (i:id) (rw:rw) = 
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> key: key i
         -> iv: iv i
         -> log: log_ref log_region i // ghost, subject to cryptographic assumption
         -> counter: seqn_ref region i log // types are sufficient to anti-alias log and counter
         -> state i rw

// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type writer i = s:state i Writer
type reader i = s:state i Reader


// We generate first the writer, then the reader (possibly several of them)
let genPost (#i:id) parent h0 (w:writer i) h1 =
  modifies Set.empty h0 h1 /\
  HH.parent w.region = parent /\
  fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  (authId i ==>
      (m_contains (ilog w.log) h1 /\
       m_sel h1 (ilog w.log) = createEmpty)) /\
  m_contains (ctr w.counter) h1 /\
  m_sel h1 (ctr w.counter) == 0
//16-04-30 how to share the whole ST ... instead of genPost?

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we might drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region)) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               r.log_region = w.region /\
               HH.parent r.region = parent /\
	       color r.region = color parent /\
               fresh_region r.region h0 h1 /\
               op_Equality #(log_ref w.region i) w.log r.log /\
	       m_contains (ctr r.counter) h1 /\
	       m_sel h1 (ctr r.counter) == 0))
// encryption (on concrete bytes), returns (cipher @| tag)
// Keeps seqn and nonce implicit; requires the counter not to overflow
// encryption of plaintexts; safe instances are idealized


// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))


val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))


val encrypt: #i:id -> e:writer i -> l:plainLen -> p:plain i l -> ST (cipher i l)
    (requires (fun h0 -> is_seqn (m_sel h0 (ctr e.counter) + 1)))
    (ensures  (fun h0 c h1 ->
                 modifies_one e.region h0 h1 /\
                 m_contains (ctr e.counter) h1 /\
                 m_sel h1 (ctr e.counter) == m_sel h0 (ctr e.counter) + 1 /\
	         (authId i ==> 
		   (let log = ilog e.log in
		    let ent = Entry l c p in
		    let n = Seq.length (m_sel h0 log) in
		    m_contains log h1 /\
		    witnessed (MonotoneSeq.at_least n ent log) /\
		    m_sel h1 log = snoc (m_sel h0 log) ent))))


let matches #i l (c:cipher i l) (Entry l' c' _) = l = l' && c = c'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: #i:id -> d:reader i -> l:plainLen -> c:cipher i l 
  -> ST (option (plain i (min l (max_TLSPlaintext_fragment_length + 1))))
  (requires (fun h0 -> is_seqn (m_sel h0 (ctr d.counter) + 1)))
  (ensures  (fun h0 res h1 ->
      let j = m_sel h0 (ctr d.counter) in
      (authId i ==>
	(let log = m_sel h0 (ilog d.log) in
	 if j < Seq.length log && matches l c (Seq.index log j)
	 then res = Some (Entry.p (Seq.index log j))
	 else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _  ->   modifies_one d.region h0 h1
              /\ modifies_rref d.region !{as_ref (as_rref (ctr d.counter))} h0 h1
	      /\ m_sel h1 (ctr d.counter) == j + 1)))
