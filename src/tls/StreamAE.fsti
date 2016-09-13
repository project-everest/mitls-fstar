module StreamAE

// Authenticated encryption for a stream of variable-length plaintexts.
// Supports all TLS 1.3 record protection mechanisms (but aims at generality)
// No support for additional authenticated data.

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open StreamPlain

module HH = FStar.HyperHeap

// The index is treated abstractly, with
// - a restriction to TLS 1.3
// - `alg` for controlling algorithmic agility (consider making it private)

type id = i:id { is_ID13 i }
let alg (i:id) : CoreCrypto.aead_cipher = AEAD._0 (aeAlg_of_id i)

private inline let min (a:int) (b:int) = if a < b then a else b
private inline let max (a:int) (b:int) = if a < b then b else a


(*** Key materials ***)

// The length of the per-record nonce (iv_length) is set to max(8 bytes, N_MIN)
// for the AEAD algorithm (see [RFC5116] Section 4)
let iv_length i = max 8 (CoreCrypto.aeadRealIVSize (alg i))

// concrete representations
type key (i:id) = lbytes (CoreCrypto.aeadKeySize (alg i)) 
type iv  (i:id) = lbytes (iv_length i)


(*** Plaintexts and ciphertexts ***)

// Plaintexts are defined in StreamPlain, represented as bounded bytestrings.
// Ciphertexts are longer by exactly (tagLen i) bytes.

let tagLen i : nat = CoreCrypto.aeadTagSize (alg i)
let cipherLen i (l:plainLen) : nat = l + tagLen i
type cipher i (l:plainLen) = lbytes (cipherLen i l)

// Presumed plaintext length when decrypting c
let lenCipher i (c:bytes { tagLen i <= length c }) : nat = length c - tagLen i

//16-09-10 causing a lexing error, why? 
//(* ** Ideal State ***) 

// ideal StreamAE maintains a table from sequence numbers to entries
// (we'll need a separate ideal flag to support dynamic compromise)


type entry (i:id) =
  | Entry: l:plainLen -> c:cipher i l -> p:plain i l -> entry i


let ideal_log (r:rid) (i:id) = log_t r (entry i)

let log_ref (r:rid) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

// applied to force the condition within log_ref
let ilog (#r:rid) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) = l

// 'ctr' here refers to the encryption sequence number---not the internal block counter.

irreducible let max_ctr: nat = pow2 64 - 1
assume val max_ctr_value: unit -> Lemma (max_ctr = 18446744073709551615)
// how to avoid this?

type seqnum = c:nat{c <= max_ctr} 

// a ref to an increasing sequence number,
// when authId i, the sequence number is at most min(length log, max_ctr)

let concrete_ctr (r:rid) (i:id) : Tot Type0 = m_rref r seqnum increases

let ideal_ctr (#rl:rid) (r:rid) (i:id) (log:ideal_log rl i) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log max_ctr
    
let ctr_ref (#rl:rid) (r:rid) (i:id) (log:log_ref rl i) : Tot Type0 = 
  if authId i   
  then ideal_ctr r i (log <: ideal_log rl i)
  else m_rref r seqnum increases

let ctr (#rl:rid) (#r:rid) (#i:id) (#log:log_ref rl i) (c:ctr_ref r i log)
  : Tot (m_rref r (if authId i 
		   then seqn_val #rl #(entry i) #(fun (s:seq (entry i)) -> True) r (ilog log) max_ctr 
		   else seqnum) 
		increases) =
  c

(*
// error message: on log:
exp (FStar.Monotonic.Seq.i_seq rl (StreamAE.entry i) (fun s -> Prims.l_True))
got (StreamAE.log_ref l i)
  = if authId i then ideal_log rl i else unit
  = log_t rl (entry i) 
  = i_seq rl a (fun (s:seq a) -> True) (fun s -> True)
*)

// local state for encryption and decryption.
// kept concrete for log and seqn, but key and iv should be private.
noeq type state (i:id) (rw:rw) = 
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> key: key i
         -> iv: iv i
         -> log: log_ref log_region i     // ghost, subject to cryptographic assumption
         -> seqn: ctr_ref region i log // types are sufficient to anti-alias log and seqn
         -> state i rw

// Some invariants:
// - the writer seqn is the length of the log; the reader seqn is lower or equal
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
       m_sel h1 (ilog w.log) == createEmpty)) /\
  m_contains (ctr w.seqn) h1 /\
  m_sel h1 (ctr w.seqn) === 0
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
	       m_contains (ctr r.seqn) h1 /\
	       m_sel h1 (ctr r.seqn) === 0))
// encryption (on concrete bytes), returns (cipher @| tag)
// Keeps seqn and nonce implicit; requires the seqn not to overflow
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
    (requires (fun h0 -> m_sel h0 (ctr e.seqn) < max_ctr))
    (ensures  (fun h0 c h1 ->
                 modifies_one e.region h0 h1 /\
                 m_contains (ctr e.seqn) h1 /\
                 m_sel h1 (ctr e.seqn) === m_sel h0 (ctr e.seqn) + 1 /\
	         (authId i ==>
		   (let log = ilog e.log in
		    let ent = Entry l c p in
		    let n = Seq.length (m_sel h0 log) in
		    m_contains log h1 /\
		    witnessed (at_least n ent log) /\
		    m_sel h1 log == snoc (m_sel h0 log) ent))))

(* val matches: #i:id -> l:plainLen -> cipher i l -> entry i -> Tot bool *)
let matches (#i:id) (l:plainLen) (c:cipher i l) (e:entry i) : Tot bool = 
  let Entry l' c' _ = e in
  l = l' && c = c'

// decryption, idealized as a lookup at index d.seq# in the log for safe instances
val decrypt: #i:id -> d:reader i -> l:plainLen -> c:cipher i l
  -> ST (option (plain i (min l (max_TLSPlaintext_fragment_length + 1))))
  (requires (fun h0 -> m_sel h0 (ctr d.seqn) < max_ctr))
  (ensures  (fun h0 res h1 ->
      let j = m_sel h0 (ctr d.seqn) in
      (authId i ==>
	(let log = m_sel h0 (ilog d.log) in
	 if j < Seq.length log && matches l c (Seq.index log j)
	 then res = Some (Entry.p (Seq.index log j))
	 else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _  ->   modifies_one d.region h0 h1
              /\ modifies_rref d.region !{as_ref (as_rref (ctr d.seqn))} h0 h1
	      /\ m_sel h1 (ctr d.seqn) === j + 1)))
