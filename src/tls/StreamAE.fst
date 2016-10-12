module StreamAE

// Provides authenticated encryption for a stream of variable-length
// plaintexts; concretely, we use AES_GCM but any other AEAD algorithm
// would do.

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open StreamPlain


module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type rid = FStar.Monotonic.RRef.rid

type id = i:id { is_ID13 i }

let alg (i:id) : CoreCrypto.aead_cipher = AEAD._0 (aeAlg_of_id i)

let ltag i : nat = CoreCrypto.aeadTagSize (alg i)

let cipherLen i (l:plainLen) : nat = l + ltag i

type cipher i (l:plainLen) = lbytes (cipherLen i l)

// will require proving before decryption
let lenCipher i (c:bytes { ltag i <= length c }) : nat = length c - ltag i

type entry (i:id) =
  | Entry: l:plainLen -> c:cipher i l -> p:plain i l -> entry i

private unfold let min (a:int) (b:int) = if a < b then a else b
private unfold let max (a:int) (b:int) = if a < b then b else a

// The length of the per-record nonce (iv_length) is set to max(8 bytes, N_MIN)
// for the AEAD algorithm (see [RFC5116] Section 4)
let iv_length i = max 8 (CoreCrypto.aeadRealIVSize (alg i))

// key materials 
type key (i:id) = lbytes (CoreCrypto.aeadKeySize (alg i)) 
type iv  (i:id) = lbytes (iv_length i)

let ideal_log (r:rid) (i:id) = log_t r (entry i)

let log_ref (r:rid) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:rid) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) =
  l

irreducible let max_ctr: n:nat{n = 18446744073709551615} =
  assert_norm (pow2 64 - 1 = 18446744073709551615);
  pow2 64 - 1

type counter = c:nat{c <= max_ctr} 

let ideal_ctr (#l:rid) (r:rid) (i:id) (log:ideal_log l i) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log max_ctr
  // An increasing counter, at most min(length log, 2^64-1)
  
let concrete_ctr (r:rid) (i:id) : Tot Type0 = 
  m_rref r counter increases

let ctr_ref (#l:rid) (r:rid) (i:id) (log:log_ref l i) : Tot Type0 = 
  if authId i   
  then ideal_ctr r i (log <: ideal_log l i)
  else m_rref r counter increases

let ctr (#l:rid) (#r:rid) (#i:id) (#log:log_ref l i) (c:ctr_ref r i log)
  : Tot (m_rref r (if authId i 
		   then seqn_val #l #(entry i) r log max_ctr 
		   else counter) 
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
noeq type state (i:id) (rw:rw) = 
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> key: key i
         -> iv: iv i
         -> log: log_ref log_region i // ghost, subject to cryptographic assumption
         -> counter: ctr_ref region i log // types are sufficient to anti-alias log and counter
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
  stronger_fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  (authId i ==>
      (m_contains (ilog w.log) h1 /\
       m_sel h1 (ilog w.log) == createEmpty)) /\
  m_contains (ctr w.counter) h1 /\
  m_sel h1 (ctr w.counter) === 0
//16-04-30 how to share the whole ST ... instead of genPost?

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we might drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))

(*
 * AR: had to provide implicit arguments for ectr line, the cut, and the timeout
 *)
#set-options "--z3timeout 30"
let gen parent i =
  let kv = CoreCrypto.random (CoreCrypto.aeadKeySize (alg i)) in
  let iv = CoreCrypto.random (iv_length i) in
  let writer_r = new_region parent in
  let _ = cut (is_eternal_region writer_r) in
  if authId i then
    let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
    let ectr: ideal_ctr #writer_r writer_r i log = new_seqn #writer_r #(entry i) #max_ctr writer_r 0 log in
    State #i #Writer #writer_r #writer_r kv iv log ectr
  else
    let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
    State #i #Writer #writer_r #writer_r kv iv () ectr
#reset-options

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region)) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               r.log_region = w.region /\
               HH.parent r.region = parent /\
	       color r.region = color parent /\
               stronger_fresh_region r.region h0 h1 /\
               op_Equality #(log_ref w.region i) w.log r.log /\
	       m_contains (ctr r.counter) h1 /\
	       m_sel h1 (ctr r.counter) === 0))
// encryption (on concrete bytes), returns (cipher @| tag)
// Keeps seqn and nonce implicit; requires the counter not to overflow
// encryption of plaintexts; safe instances are idealized

let genReader parent #i w =
  let reader_r = new_region parent in
  if authId i then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #(w.region) w.key w.iv w.log dctr
  else let dctr : concrete_ctr reader_r i = m_alloc reader_r 0 in
    State #i #Reader #reader_r #(w.region) w.key w.iv () dctr

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

let coerce parent i kv iv =
  let writer_r = new_region parent in
  let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
  State #i #Writer #writer_r #writer_r kv iv () ectr 


val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))

let leak #i #role s = State.key s, State.iv s


// The per-record nonce for the AEAD construction is formed as follows:
//
// 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
//
// 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
//    depending on the role.
//
// The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
// we can reason about sequence-number collisions before applying it.
private abstract let aeIV i (seqn:counter) (staticIV:iv i) : lbytes (iv_length i) =
  lemma_repr_bytes_values seqn;
  let extended = bytes_of_int (iv_length i) seqn in
  xor (iv_length i) extended staticIV

// we are not relying on additional data
private abstract let noAD = empty_bytes


val encrypt: #i:id -> e:writer i -> l:plainLen -> p:plain i l -> ST (cipher i l)
    (requires (fun h0 -> m_sel h0 (ctr e.counter) < max_ctr))
    (ensures  (fun h0 c h1 ->
                 modifies_one e.region h0 h1 /\
                 m_contains (ctr e.counter) h1 /\
                 m_sel h1 (ctr e.counter) === m_sel h0 (ctr e.counter) + 1 /\
	         (authId i ==>
		   (let log = ilog e.log in
		    let ent = Entry l c p in
		    let n = Seq.length (m_sel h0 log) in
		    m_contains log h1 /\
		    witnessed (at_least n ent log) /\
		    m_sel h1 log == snoc (m_sel h0 log) ent))))

(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
let encrypt #i e l p =
  admit ();
  let ctr = ctr e.counter in 
  m_recall ctr;
  let text = if safeId i then createBytes l 0z else repr i l p in
  let n = m_read ctr in
  let iv = aeIV i n e.iv in
  let c = CoreCrypto.aead_encrypt (alg i) e.key iv noAD text in
  if authId i then
    begin
    let ilog = ilog e.log in
    m_recall ilog;
    let ictr: ideal_ctr e.region i ilog = e.counter in
    testify_seqn ictr;
    write_at_end ilog (Entry l c p); //need to extend the log first, before incrementing the counter for monotonicity; do this only if ideal
    m_recall ictr;
    increment_seqn ictr;
    m_recall ictr
    end
  else
    m_write ctr (n + 1);
  c

(* val matches: #i:id -> l:plainLen -> cipher i l -> entry i -> Tot bool *)
let matches (#i:id) (l:plainLen) (c:cipher i l) (e:entry i) : Tot bool = 
  let Entry l' c' _ = e in
  l = l' && c = c'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: #i:id -> d:reader i -> l:plainLen -> c:cipher i l
  -> ST (option (plain i (min l (max_TLSPlaintext_fragment_length + 1))))
  (requires (fun h0 -> m_sel h0 (ctr d.counter) < max_ctr))
  (ensures  (fun h0 res h1 ->
      let j = m_sel h0 (ctr d.counter) in
      (authId i ==>
	(let log = m_sel h0 (ilog d.log) in
	 if j < Seq.length log && matches l c (Seq.index log j)
	 then res = Some (Entry.p (Seq.index log j))
	 else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _  ->  
                let ctr_counter_as_hsref = as_hsref (ctr d.counter) in
                modifies_one d.region h0 h1
              /\ modifies_rref d.region !{as_ref ctr_counter_as_hsref} h0.h h1.h
	      /\ m_sel h1 (ctr d.counter) === j + 1)))

#set-options "--z3timeout 100 --initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 1"
// decryption, idealized as a lookup of (c,ad) in the log for safe instances
let decrypt #i d l c =
  admit ();
  let ctr = ctr d.counter in 
  m_recall ctr;
  let j = m_read ctr in
  if authId i 
  then 
    let ilog = ilog d.log in
    let log  = m_read ilog in
    let ictr: ideal_ctr d.region i ilog = d.counter in
    let _ = testify_seqn ictr in //now we know that j <= Seq.length log
    if j < Seq.length log && matches l c (Seq.index log j) then
      begin
      increment_seqn ictr;
      m_recall ctr;
      Some (Entry.p (Seq.index log j))
      end
    else None
  else //concrete
     let iv = aeIV i j d.iv in
     match CoreCrypto.aead_decrypt (alg i) d.key iv noAD c with
     | None -> None
     | Some pr ->
       begin
       assert (Platform.Bytes.length pr = l);
       match mk_plain i l pr with
       | Some p -> (m_write ctr (j + 1); Some p)
       | None   -> None
       end


(* TODO

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)
- Injective allocation table from i to refs

*)
