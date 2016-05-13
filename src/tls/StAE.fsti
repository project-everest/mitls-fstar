module StAE

// Authenticated encryptions of streams of TLS fragments (from Content)
// multiplexing StatefulLHAE and StreamAE with (some) length hiding
// (for now, under-specifying ciphertexts lengths and values)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open Content
open MonotoneSeq
open FStar.Monotonic.RRef
module HH = HyperHeap

// plaintexts are defined in Content.fragment i

// ciphertexts, ignoring details for now (would be needed for functional correctness)
// the first two should be concretely defined (for now in TLSInfo)

assume val validCipherLen: i:id -> l:nat -> Type0 // sufficient to ensure the cipher can be processed without length errors

assume val cipherLen: i:id -> fragment i -> Tot (l:nat {validCipherLen i l})

type encipher (#i:id) (f:fragment i) = lbytes (cipherLen i f)
type decipher (i:id) = b:bytes { validCipherLen i (length b) }

// concrete key materials, for leaking & coercing.
// (each implementation splits it into encryption keys, IVs, MAC keys, etc)

let aeKeySize (i:id) = 
  if pv_of_id i = TLS_1p3 
  then CoreCrypto.aeadKeySize (StreamAE.alg i) + CoreCrypto.aeadRealIVSize (StreamAE.alg i)
  else 0 //FIXME!

type keybytes (i:id) = lbytes (aeKeySize i)

// abstract instances

val state: i:id -> rw:rw -> Type0



type reader i = state i Reader
type writer i = state i Writer

val region:     #i:id -> #rw:rw -> state i rw -> Tot rgn
val log_region: #i:id -> #rw:rw -> state i rw -> Tot rgn
// how to specify those two? Their properties are available at creation-time. 


// our view to AE's ideal log (when idealized, ignoring ciphers) and counter
// TODO: write down their joint monotonic specification: both are monotonic, and seqn = length log when ideal

type ideal_log (i:id) = seq (fragment i)  // TODO: consider adding constraint on terminator fragments

val logT: #i:id { authId i } -> #rw:rw -> state i rw -> HH.t -> GTot (ideal_log i)

val seqnT: #i:id -> #rw:rw -> state i rw -> HH.t -> Tot seqn_t 

let incrementable (#i:id) (#rw:rw) (s:state i rw) (h:HH.t) = is_seqn (seqnT s h + 1)

// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

// We generate first the writer, then the reader (possibly several of them)

let genPost (#i:id) parent h0 (w:writer i) h1 = 
  let r = region w in 
  modifies Set.empty h0 h1 /\
  HH.parent r = parent /\
  fresh_region r h0 h1 /\
  color r = color parent /\
  seqnT w h1 = 0 /\
  (authId i ==> logT #i #Writer w h1 = createEmpty) // we need to re-apply #i knowning authId

// Generate a fresh instance with index i in a fresh sub-region 

val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> keybytes i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (keybytes i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent (region w))) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               log_region r = region w /\
               HH.parent (region r) = parent /\
	       color (region r) = color parent /\
               fresh_region (region r ) h0 h1 /\
               //?? op_Equality #(log_ref w.region i) w.log r.log /\
               seqnT r h1 = 0))
// encryption, recorded in the log; safe instances are idealized
val encrypt: #i:id -> e:writer i -> f:fragment i -> ST (encipher f)
  (requires (fun h0 -> incrementable e h0))
  (ensures  (fun h0 c h1 ->
               modifies_one (region e) h0 h1 /\
               seqnT e h1 = seqnT e h0 + 1 /\
               authId i ==> logT #i #Writer e h1 = snoc (logT #i #Writer e h0) f))
//TODO restore monotonic post; see StreamAE.fsti

// decryption, idealized as a lookup for safe instances
val decrypt: #i:id -> d:reader i -> c:decipher i -> ST (option (f:fragment i { length c = cipherLen i f}))
  (requires (fun h0 -> incrementable d h0))
  (ensures  (fun h0 res h1 ->
	      match res with
 	     | None   -> modifies Set.empty h0 h1
	     | Some f -> let j = seqnT d h0 in 
                        modifies_one (region d) h0 h1 /\ 
                        seqnT d h1 = j + 1 /\
                        (authId i ==>
                           (let written = logT #i #Reader d h1 in 
                           j < Seq.length written /\
                           f = Seq.index written j)))) 
