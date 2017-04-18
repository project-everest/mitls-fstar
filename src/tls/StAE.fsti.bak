(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module StAE

// Authenticated encryptions of streams of TLS fragments (from Content)
// multiplexing StatefulLHAE and StreamAE with (some) length hiding
// (for now, under-specifying ciphertexts lengths and values)

open Platform.Error
open Platform.Bytes
open TLSError
open TLSConstants
open TLSInfo

(* distinguishing the two multiplexing choices of StAE based on the ids *)

let is_stream (i: TLSInfo.id) = ID13? i

let is_stlhae (i:TLSInfo.id) = ID12? i && AEAD? (aeAlg_of_id i) &&
  (AEAD?._0 (aeAlg_of_id i) = CoreCrypto.AES_128_GCM ||
   AEAD?._0 (aeAlg_of_id i) = CoreCrypto.AES_256_GCM)

// was:
// let is_stream_ae i = pv_of_id i = TLS_1p3
// let is_stateful_lhae i = pv_of_id i <> TLS_1p3 /\ is_AEAD i.aeAlg /\ ~ (authId i)

type stae_id = i:id {is_stream i \/ is_stlhae i}

(* various utilities related to lengths of ciphers and fragments *)

// plaintexts are defined in Content.fragment i
//16-06-08 see also StreamPlain and StatefulPlain.

let frag_plain_len (#i:id{is_stream i}) (f:Content.fragment i): StreamPlain.plainLen = snd (Content.rg i f) + 1


(*
// ciphertexts, ignoring details for now (would be needed for functional correctness)
// the first two should be concretely defined (for now in TLSInfo)

assume val validCipherLen: i:id -> l:nat -> Type0 // sufficient to ensure the cipher can be processed without length errors
assume val cipherLen: i:id -> fragment i -> Tot (l:nat {validCipherLen i l})

type encipher (#i:id) (f:fragment i) = lbytes (cipherLen i f)
type decipher (i:id) = b:bytes { validCipherLen i (length b) }
*)

// concrete key materials, for leaking & coercing.
// (each implementation splits it into encryption keys, IVs, MAC keys, etc)
val aeKeySize: i:stae_id -> Tot nat // abstraction required to hide AEADProvider? 
type keyBytes (i:stae_id) = lbytes (aeKeySize i)

(* older:
let aeKeySize (i:id) = 
  if pv_of_id i = TLS_1p3 
  then CoreCrypto.aeadKeySize (StreamAE.alg i) + CoreCrypto.aeadRealIVSize (StreamAE.alg i)
  else 0 //FIXME!
*)

(* `state i rw`, a sum to cover StreamAE (1.3) and StatefulLHAE (1.2) *)

val state: i:id -> rw:rw -> Type0
val region: #i:id -> #rw:rw -> state i rw -> Tot rgn
val log_region: #i:id -> #rw:rw -> state i rw -> Tot rgn

type reader (i:id) = state i Reader
type writer (i:id) = state i Writer

// how to specify those two? Their properties are available at creation-time. 


(* logs of fragments, defined as projections on the underlying entry logs *)

// our view to AE's ideal log (when idealized, ignoring ciphers) and counter
// TODO: write down their joint monotonic specification: both are monotonic, 
// and seqn = length log when ideal

// TODO: consider adding constraint on terminator fragments
type frags (i:id{~ (PlaintextID? i)}) = Seq.seq (Content.fragment i)
 
// val ideal_log (r:rgn) (i:id): Type0 // vs frags i?

val fragments: #i:id -> #rw:rw -> s:state i rw{authId i} ->  h:HyperStack.mem -> GTot (frags i)
val fragments_prefix: #i:id -> #rw:rw -> s:state i rw{authId i} ->  fs:frags i -> HyperStack.mem -> GTot Type0
// TODO get something out of it!

(* projecting sequence numbers *) 

val seqnT: #i:id -> #rw:rw -> state i rw -> HyperStack.mem -> GTot seqn_t  // nat? 

// incrementable if it doesn't overflow
let incrementable (#i:id) (#rw:rw) (s:state i rw) h = is_seqn (seqnT s h + 1)
//or: = seqnT s h < 18446744073709551615

let trigger_frame (h:HyperStack.mem) = True
let frame_f (#a:Type) (f:HyperStack.mem -> GTot a) (h0:HyperStack.mem) (s:Set.set HyperHeap.rid) =
  forall h1.{:pattern trigger_frame h1}
        trigger_frame h1 /\ 
        (HyperHeap.equal_on s FStar.HyperStack.(h0.h) FStar.HyperStack.(h1.h) ==> f h0 == f h1)
//17-04-13 horrible scopes

// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic


(* key operations *) 

// We generate first the writer, then the reader (possibly several of them)

// Generate a fresh instance with index i in a fresh sub-region 

let genPost (#i:id) parent h0 (w:writer i) h1 =
  let r = region #i #Writer w in
  HyperStack.modifies Set.empty h0 h1 /\
  HyperHeap.extends r parent /\
  stronger_fresh_region r h0 h1 /\
  HyperHeap.color r = HyperHeap.color parent /\
  seqnT #i #Writer w h1 = 0 /\
  (authId i ==> fragments #i #Writer w h1 == Seq.createEmpty) // we need to re-apply #i knowning authId
val gen: parent:rgn -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))

val genReader: parent:rgn -> #i:id -> w:writer i -> ST (reader i)
  (requires fun h0 -> 
    HyperHeap.disjoint parent (region #i #Writer w)) //16-04-25  we may need w.region's parent instead
  (ensures  fun h0 (r:reader i) h1 ->
    HyperStack.modifies Set.empty h0 h1 /\
    log_region r = region #i #Writer w /\
    HyperHeap.extends (region r) parent /\
    HyperHeap.color (region r) = HyperHeap.color parent /\
    stronger_fresh_region (region r) h0 h1 /\
    //op_Equality #(log_ref w.region i) w.log r.log /\
    seqnT r h1 = 0)

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rgn -> i:stae_id{~(authId i)} -> keyBytes i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

// first arguments was #i:id; an old comments says:
// with 2 units of i_fuel, we can invert s and prove that i must be an stae_id
val leak: #i:stae_id{~(authId i)} -> #role:rw -> s:state i role -> ST (keyBytes i) 
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> HyperStack.modifies Set.empty h0 h1 ))


(* encryption, recorded in the log; safe instances are idealized *) 
#set-options "--z3rlimit 200" 
val encrypt: #i:id -> e:writer i -> f:Content.fragment i -> ST (Content.encrypted f)
  (requires fun h0 -> incrementable e h0) // expansion required for subtyping
  (ensures  fun h0 c h1 ->
    HyperStack.modifies_one (region e) h0 h1 /\ 
    seqnT e h1 = seqnT e h0 + 1 /\ 
    frame_f (seqnT e) h1 (Set.singleton (log_region e)) /\ 
    ( authId i ==>
        fragments e h1 == Seq.snoc (fragments e h0) f /\ 
        frame_f (fragments e) h1 (Set.singleton (log_region e)) /\
        //17-04-13  too concrete? /\
        Monotonic.RRef.witnessed (fragments_prefix e (fragments e h1))
        ))

(* decryption, idealized as a lookup for safe instances *)

val fragment_at_j: #i:id -> #rw:rw -> 
  s:state i rw{authId i} -> n:nat -> f:Content.fragment i -> HyperStack.mem ->  Tot Type0

// do we need length c = cipherLen i f? 
val decrypt: #i:id -> d:reader i -> c:Content.decrypted i -> 
  ST (option (f:Content.fragment i))
    (requires fun h0 -> incrementable d h0)
    (ensures  fun h0 res h1 ->
      match res with
      | None -> HyperStack.modifies Set.empty h0 h1
      | Some f ->
          let ct,rg = Content.ct_rg i f in
          let j = seqnT d h0 in
            seqnT d h1 = j + 1 /\
            ( if is_stream i 
              then frag_plain_len #i f <= Content.cipherLen i f
              else
                ct = fst c /\
                Range.wider (Range.cipherRangeClass i (length (snd c))) rg) /\
                HyperStack.modifies_one (region d) h0 h1 /\
                ( authId i ==>
                    ( let written = fragments d h0 in
                      j < Seq.length written /\
                      f = Seq.index written j /\
                      frame_f (fragments d) h1 (Set.singleton (log_region d)) /\
                      //17-04-13 too concrete? /\
                      Monotonic.RRef.witnessed (fragment_at_j d j f)
                      )))

