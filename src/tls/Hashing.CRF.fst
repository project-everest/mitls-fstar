(** computational assumption: collision resistance *)
module Hashing.CRF

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Bytes
open Hashing.Spec

assume val crf: alg -> Tot bool  // to be moved elsewhere, set to false for real extraction

(* Depending on a single, global idealization function, we keep a global
    inverse table for all (finalized) hash computations, and we use it to
    detect concrete collisions. Technically, this is modelled as
    non-termination of a stateful, partially-correct finalize filter.
    This may depend on some prior flag to keep the hashed input in the
    incremental hash implementation. (This is always the case for now.)  *)

module MR = FStar.Monotonic.RRef
module MM = FStar.Monotonic.DependentMap

// the precise types guarantee that the table stays empty when crf _ = false
private type range = | Computed: a: alg {crf a} -> tag a -> range
private type domain (r:range) =
  b:bytes {(let Computed a t = r in Bytes.equal (hash a b) t)}

private let inv (f:MM.partial_dependent_map range domain) = True // a bit overkill?
private let table : MM.t TLSConstants.tls_tables_region range domain inv = MM.alloc()

// witnessing that we hashed this particular content (for collision detection)
// to be replaced by a witness of inclusion in a global table of all hash computations.
// (not sure how to manage that table)

//val hashed: a:alg -> b:bytes -> Type
abstract type hashed (a:alg) (b:bytes) =
  crf a ==> (
    let h = hash a b in
    let b: domain (Computed a h) = b in
    MR.witnessed (MM.contains table (Computed a h) b))

val crf_injective (a:alg) (b0:bytes) (b1:bytes): ST unit  // should be STTot
  (requires (fun h0 -> hashed a b0 /\ hashed a b1 ))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ (crf a /\ hash a b0 =  hash a b1 ==> Bytes.equal b0 b1)))
let crf_injective a b0 b1 =
  if crf a then (
    MR.m_recall table;
    let f = MR.m_read table in
    let h0 = hash a b0 in
    let h1 = hash a b1 in
    MR.testify(MM.contains table (Computed a h0) b0);
    MR.testify(MM.contains table (Computed a h1) b1);
  ())

private val stop: s:string -> ST 'a
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> False))
let rec stop (s:string) = stop s

include Hashing

val finalize: #a:alg -> v:accv a -> ST (tag a)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 ->
    let b = content v in
//17-04-12 broken by our switch to haclstar? older comment: precise enough? unclear where it goes in hacl*
// modifies (Set.as_set [TLSConstants.tls_tables_region]) h0 h1 /\
    t = hash a b /\ hashed a b
  ))

let finalize #a v =
  let h = Hashing.finalize v in
  if crf a then (
    let x = Computed a h in
    let b = Hashing.content v in
    match MM.lookup table x with
      | None -> MM.extend table x b
      | Some b' -> if b <> b' then stop "hash collision detected");
  h

#set-options "--z3rlimit 100"
// sanity check
private val test: a:alg -> b0:bytes -> b1:bytes -> St unit
let test a b0 b1 =
  // we need to record *both* computations
  let h = finalize (extend (start a) b0) in
  let h' = finalize (extend (extend (start a) b1) b1) in

  // ...and, annoyingly, to normalize concatenations
  assert(Bytes.equal (empty_bytes @| b0) b0);
  assert(Bytes.equal ((empty_bytes @| b1) @| b1) (b1 @| b1));

  if h <> h' then assert(b0 <> b1 @| b1);

  // ...and to apply a stateful lemma
  crf_injective a b0 (b1 @| b1);
  if h = h' then assert(crf a ==> Bytes.equal b0 (b1 @| b1))
