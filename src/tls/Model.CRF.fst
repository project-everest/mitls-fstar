(** computational assumption: collision resistance *)
module Model.CRF

/// This module should not be extracted 

open EverCrypt.Hash // only for the specs (renamings)

//2018.04.24 SZ: to be moved elsewhere, set to false for real extraction
//inline_for_extraction
// let crf _ = false
assume val crf: alg -> Tot bool

let h = Spec.Hash.hash 

(* Depending on a single, global idealization function, we keep a global
    inverse table for all (finalized) hash computations, and we use it to
    detect concrete collisions. Technically, this is modelled as
    non-termination of a stateful, partially-correct finalize filter.
    This may depend on some prior flag to keep the hashed input in the
    incremental hash implementation. (This is always the case for now.)  *)

open Mem 
module MDM = FStar.Monotonic.DependentMap 

// now bounded irrespective of a, as in EverCrypt.Incremental (TBD)
let bytes = Seq.seq UInt8.t

//$ avoid using it because ghost lack structural subtyping.
let hashable (s:bytes) = Seq.length s < pow2 61
// type hashable (a:alg) = v:Seq.seq UInt8.t {Seq.length v < maxLength a}

// the precise types guarantee that the table stays empty when crf _ = false
private type range = | Computed: a: alg {crf a} -> t: tag a -> range
private type domain (r:range) =
  b:Seq.seq UInt8.t {
    let Computed a t = r in 
    Seq.length b < maxLength a /\ 
    h a b = t}

private let inv (f:MDM.partial_dependent_map range domain) = True // a bit overkill?
private let table : MDM.t tls_tables_region range domain inv = MDM.alloc()

// witnessing that we hashed this particular content (for collision detection)
// to be replaced by a witness of inclusion in a global table of all hash computations.
// (not sure how to manage that table)

//val hashed: a:alg -> b:bytes -> Type

abstract type hashed (a:alg) (b:bytes) =
  model /\ crf a ==> (
    hashable b /\
    Seq.length b < maxLength a /\
    (
    let t = h a b in
    witnessed (MDM.contains table (Computed a t) (b <: domain (Computed a t)))))

// required to go through abstraction when switching 
let concrete_hashed a b: Lemma (~model ==> hashed a b) = ()

val injective (a:alg) (b0 b1: Ghost.erased bytes): 
  Stack unit  
  (requires fun h0 -> 
    let b0 = Ghost.reveal b0 in 
    let b1 = Ghost.reveal b1 in
    hashed a b0 /\ hashed a b1)
  (ensures fun h0 _ h1 -> 
    let b0 = Ghost.reveal b0 in 
    let b1 = Ghost.reveal b1 in
    h0 == h1 /\ (model /\ crf a /\ h a b0 == h a b1 ==> b0 == b1))
let injective a b0 b1 =
  if model && crf a then (
    recall table;
    let f = !table in
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b0))) (Ghost.reveal b0));
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b1))) (Ghost.reveal b1))
  )

/// We use [stop] to model the exclusion of "bad" events, in this case
/// a hash collision.  We should review this "flagless" style for
/// crypto modelling.

noextract 
private val stop: s:string -> Stack 'a
  (requires fun h -> True)
  (ensures fun h0 r h1 -> False)
let rec stop (s:string) = stop s

val hash: a:alg -> v:bytes -> Stack (tag a)
  (requires fun h0 -> hashable v)
  (ensures fun h0 t h1 ->
    LowStar.Buffer.(modifies loc_none h0 h1) /\
    Seq.length v < maxLength a /\
    t == h a v /\ 
    hashed a v
  )

open LowStar.Buffer

module ST = FStar.HyperStack.ST 

let hash a v =
  let h0 = ST.get() in 
  assert_norm (pow2 61 < pow2 125);
  assert(Seq.length v < maxLength a);
  let t = Spec.Hash.hash a v in 
  if crf a then (
    let x = Computed a t in
    match MDM.lookup table x with
      | None -> MDM.extend table x v
      | Some v' -> if v <> v' then stop "hash collision detected");
  let h1 = ST.get() in 
  //19-05-25 TODO stuck with an old library
  assume(h0 == h1); //modifies loc_none h0 h1);
  t

#set-options "--z3rlimit 100"
// sanity check

open FStar.Seq
private val test (a:alg {crf a}) (b0 b1: (b:bytes{hashable b})): St unit
let test a b0 b1 =
  let t0 = hash a b0 in 
  let t1 = hash a b1 in
  injective a (Ghost.hide b0) (Ghost.hide b1);
  if model && t0 = t1 then assert(b0 == b1)
  
