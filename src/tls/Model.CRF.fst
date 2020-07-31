(** computational assumption: collision resistance *)
module Model.CRF

/// This module should not be extracted to C.

open Declassify
open Mem
open Spec.Hash.Definitions
open EverCrypt.Hash
open EverCrypt.Hash.Incremental // only for the specs (renamings)

module MDM = FStar.Monotonic.DependentMap

#set-options "--max_fuel 0 --max_ifuel 0"

/// Verification is parametric in this specification function. Its
/// concrete definition would state our collision-resistance
/// assumption for a subset of the algorithms supported by EverCrypt.

let crf = admit ()

/// Depending on a single, global idealization function, we keep a
/// global inverse table for all (finalized) hash computations, and we
/// use it to detect concrete collisions. Technically, this is
/// modelled as non-termination of a stateful, partially-correct
/// finalize filter. This may depend on some prior flag to keep the
/// hashed input in the incremental hash implementation. (This is
/// always the case for now.)

// the precise types guarantee that the table stays empty when crf _ = false
private type range = | Computed: a: alg {crf a} -> t: bytes_hash a -> range

private type domain (r:range) =
  b:Seq.seq UInt8.t {
    let Computed a t = r in
    Seq.length b <= max_input_length a /\
    h a b = t}

private let table : MDM.t tls_tables_region range domain (fun _ -> True) = MDM.alloc()

// witnessing that we hashed this particular content (for collision detection)
// to be replaced by a witness of inclusion in a global table of all hash computations.
// (not sure how to manage that table)

//val hashed: a:alg -> b:bytes -> Type

type hashed (a:alg) (b:bytes) =
  model /\ crf a ==> (
    hashable b /\
    Seq.length b <= max_input_length a /\
    (
    let t = h a b in
    witnessed (MDM.contains table (Computed a t) (b <: domain (Computed a t)))))

let hashed_max_input_length a b = ()

// required to go through abstraction when switching
let concrete_hashed a b: Lemma (~model ==> hashed a b) = ()

let injective a b0 b1 =
  if model && crf a then (
    recall table;
    let f = !table in
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b0))) (Ghost.reveal b0));
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b1))) (Ghost.reveal b1))
  )

/// We use [stop] to model the exclusion of "bad" events, in this case
/// a hash collision. We should review this "flagless" style for
/// crypto modelling.

private val stop: s:string -> Stack 'a
  (requires fun h -> True)
  (ensures fun h0 r h1 -> False)
let rec stop (s:string) = stop s

open LowStar.Buffer

module ST = FStar.HyperStack.ST

let hash a v =
  let h0 = ST.get() in
  assert_norm (pow2 61 < pow2 125);
  assert(Seq.length v <= max_input_length a);
  let t = Spec.Agile.Hash.hash a v in
  if crf a then (
    let x = Computed a t in
    match MDM.lookup table x with
      | None -> MDM.extend table x v
      | Some v' -> if v <> v' then stop "hash collision detected");
  let h1 = ST.get() in
  LowStar.Buffer.modifies_loc_regions_intro (Set.singleton tls_tables_region) h0 h1;
  t

// sanity check

#set-options "--z3rlimit 100"
open FStar.Seq

private val test (a:alg {crf a}) (b0 b1: (b:bytes{hashable b})): St unit
let test a b0 b1 =
  let t0 = hash a b0 in
  let t1 = hash a b1 in
  injective a (Ghost.hide b0) (Ghost.hide b1);
  if model && t0 = t1 then assert(b0 == b1)
