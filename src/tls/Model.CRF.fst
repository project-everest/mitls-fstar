(** computational assumption: collision resistance *)
module Model.CRF

open Declassify
open Mem
open Spec.Hash.Definitions
open EverCrypt.Hash
open EverCrypt.Hash.Incremental // only for the specs (renamings)

module MDM = FStar.Monotonic.DependentMap

let crf: alg -> Tot bool = admit ()

type hashed (a:alg) (b:bytes) =
  model /\ crf a ==> (
    hashable b /\
    Seq.length b <= max_input_length a /\
    (
    let t = h a b in
    witnessed (MDM.contains table (Computed a t) (b <: domain (Computed a t)))))

let hashed_max_input_length a b = ()

let concrete_hashed a b = ()

let injective a b0 b1 =
  if model && crf a then (
    recall table;
    let f = !table in
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b0))) (Ghost.reveal b0));
    testify(MDM.contains table (Computed a (h a (Ghost.reveal b1))) (Ghost.reveal b1))
  )

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

let test a b0 b1 =
  let t0 = hash a b0 in
  let t1 = hash a b1 in
  injective a (Ghost.hide b0) (Ghost.hide b1);
  if model && t0 = t1 then assert(b0 == b1)
