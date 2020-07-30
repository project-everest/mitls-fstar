(** computational assumption: collision resistance *)
module Hashing.CRF

open Mem
include Hashing
open FStar.Bytes

let hashed (a:alg) (b:hashable a) =
  crf a ==> (
    let t = h a b in
    let b: domain (Computed a t) = b in
    witnessed (MDM.contains table (Computed a t) b))

let crf_injective a b0 b1 =
  if crf a then (
    recall table;
    let f = !table in
    testify(MDM.contains table (Computed a (h a b0)) b0);
    testify(MDM.contains table (Computed a (h a b1)) b1)
  )

#set-options "--admit_smt_queries true" //18-02-26 was verified with MonotonicMap
let finalize #a v =
  let t = Hashing.finalize v in
  if crf a then (
    let x = Computed a t in
    let b = Hashing.content v in
    match MDM.lookup table x with
      | None -> MDM.extend table x b
      | Some b' -> if b <> b' then stop "hash collision detected");
  t
#reset-options 

#set-options "--z3rlimit 100"
let test a b0 b1 =
  // we need to record *both* computations
  let h = finalize (extend (start a) b0) in
  let h' = finalize (extend (extend (start a) b1) b1) in

  // ...and, annoyingly, to normalize concatenations
  //18-02-25 TODO those two were at least assertable with Platform.Bytes
  assume(empty_bytes @| b0 = b0);
  assume((empty_bytes @| b1) @| b1 = b1 @| b1);

  if h <> h' then assert(b0 <> b1 @| b1);

  // ...and to apply a stateful lemma
  crf_injective a b0 (b1 @| b1);
  if h = h' then assert(crf a ==> b0 = b1 @| b1)
