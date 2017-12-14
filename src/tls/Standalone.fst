module Standalone
open FStar.Bytes
open FStar.HyperStack.ST
open FStar.Monotonic.RRef
module MM = FStar.Monotonic.DependentMap
module HH = FStar.HyperHeap
module MR = FStar.Monotonic.RRef
assume val some_region : HH.rid
type random = lbytes 32
let injective (n:MM.partial_dependent_map random (fun _ -> rid)) = True
let nonce_rid_table : MM.t some_region random (fun _ -> MR.ex_rid) injective =
    MM.alloc ()
