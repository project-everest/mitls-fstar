module Standalone
open FStar.Bytes
open FStar.HyperStack.ST
open FStar.Monotonic.RRef
module MM = MonotoneMapNonDep
module HH = FStar.HyperHeap
module MR = FStar.Monotonic.RRef
assume val some_region : HH.rid
type random = lbytes 32
let injective (n:MM.map' random rid) = True
let nonce_rid_table : MM.t some_region random MR.ex_rid injective =
    MM.alloc ()
