module Standalone
module HS = FStar.HyperStack //Added automatically
module HST = FStar.HyperStack.ST //Added automatically
open FStar.Bytes
open FStar.HyperStack.ST

module MM = FStar.Monotonic.DependentMap


assume val some_region : HS.rid
type random = lbytes 32
let injective (n:MM.partial_dependent_map random (fun _ -> rid)) = True
let nonce_rid_table : MM.t some_region random (fun _ -> HST.ex_rid) injective =
    MM.alloc ()
