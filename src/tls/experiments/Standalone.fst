module Standalone

open FStar.Bytes

module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

assume val some_region : HS.rid
type random = lbytes 32
let injective (n:MDM.partial_dependent_map random (fun _ -> HS.rid)) = True
let nonce_rid_table : MDM.t some_region random (fun _ -> HST.ex_rid) injective =
    MDM.alloc ()
