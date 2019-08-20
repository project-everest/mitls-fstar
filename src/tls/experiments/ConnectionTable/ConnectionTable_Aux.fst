module ConnectionTable_Aux

let configuration = FStar.UInt8.t

type client_hello =
  | CH: random:FStar.UInt32.t -> cookie:bool -> client_hello

let ch_random (CH random _) = random

let cookie = FStar.UInt32.t

let has_cookie (CH _ cookie) = cookie

let ch_of_cookie (CH random cookie) = CH random false

let ch_compatible ch cfg = true

let rgn = HyperStack.ST.new_region HyperStack.root
