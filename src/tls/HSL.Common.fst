module HSL.Common

open FStar.Integers

open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

type bytes = LowParse.Bytes.bytes

(* Debug output, shared by client and server *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("HSL| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_HSL then print else (fun _ -> ())

#set-options "--max_fuel 0 --max_ifuel 0"

[@"opaque_to_smt"]
let format_hs_msg (m:HSM.handshake) : GTot bytes =
  HSM.handshake_serializer m

[@"opaque_to_smt"]
let format_hs12_msg (m:HSM12.handshake12) : GTot bytes =
  HSM12.handshake12_serializer m

[@"opaque_to_smt"]
let format_hs13_msg (m:HSM13.handshake13) : GTot bytes =
  HSM13.handshake13_serializer m

/// Buffer [from, to) is a serialization of m

let valid_parsing (m:HSM.handshake) (from to:uint_32) (b:B.buffer uint_8) (h:HS.mem) =
  from <= to /\ to <= B.len b /\
  (let buf = B.gsub b from (to - from) in
   format_hs_msg m == B.as_seq h buf)

let valid_parsing12 (m:HSM12.handshake12) (from to:uint_32) (b:B.buffer uint_8) (h:HS.mem) =
  from <= to /\ to <= B.len b /\
  (let buf = B.gsub b from (to - from) in
   format_hs12_msg m == B.as_seq h buf)

let valid_parsing13 (m:HSM13.handshake13) (from to:uint_32) (b:B.buffer uint_8) (h:HS.mem) =
  from <= to /\ to <= B.len b /\
  (let buf = B.gsub b from (to - from) in
   format_hs13_msg m == B.as_seq h buf)

let region_includes r l = B.loc_regions true (Set.singleton r) `B.loc_includes` l
