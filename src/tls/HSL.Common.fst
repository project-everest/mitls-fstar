module HSL.Common

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HashSpec = Hashing.Spec
module HSM = HandshakeMessages

module LP = LowParse.Low.Base

type hbytes = Spec.Hash.Definitions.bytes


/// TODO: define using high-level serializers from LowParse

assume val format_hs_msg (m:HSM.hs_msg) : Tot hbytes


/// TODO: LowParse definition of saying buf is a valid serialization of m

let valid_parsing_aux (m:HSM.hs_msg) (buf:B.buffer uint_8) (h:HS.mem) =
  format_hs_msg m == B.as_seq h buf


/// Helper to enforce spatial safety of indices in the st input buffer
/// and that the buffer is a serialization of m

let valid_parsing (m:HSM.hs_msg) (from to:uint_32) (b:B.buffer uint_8) (h:HS.mem) =
  from <= to /\
  to <= B.len b /\
  (let buf = B.gsub b from (to - from) in
   valid_parsing_aux m buf h)

let region_includes r l = B.loc_regions true (Set.singleton r) `B.loc_includes` l
