module Blah

// module HS = FStar.HyperStack

// type rset = FStar.Set.set nat

// let rset_union (s1:rset) (s2:rset): Tot rset = Set.union s1 s2

// let main () = 
//   let q = rset_union (Set.singleton 1) (Set.singleton 2) in
//   if Set.mem 2 q then 0 else 1

// let main () =
//   let bs = FStar.Bytes.twobytes (41uy, 42uy) in
//   match Format.ECCurveType.ecCurveType_parser32 bs with
//   | Some _ -> 1
//   | _ -> 2

// let main () =
//   let bs = FStar.Bytes.create 5ul 1uy in
//   Bytes.length bs

#set-options "--use_two_phase_tc false"
let tls_client_label = FStar.Bytes.utf8_encode "client finished"
