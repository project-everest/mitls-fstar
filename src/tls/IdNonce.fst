(* This module maintains a injective monotonic map from nonces to ids *)
module IdNonce
open TLSConstants
open FStar.Bytes
open FStar.Error
open TLSInfo

module MM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack

//The goal of the rest of the module is to provide id_of_nonce
//and to prove that the two are mutual inverses
type n_id (n:random) = i:id{nonce_of_id i = n}

//nonce_id_table:
//  A monotone, injective partial map in the tls_tables_region, from random to rid
let nonce_id_table : MM.t tls_tables_region random n_id (fun x -> True) =
  MM.alloc ()

let id_of_nonce (n:random) (i:n_id n) = witnessed (MM.contains nonce_id_table n i)

val insert: n:random -> i:n_id n -> ST unit
  (requires (fun h -> MM.fresh nonce_id_table n h))
  (ensures (fun h0 _ h1 ->
      (HS.modifies (Set.singleton tls_tables_region) h0 h1 /\
       HS.modifies_ref tls_tables_region (Set.singleton (HS.as_addr nonce_id_table)) h0 h1 /\
       id_of_nonce n i)))
let insert n i =
  recall nonce_id_table;
  MM.extend nonce_id_table n i

val lookup: n:random -> ST (option (n_id n))
  (requires (fun h -> True))
  (ensures (fun h0 idopt h1 ->
    h0==h1 /\
    (match idopt with
     | None -> MM.fresh nonce_id_table n h0
     | Some i -> MM.contains nonce_id_table n i h0 /\
                id_of_nonce n i)))
let lookup n = MM.lookup nonce_id_table n

val injectivity : n:random -> m:random -> i:n_id n -> j:n_id m ->  ST unit
  (requires (fun h -> i=!=j /\ id_of_nonce n i /\ id_of_nonce m j))
  (ensures (fun h0 _ h1 -> n<>m))
let injectivity n m i j =
  testify (MM.contains nonce_id_table n i);
  testify (MM.contains nonce_id_table m j)
