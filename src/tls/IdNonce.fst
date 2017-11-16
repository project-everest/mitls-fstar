(* This module maintains a injective monotonic map from nonces to ids *)
module IdNonce
open TLSConstants
open FStar.Bytes
open FStar.Error
open TLSInfo

module N=Nonce
module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

//The goal of the rest of the module is to provide id_of_nonce
//and to prove that the two are mutual inverses
type n_id (n:random) = i:id{nonce_of_id i = n}

//nonce_id_table:
//  A monotone, injective partial map in the tls_tables_region, from random to rid
let nonce_id_table : MM.t tls_tables_region random n_id (fun x -> True) =
  MM.alloc #tls_tables_region #random #n_id #(fun x -> True)

let id_of_nonce (n:random) (i:n_id n) = MR.witnessed (MM.contains nonce_id_table n i)

val insert: n:random -> i:n_id n -> ST unit
  (requires (fun h -> MM.sel (MR.m_sel h nonce_id_table) n == None))
  (ensures (fun h0 _ h1 ->
      let nonce_id_table_as_hsref = MR.as_hsref nonce_id_table in
      (HS.modifies (Set.singleton tls_tables_region) h0 h1 /\
       HS.modifies_ref tls_tables_region (Set.singleton (Heap.addr_of (HH.as_ref (HS.MkRef?.ref nonce_id_table_as_hsref)))) h0 h1 /\
       id_of_nonce n i)))
let insert n i =
  MR.m_recall nonce_id_table;
  MM.extend nonce_id_table n i

val lookup: n:random -> ST (option (n_id n))
  (requires (fun h -> True))
  (ensures (fun h0 idopt h1 ->
    h0==h1 /\
    idopt == MM.sel (MR.m_sel h0 nonce_id_table) n /\
    (match idopt with
     | None -> True
     | Some i -> id_of_nonce n i)))
let lookup n = MM.lookup nonce_id_table n

val injectivity : n:random -> m:random -> i:n_id n -> j:n_id m ->  ST unit
  (requires (fun h -> i=!=j /\ id_of_nonce n i /\ id_of_nonce m j))
  (ensures (fun h0 _ h1 -> n<>m))
let injectivity n m i j =
  MR.testify (MM.contains nonce_id_table n i);
  MR.testify (MM.contains nonce_id_table m j)
