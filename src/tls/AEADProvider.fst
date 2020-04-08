module AEADProvider

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes

open Mem
open TLSConstants
open FStar.UInt32

module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = EverCrypt
module LB = LowStar.Buffer
module CI = Crypto.Indexing
module Plain = Crypto.Plain
module CB = Crypto.Symmetric.Bytes

let iv (i:id) = lbytes (iv_length i)

let coerce_iv (i:id) (b:lbytes (iv_length i)) : Tot (iv i) = b


#reset-options "--using_facts_from '* -LowParse.Spec.Base'"
 
let create_nonce (#i:id) (#rw:rw) (st:state i rw) (n:nonce i): Tot (i:iv i) =
  let salt = salt_of_state st in
  match (TLSInfo.pv_of_id i, alg i) with
  | (TLS_1p3, _) | (_, EverCrypt.CHACHA20_POLY1305) ->
    xor_ #(iv_length i) n salt
  | _ ->
    assert(Bytes.length salt + Bytes.length n = iv_length i);
    salt @| n

let lemma_nonce_iv (#i:id) (#rw:rw) (st:state i rw) (n1:nonce i) (n2:nonce i)
  : Lemma (create_nonce st n1 == create_nonce st n2 ==> n1 == n2) =
  admit ();  //AR: 04/08/2019: This proof was admitted already
  let salt = salt_of_state st in
  match (TInfo.pv_of_id i, alg' i) with
  | (TLS_1p3, _) | (_, EverCrypt.CHACHA20_POLY1305) ->
    xor_idempotent (UInt32.uint_to_t (iv_length i)) n1 salt;
    xor_idempotent (UInt32.uint_to_t (iv_length i)) n2 salt
  | _ ->
    if (salt @| n1) = (salt @| n2) then
      () //lemma_append_inj salt n1 salt n2 //TODO bytes NS 09/27

#set-options "--admit_smt_queries true"
let encrypt (#i:id) (#l:plainlen) (w:writer i) (iv:iv i) (ad:adata i) (plain:plain i l)
  : ST (cipher:cipher i l)
       (requires (fun h -> True))
       (ensures (fun h0 cipher h1 -> modifies_none h0 h1))
  =
  push_frame ();
  dbg ("ENCRYPT[N="^(hex_of_bytes iv)^",AD="^(hex_of_bytes ad)^"]");
  let adlen = uint_to_t (length ad) in
  let plainlen = uint_to_t l in
  let taglen = uint_to_t (taglen i) in
  let cipherlen = plainlen +^ taglen in
  let ad = from_bytes ad in
  let cipher_tag = LB.alloca 0uy cipherlen in
  let cipher = LB.sub cipher_tag 0ul plainlen in
  let tag = LB.sub cipher_tag plainlen taglen in
  let iv = from_bytes iv in
  let plain =
    if not (TLSInfo.safeId i)
    then from_bytes plain
    else LB.alloca 0uy plainlen
  in
  EverCrypt.aead_encrypt (fst w) iv ad adlen plain plainlen cipher tag;
  let cipher_tag_res = FStar.Bytes.of_buffer cipherlen cipher_tag in
  pop_frame();
  cipher_tag_res

let decrypt (#i:id) (#l:plainlen) (st:reader i) (iv:iv i) (ad:adata i) (cipher:cipher i l)
  : ST (co:option (plain i l))
       (requires (fun _ -> True))
//  (requires (fun _ ->
//    FStar.UInt.size (length ad) 32
//    /\ FStar.UInt.size (length cipher) 32
//    /\ length cipher >= CC.aeadTagSize (alg i))
       (ensures (fun h0 plain h1 -> modifies_none h0 h1))
  =
  push_frame();
  dbg ("DECRYPT[N="^(hex_of_bytes iv)^",AD="^(hex_of_bytes ad)^"]");
  let iv = from_bytes iv in
  let adlen = uint_to_t (length ad) in
  let ad = from_bytes ad in
  let plainlen = uint_to_t l in
  let taglen = uint_to_t (taglen i) in
  let cipher_tag_buf = from_bytes cipher in
  let cipher = LB.sub cipher_tag_buf 0ul plainlen in
  let tag = LB.sub cipher_tag_buf plainlen taglen in
  let plain = LB.alloca 0uy plainlen in
  let ok = EverCrypt.aead_decrypt (fst st) iv ad adlen plain plainlen cipher tag in
  let ret =
    if ok = 1ul
    then Some (FStar.Bytes.of_buffer plainlen plain)
    else None
  in
  pop_frame();
  ret
