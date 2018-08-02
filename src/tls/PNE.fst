module PNE

module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128


open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.Error
open FStar.Bytes

open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg

    
let table_region = new_region tls_region

let tbl_ref (r:erid) (i:I.id) (u:info) : Tot Type0 =
  m_rref r (Seq.seq (entry i u)) grows

noeq type pne_state (i:I.id) (u:info) =
  | PNE_state :
    region: subrgn table_region ->
    key: lbytes 16 ->  
    tbl: tbl_ref region i u ->
    pne_state i u

let table (#i:I.id) (#u:info) (st:pne_state i u) (h:mem) : GTot (Seq.seq (entry i u)) =
  sel h (PNE_state?.tbl st)


let footprint (#i:I.id) (#u:info) (st:pne_state i u) =
  PNE_state?.region st
 

let create (i:I.id) (u:info) =
  let rg = new_region table_region in
  let k = CoreCrypto.random 16 in
  let t = ralloc #(Seq.seq (entry i u)) #grows rg Seq.empty in
  PNE_state rg k t

//todo use the real aes/chacha from evercrypt
assume val aes: lbytes 16 -> lbytes 16 -> lbytes 16

#reset-options "--z3rlimit 50"

let encrypt #i #u st #l n c =
  let s = sample_cipher c in
  let t = PNE_state?.tbl st in
  let k = PNE_state?.key st in
  let l' = U32.uint_to_t l in   
  if safePNE i then
    (let ne = CoreCrypto.random l in
    t := Seq.snoc (!t) (Entry s ne n);
    ne)
  else
    (let mask = Bytes.slice (aes k s) 0ul l' in 
    let ne = Bytes.xor l' (repr i u l n) mask in
    t := Seq.snoc (!t) (Entry s ne n);
    ne)
  

let decrypt #i #u st #l ne c =
  let s = sample_cipher c in
  let t = PNE_state?.tbl st in
  let k = PNE_state?.key st in
  let l' = U32.uint_to_t l in
  if safePNE i then
    (match Seq.find_l (sample_filter i u s) !t with
          | None -> None
          | Some (Entry _ ne' n) -> 
            if ne = ne' then Some n
            else None)
  else
    (let mask = Bytes.slice (aes k s) 0ul l' in
    let n = Bytes.xor l' ne mask in
    Some (abs i u l n))
