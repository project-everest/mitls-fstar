module PNE2
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


//let pnlen = 4

val table_region : rgn

type prfid = Flag.prfid

let safePNE (j:prfid) = Flag.safePNE j

type cipher = b:bytes{Bytes.length b >= 16}

type mask = lbytes 16 

type ciphersample = lbytes 16

//type pnlen = n:nat{n<=16}
//let pnlen = n:nat{n=1 \/ n=2 \/ n=4}

//type epn (l:pnlen) = lbytes l

(*
noeq type pn_pkg =
  | PNPkg:
    pn: (i:I.id -> l:pnlen -> (t:Type0{hasEq t})) ->
    as_bytes: (i:I.id -> l:pnlen -> pn i l -> GTot (lbytes l)) ->
    repr: (i:I.id{~(safePNE i)} -> l:pnlen -> n:pn i l -> Tot (b:lbytes l{b == as_bytes i l n})) ->
    from_bytes: (i:I.id -> l:pnlen -> b:lbytes l -> GTot (n:pn i l{as_bytes i l n == b})) ->
    abs: (i:I.id{~(safePNE i)} -> l:pnlen -> b:lbytes l -> Tot (n:pn i l{n == from_bytes i l b})) ->
    pn_pkg

let info = pn_pkg

let pn (i:I.id) (u:info) (l:pnlen) = PNPkg?.pn u i l

let repr (i:I.id{~(safePNE i)}) (u:info) (l:pnlen) (n:pn i u l) = PNPkg?.repr u i l n

let abs (i:I.id{~(safePNE i)}) (u:info) (l:pnlen) (b:lbytes l) = PNPkg?.abs u i l b
*)
type entry (j:prfid) =
  | Entry :
    c:cipher ->
    m:mask ->
    entry j

val pne_state : (j:prfid) -> Type0

val table : (#j:prfid) -> (st:pne_state j) -> (h:mem) -> GTot (Seq.seq (entry j))

val footprint : #j:prfid -> st:pne_state j -> GTot (subrgn table_region)

val frame_table: #j:prfid -> st:pne_state j -> l:Seq.seq (entry j) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
    (requires
      safePNE j /\
      table st h0 == l /\
      modifies s h0 h1 /\
      Set.disjoint s (Set.singleton (footprint st)))
    (ensures table st h1 == l)

let cipher_filter (j:prfid) (c:cipher) (e:entry j) : bool =
  Entry?.c e = c

let entry_for_cipher (#j:prfid) (c:cipher) (st:pne_state j) (h:mem) :
  GTot (option (entry j)) =
  Seq.find_l (cipher_filter j c) (table st h)
  
let fresh_cipher (#j:prfid) (c:cipher) (st:pne_state j) (h:mem) :
  GTot bool =
  None? (entry_for_cipher c st h)

let sample_cipher (c:cipher) : s:ciphersample =
  Bytes.slice c 0ul 16ul

val create (j:prfid) : ST (pne_state j)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    modifies_none h0 h1 /\
    table st h1 == Seq.empty)

val compute :
  (#j:prfid) ->
  (st:pne_state j) ->
  (c:cipher) ->
  ST (mask)
  (requires fun h0 -> True)
  (ensures fun h0 m h1 ->
    modifies_one (footprint st) h0 h1 /\
    (safePNE j ==>
      (match (entry_for_cipher c st h0) with
        | None -> table st h1 == Seq.snoc (table st h0) (Entry c m)
        | Some (Entry _ m') -> m = m')))



