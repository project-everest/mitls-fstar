module PNE
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

let safePNE (i:I.id) = Flag.safePNE i

type cipher = b:bytes{Bytes.length b >= 16}

type ciphersample = lbytes 16

//type pnlen = n:nat{n<=16}
let pnlen = n:nat{n=1 \/ n=2 \/ n=4}

type epn (l:pnlen) = lbytes l


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

type entry (i:I.id) (u:info) =
  | Entry :
    s:ciphersample ->
    #l:pnlen -> 
    ne:epn l ->
    n:pn i u l ->
    entry i u

val pne_state : i:I.id -> u:info -> Type0

val table : (#i:I.id) -> (#u:info) -> (st:pne_state i u) -> (h:mem) -> GTot (Seq.seq (entry i u))

val footprint : #i:I.id -> #u:info -> st:pne_state i u -> GTot (subrgn table_region)
 
let sample_filter (i:I.id) (u:info) (s:ciphersample) (e:entry i u) : bool =
  Entry?.s e = s

let entry_for_sample (#i:I.id) (#u:info) (s:ciphersample) (st:pne_state i u) (h:mem) :
  GTot (option (entry i u)) =
  Seq.find_l (sample_filter i u s) (table st h)
  
let fresh_sample (#i:I.id) (#u:info) (s:ciphersample) (st:pne_state i u) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)

let sample_cipher (c:cipher) : s:ciphersample =
  Bytes.slice c 0ul 16ul

val create (i:I.id) (u:info) : ST (pne_state i u)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    modifies_none h0 h1 /\
    table st h1 == Seq.empty)

val encrypt :
  (#i:I.id) ->
  (#u:info) ->
  (st:pne_state i u) ->
  (#l:pnlen) ->
  (n:pn i u l) ->
  (c:cipher) ->
  ST (epn l)
  (requires fun h0 ->
    fresh_sample (sample_cipher c) st h0)
  (ensures fun h0 ne h1 ->
    modifies_one (footprint st) h0 h1 /\
    (let s = sample_cipher c in
    table st h1 == Seq.snoc (table st h0) (Entry s ne n)))

val decrypt :
  (#i:I.id) ->
  (#u: info) ->
  (st:pne_state i u) ->
  (#l:pnlen) ->
  (ne:epn l) ->
  (c:cipher) ->
  ST (option (pn i u l))
  (requires fun h0 -> True)
  (ensures fun h0 on h1 ->
    modifies_none h0 h1 /\
    (let s = sample_cipher c in
      (safePNE i ==>
        (match entry_for_sample s st h0 with
          | None -> None? on
          | Some (Entry _ ne' n) -> 
            if ne = ne' then on = Some n
            else None? on)
      )
    )
  )
  

