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


let pnlen = 4

val table_region : rgn

let safePNE (i:I.id) = Flag.safePNE i

type cipher = b:bytes{Bytes.length b >= 16}

type ciphersample = lbytes 16

type epn = lbytes pnlen

noeq type pn_pkg =
  | PNPkg:
    pn: (i:I.id -> (t:Type0{hasEq t})) ->
    as_bytes: (i:I.id -> pn i -> GTot (lbytes pnlen)) ->
    repr: (i:I.id{~(safePNE i)} -> n:pn i -> Tot (b:lbytes pnlen{b == as_bytes i n})) ->
    from_bytes: (i:I.id -> b:lbytes pnlen -> GTot (n:pn i{as_bytes i n == b})) ->
    abs: (i:I.id{~(safePNE i)} -> b:lbytes pnlen -> Tot (n:pn i{n == from_bytes i b})) ->
    pn_pkg

let info = pn_pkg

let pn (i:I.id) (u:info) = PNPkg?.pn u i

let repr (i:I.id{~(safePNE i)}) (u:info) (n:pn i u) = PNPkg?.repr u i n

let abs (i:I.id{~(safePNE i)}) (u:info) (b:lbytes pnlen) = PNPkg?.abs u i b

type entry (i:I.id) (u:info) =
  | Entry :
    s:ciphersample ->
    ne:epn ->
    n:pn i u ->
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
  (n:pn i u) ->
  (c:cipher) ->
  ST epn
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
  (ne:epn) ->
  (c:cipher) ->
  ST (option (pn i u))
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
  

