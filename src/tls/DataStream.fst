module DataStream

(* Application-level bytes streams exchanged over TLS;            *)
(* depending on the safety of their indexes,                      *)
(* these streams are treated abstractly by miTLS                  *)

//* now generalized to include signals; rename to Stream?

open FStar
open Heap
open FStar.HyperHeap
open Seq
open SeqProperties
open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range

//--------- application data fragments ------------------------------

// The implementation of this type is application-specific
// but it must provide a few functions to TLS, declared below.
// On safe connections, TLS ensures privacy by type abstraction
// we care about the range mostly on the sender side.

// this style enables structural subtyping on range indexes
private type pre_fragment (i:id) = bytes
val ghost_repr: #i:id -> pre_fragment i -> GTot bytes
let ghost_repr i f = f

type fragment (i:id) (rg:range) = f:pre_fragment i { Within (length (ghost_repr f)) rg}

val repr:       #i:id { ~(safeId i)} -> rg:frange i -> p:fragment i rg -> Tot (b:rbytes rg {b = ghost_repr #i p})
val mk_fragment: i:id { ~(authId i)} -> rg:frange i -> b:rbytes rg -> Tot (p:fragment i rg {b = ghost_repr #i p})

let repr i rg f = f
let mk_fragment i rg b = b

(* revisit:
// these two functions are used only by the application (or ghostly)
val createDelta: i:id -> rg:range -> rbytes rg -> Tot (fragment i rg)
val deltaBytes:  i:id -> rg:range -> fragment i rg -> Tot (rbytes rg)

let createDelta i rg f = f
let deltaBytes  i rg f = f

// these two functions are used only on unsafe epochs
//* how to specify both abstraction & functional correctness? see AppData.fs7
val deltaPlain: i:id { ~(authId i)}-> rg:range -> rbytes rg -> Tot (fragment i rg)
val deltaRepr:  i:id { ~(safeId i)}-> rg:range -> fragment i rg -> Tot (rbytes rg)

let deltaPlain i rg f = f
let deltaRepr  i rg f = f
*)


//----------application events (data + control) -------------------

type delta (i:id) =
  | Data of fragment i fragment_range
  | Close
  | Alert of alertDescription

val final: i:id -> delta i -> Tot bool
let final i d =
  match d with
  | Data f  -> false
  | Close   -> true
  | Alert a -> isFatal a

let finalized i s = is_Some (List.find (final i) s)

val wellformed: i:id -> list (delta i) -> Tot bool
let rec wellformed ki s =
  match s with
  | [] | [_] -> true
  | d::s -> not (final ki d)

type stream (i:id) = s: list (delta i) { wellformed i s }

// on authentic encrypted streams, 
// the (ghost, viewed) writer state is the current stream contents;
// the (ghost, viewed) reader state is an index in the stream.


// --- experimental
//* not much point sharing the two? is it re-implementing AppData?
//* maybe the state is just an rref?

type state (i:id) =
  | State: #region:rid ->
           log: option (rref region (stream i)) { is_Some log <==> authId i } ->
           ctr: rref region nat ->
           state i

val gen: r0:rid -> i:id -> (state i * state i)
let gen r0 (i:id) =
  let r = new_region r0 in
  let log = if authId i then Some (ralloc r []) else None in
  let ctr = ralloc r 0 in
  let enc = State #i #r log ctr in
  let dec = State #i #r log ctr in
  enc, dec

// -------------------------------------------------------------

// Auxiliary functions for ranges & splitting
//* relocate?

let min (a:nat) (b:nat) =
    if a <= b then a else b

(* commenting out splitting code for now...

// note these two functions are currently typed in ML, hence unusable

val maxLHPad: id -> l:nat{l < fragmentLength} -> nat
val splitRange: id:epoch -> r:range -> s:(range * range) { r = sum (fst s) (snd s) }
//* nicer syntax for refined tuples?
// (* )/\ within r0 r *))

let maxLHPad id len =
    let fs = TLSInfo.fragmentLength in
    let ps = maxPadSize id in
    let thisPad = min ps (fs-len) in
    let authEnc = id.aeAlg in
    match authEnc with
    | MtE encAlg macAlg ->
        (match encAlg with
        | Stream _ -> thisPad
        | Block alg ->
            let bs = blockSize alg in
            let ms = macSize (macAlg_of_id id) in
            let pl = fixedPadSize id in
            let overflow = (len + thisPad + ms + ps) % bs in
            if overflow > thisPad then
                thisPad
            else
                thisPad - overflow)
    | AEAD _ _ -> thisPad
    | _ -> unexpected "[maxLHPad] invoked on an invalid ciphersuite"

let splitRange ki r =
    let (l,h) = r in
    let si = epochSI(ki) in
    let cs = si.cipher_suite in
    let fs = TLSInfo.fragmentLength in
    let id = mk_id ki in
    let ps = maxPadSize id in
    if ps = 0 || l = h then
        // no LH to do
        if l<>h then
            unexpected "[splitRange] Incompatible range provided"
        else
            let len = min h fs in
            let r0 = (len,len) in
            let r1 = (l-len,h-len) in
            (r0,r1)
    else
        if l >= fs then
            let r0 = (fs,fs) in
            let r1 = (l-fs,h-fs) in
            (r0,r1)
        else
            let allPad = maxLHPad id l in
            let allPad = min allPad (h-l) in
            if l+allPad > fs then
                unexpected "[splitRange] Computing range over fragment size"
            else
                let r0 = (l,l+allPad) in
                let r1 = (0,h - (l+allPad)) in
                (r0,r1)

// ----------------------------------------

val split: ki:epoch -> r0:range -> r1:range -> f:fragment ki (sum r0 r1) ->
  r : (fragment ki r0 * f1: fragment ki r1)
  {	deltaBytes ki (sum r0 r1) f = (deltaBytes ki r0 (fst r) @| deltaBytes ki r1 (snd r)) }

let split ki r0 r1 f =
  let (_,h0) = r0 in
  let (l1,_) = r1 in
  let len = length f in
  let n = if h0 < (len - l1) then h0 else len - l1 in
  let (sb0,sb1) = Platform.Bytes.split f n in
  (sb0,sb1)
*)

(*

//CF 14-07-15 why this hack, just for performance?
let append (ki:epoch) (s:stream) (r:range) (d:delta r) =
//#if ideal
    let dc = d.contents in
    let c = cbytes dc in
    {sb = c :: s.sb}
//#else
//    s
//#endif

//#if ideal
let widen (ki:epoch) (s:stream) (r0:range) (r1:range) (d:delta r0) : delta r1 = d
//#endif
*)
