(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
#light "off"

module AppFragment
open Platform.Bytes
open TLSInfo
open Range
open DataStream
open Platform.Error
open TLSError

#if ideal
type fpred = DeltaFragment of epoch * stream * range * delta
#endif

type preFragment = {frag: epoch * stream * delta}
type fragment = preFragment
type plain = fragment

let mk_fragment e s r d =
    let i = mk_id e in
    let f = {frag = e,s,d} in
    #if ideal
    Pi.assume (DeltaFragment(e,s,r,d));
    #endif
    let s' = append e s r d in
    (f,s')

let check (e:epoch) (e':epoch) = ()

let delta e s r f =
    let (e',s',d) = f.frag in
    // the following idealization is reindexing.
    #if ideal
    if auth e then
      // typechecking relies on e = e' & s = s':
      // they both follow from Auth(e), implying Sent(e,s,r,f) hence ?d. f.frag = (e,s,d)
      let s'' = append e s r d in
      (d,s'')
    else
      // we coerce d to the local epoch
      //CF 14-07-15 ??
      //CF below, we can't prove not(Safe(e')).
      //CF from Id(e') = Id(e), we should get not(AuthId(Id(e')) => not(Auth(e')) => not(Safe(e'))
      let raw = deltaRepr e' s' r d in
      let d' = deltaPlain e s r raw in
      let s'' = append e s r d' in
      (d',s'')
    #else
      // we could skip this append
      let s'' = append e s r d in
      (d,s'')
    #endif

let mk_plain i r b =
  let e = TLSInfo.unAuthIdInv i in // CF review
  let s = DataStream.init e in
  let d = DataStream.deltaPlain e s r b in
  {frag = (e,s,d)}

let repr (i:id) r f =
  let (e',s,d) = f.frag in
  DataStream.deltaRepr e' s r d

let makeExtPad (i:id) (r:range) (f:fragment) =
#if TLSExt_extendedPadding
    if Extensions.hasExtendedPadding i then
        let (e',s,d) = f.frag in
        //AP: This e' has no relation to i.
        //AP: In particular, e' misses crucial information such as negotiated ciphersute and extensions
        //AP: So, we're forced to do the padding here, rather than in DataStream
        let b = DataStream.deltaBytes e' s r d in
        let len = length b in
        let pad = extendedPad i r len in
        let padded = pad@|b in
        let d = DataStream.createDelta e' s r padded in //CF breaking abstraction
        {frag = (e',s,d)}
    else
#endif
        f

let parseExtPad (i:id) (r:range) (f:fragment) : result (fragment) =
#if TLSExt_extendedPadding
    if Extensions.hasExtendedPadding i then
        let (e',s,d) = f.frag in
        let b = DataStream.deltaBytes e' s r d in
        match TLSConstants.vlsplit 2 b with
        | Error(x) -> Error(x)
        | Correct(res) ->
            let (_,b) = res in
            let d = DataStream.createDelta e' s r b in //CF breaking abstraction
            correct ({frag = (e',s,d)})
    else
#endif
        correct f

#if ideal
let widen (i:id) (r0:range) (f0:fragment) =
    let r1 = rangeClass i r0 in
    let (e,s,d0) = f0.frag in
    let d1 = DataStream.widen e s r0 r1 d0 in
    let (f1,_) = mk_fragment e s r1 d1 in
    f1
#endif




(*KB unused
val delta': ki:epoch -> s:(;Id(ki)) stream -> r:range ->
  f:(;Id(ki),r) fragment{not AuthId(ki)} ->
  d:(;Id(ki),s,r) delta * s':(;Id(ki)) stream{s' = ExtendStreamDelta(Id(ki),s,r,d)}

let delta' e s r f =
    let i = id e in
    let (s',d) = f.frag in
    let b = DataStream.deltaRepr i s' r d in
    let d = DataStream.deltaPlain i s r b in
    let s'' = append i s r d in
    (d,s'')
*)
