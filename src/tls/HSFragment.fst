(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module HSFragment
open Platform.Bytes
open TLSInfo
module Range = Range
open Range
open Platform.Error
open TLSError

type fragment = {frag: rbytes}
type stream = {sb:list (bytes)}
type plain = fragment

let fragmentPlain (ki:id) (r:range) b = {frag = b}
let fragmentRepr (ki:id) (r:range) f = f.frag

let init (e:id) = {sb=[]}
let extend (e:id) (s:stream) (r:range) (f:fragment) =
#if ideal
    {sb = f.frag :: s.sb}
#else
    s
#endif

let reStream (e:id) (s:stream) (r:range) (p:plain) (s':stream) = p

let makeExtPad (i:id) (r:range) (p:plain) =
#if TLSExt_extendedPadding
    if Extensions.hasExtendedPadding i then
        let f = p.frag in
        let len = length f in
        let pad = extendedPad i r len in
        {frag = pad@|f}
    else
#endif
        p

let parseExtPad (i:id) (r:range) (p:plain) : result (plain) =
#if TLSExt_extendedPadding
    if Extensions.hasExtendedPadding i then
        let f = p.frag in
        match TLSConstants.vlsplit 2 f with
        | Error(x) -> Error(x)
        | Correct(res) ->
            let (_,f) = res in
            correct ({frag = f})
    else
#endif
        correct p

#if ideal
let widen (e:id) (r0:range) (r1:range) (f0:fragment) =
    let b = f0.frag in {frag = b}
#endif
