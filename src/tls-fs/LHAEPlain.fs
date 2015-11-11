(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module LHAEPlain
//open Seq
open Bytes
open Error
open TLSError
open TLSConstants
open TLSInfo
open Range

type adata = bytes

let makeAD (i:id) ((seqn,h):StatefulPlain.history) ad =
    let bn = bytes_of_seq seqn in
    bn @| ad

// We statically know that ad is big enough
let parseAD (i:id) ad = 
    let (snb,ad) = Bytes.split ad 8 in
    ad

type fragment = {contents:StatefulPlain.fragment}
type plain = fragment

let mk_plain (i:id) (ad:adata) (rg:range) b =
    let ad = parseAD i ad in
    let h = StatefulPlain.emptyHistory i in
    let p = StatefulPlain.mk_plain i h ad rg b in
    {contents =  p}

let reprFragment (i:id) (ad:adata) (rg:range) p =
    let ad = parseAD i ad in
    StatefulPlain.reprFragment i ad rg p.contents

let repr i ad rg p = reprFragment i ad rg p

let statefulPlainToLHAEPlain (i:id) (h:StatefulPlain.history) 
    (ad:StatefulPlain.adata) (ad':adata) (r:range) f = {contents = f}
let lhaePlainToStatefulPlain (i:id) (h:StatefulPlain.history) 
    (ad:StatefulPlain.adata) (ad':adata) (r:range) f = f.contents

let makeExtPad id ad rg p =
    let ad = parseAD id ad in
    let c = p.contents in
    let c = StatefulPlain.makeExtPad id ad rg c in
    {contents = c}

let parseExtPad id ad rg p =
    let ad = parseAD id ad in
    let c = p.contents in
    match StatefulPlain.parseExtPad id ad rg c with
    | Error(x) -> Error(x)
    | Correct(c) -> correct ({contents = c}) 

#if ideal
let widen i ad r f =
    let ad' = parseAD i ad in
    let f' = StatefulPlain.widen i ad' r f.contents in
    {contents = f'}
#endif
