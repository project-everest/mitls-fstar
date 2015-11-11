(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module List

open Bytes

let fold (op: bytes-> bytes-> bytes) state data = List.fold op state data
let filter f l = List.filter f l
let foldBack (f:bytes -> bytes -> bytes) bl s = List.foldBack f bl s
let exists f l = List.exists f l
let memr l x = List.exists (fun y -> x = y) l
let choose f l = List.choose f l
let tryFind f l = List.tryFind f l
let listLength (l:'a list) = l.Length
let listHead (l:'a list) = l.Head
let find f l = List.find f l
let map f l = List.map f l
