open Bytes

let is_some o = match o with Some x -> true | _ -> false
let get_some o = match o with Some x -> x | _ -> failwith "get_some: expected Some"

let fold (op: bytes-> bytes-> bytes) state data = List.fold_left op state data
let filter f l = List.filter f l
let foldBack (f:bytes -> bytes -> bytes) bl s = List.fold_right f bl s
let exists f l = List.exists f l
let memr l x = List.exists (fun y -> x = y) l
let choose f l = List.map get_some (List.filter is_some (List.map f l))
let tryFind f l = try Some (List.find f l) with _ -> None
let listLength (l:'a list) = List.length l
let listHead (l:'a list) = List.hd l
let find f l = List.find f l
let map f l = List.map f l