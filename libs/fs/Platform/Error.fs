(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Error

type ('a,'b) optResult =
    | Error of 'a
    | Correct of 'b

let perror (file:string) (line:string) (text:string) =
#if verify
    text
#else
    Printf.sprintf "Error at %s:%s: %s." file line (if text="" then "No reason given" else text)
#endif

let correct x = Correct x

let unexpected info = failwith info
let unreachable info = failwith info

let ideal_flag = true
let if_ideal e d = if ideal_flag then e() else d

let mem x l = List.tryFind (fun y -> y = x) l <> None
