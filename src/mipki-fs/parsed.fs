module Parsed

open Asn1
open TplAst

type parsed = (string * binding) list

and binding =
| B_VALUE of asnval
| B_FRAME of parsed list

type pref = parsed ref

exception Duplicate_binding of string

let create () : pref = ref []

let rec lookup (p:pref) (x:string) : option<binding> =
    let rec aux = function
    | (k,v)::t -> if k=x then Some(v) else aux t
    | [] -> None
    aux !p

let append (p:pref) (k:string) (v:asnval) =
//    printfn "ADD %s %A" k (snd v |> SBA.b2ba)
    match lookup p k with
    | None -> p := (k, B_VALUE(v)) :: !p
    | Some(_) -> raise (Duplicate_binding k)

let appendf (p:pref) (k:string) (v:parsed list) =
    match lookup p k with
    | None -> p := (k, B_FRAME(v)) :: !p
    | Some(_) -> raise (Duplicate_binding k)

let value (p:pref) =
    List.rev !p