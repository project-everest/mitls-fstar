module TplAst

open SBA
open Asn1

type asnoption =
| O_REQUIRED
| O_OPTIONAL of option<asn1>

type asntag = option<int * bool> // false = explicit, true = implicit

type asntpl =
| TPL_CHOICE of list<asntag * asntpl>                 // choice between tag-unambiguous options
| TPL_SEQ of bool * list<asntag * asnoption * asntpl> // fixed sequencing; flag ? SET : SEQUENCE 
| TPL_SEQOF of string * bool * (int * int) * asntpl   // unknown, homogeneous sequence, with min and max numbers of elements matching the template
| TPL_DEFINEDBY of string * list<asnval * asntpl>     // One of multiple templates based on a previous value
| TPL_ENCAPSULATED of bool * asntpl                   // flag ? Bitstring : Octet 
| TPL_CONSTANT of asnval
| TPL_VARIABLE of string * asntype * list<asnval>

exception Undefined_template_var of string;

let tvar : (string * asntpl) list ref = ref []

let savetpl x tpl =
  tvar := (x, tpl) :: !tvar

let lookup x =
  let rec aux = function
  | (k,v) :: t -> if x=k then v else aux t
  | [] -> raise (Undefined_template_var x)
  aux !tvar

let tplsub sub tpl =
    let subs x =
        let rec aux =
            function
            | (k,v) :: t -> if x=k then v else aux t
            | [] -> x
        aux sub
    let rec aux =
        function
        | TPL_CHOICE(l) -> TPL_CHOICE(List.map (fun (x,y)->(x, aux y)) l)
        | TPL_SEQ(f, l) -> TPL_SEQ(f, List.map (fun (x,y,z)->(x, y, aux z)) l)
        | TPL_SEQOF(s, f, len, t) -> TPL_SEQOF(subs s, f, len, aux t)
        | TPL_DEFINEDBY(s, l) -> TPL_DEFINEDBY(subs s, List.map (fun (x,y)->(x, aux y)) l)
        | TPL_ENCAPSULATED(f, t) -> TPL_ENCAPSULATED(f, aux t)
        | TPL_VARIABLE(s, t, v) -> TPL_VARIABLE(subs s, t, v)
        | x -> x
    aux tpl