module Tplverifier

open SBA
open Asn1
open TplAst

exception Template_mismatch of asntpl * asn1
exception Missing_element of asntpl
exception Value_mismatch of list<asnval> * asnval
exception Tag_mismatch of asntpl * asn1
exception Unexpected_element of asn1
exception Invalid_defby of string
exception Invalid_numberof of asntpl
exception No_matching_option of asntpl
exception Invalid_encapsulated of asnval

let tpl_verify (tpl:asntpl) (input:asn1) : Parsed.parsed =
    let res = ref (Parsed.create ())
    let rec aux ignty tpl x =
//        printfn "============\nCMP %A %A\n===========\n\n" tpl x
        match (tpl, x) with
        | (TPL_CHOICE(l), x) ->
            aux2 (List.map (fun (tag,t)->(tag, O_OPTIONAL(None), t)) l) [x]
        | (TPL_SEQ(f1, l1), A_SEQ(f2, l2)) when f1=f2 ->
            aux2 l1 l2
        | (TPL_SEQOF(s, f1, (min,max), t), A_SEQ(f2, l2)) when f1=f2 ->
            let ln = List.length l2 in
                if (ln < min) || (ln > max && max > 0) then
                    raise (Invalid_numberof t)
            let cur = !res
            let elem cur x =
                res := Parsed.create ()
                aux false t x
                (Parsed.value !res) :: cur
            let frame = List.fold elem [] l2 |> List.rev
            Parsed.appendf cur s frame
            res := cur
        | (TPL_ENCAPSULATED(f, t), A_ENC(f2, x)) when f=f2 ->
            aux false t x
        | (TPL_ENCAPSULATED(f, t), A_CST(ty, v)) when (not f && ty=C_STR(S_OCTET)) || (f && ty=C_STR(S_BIT)) ->
            if f then match b2list v with 0uy :: _ -> () | _ -> raise (Invalid_encapsulated (ty, v))
            let dec = Asn1decode.asn1_decode (b2ba (if f then sub v 1 0 else v)) in
            aux false t dec
        | (TPL_CONSTANT(ty, v), A_CST(ty2, v2)) ->
            if (ignty || ty=ty2) && beq v v2 then ();
            else raise (Template_mismatch(tpl, x))
        | (TPL_VARIABLE(n, ty, pv), A_CST(ty2, v2)) ->
            if (ignty || ty=ty2) && (pv=[] || List.exists (fun (tt,tv) -> beq v2 tv) pv) then
                Parsed.append !res n (ty2, v2)
            else raise (Tag_mismatch(tpl, x))
        | (TPL_DEFINEDBY(s, l), x) ->
            match Parsed.lookup !res s with
            | Some(Parsed.B_VALUE(_, v)) ->
                match List.tryFind (fst >> snd >> (beq v)) l with
                | None ->
                    match List.rev l with
                    | ((C_NULL, bTrue), t) :: _ -> aux false t x
                    | _ -> raise (Invalid_defby(s))
                | Some(_, tpl) -> aux false tpl x
            | _ -> raise (Invalid_defby s)
        | _ -> raise (Tag_mismatch(tpl, x))
    and aux2 (it:list<asntag * asnoption * asntpl>) (inp:list<asn1>) =
//        printfn "============\nCMP %A %A\n===========\n\n" it inp
        match it with
        | (Some(ti, f), o, t) :: rt ->
            match inp with
            | A_TAG(i, x) :: xr when not f && ti=i -> 
                aux f t x
                aux2 rt xr
            | A_CST(C_CUSTOM(i), v) :: xr when f && ti=i -> 
                aux f t (List.head inp)
                aux2 rt xr
            | _ ->
                match o with
                | O_REQUIRED -> raise (Missing_element(t))
                | O_OPTIONAL(None) -> aux2 rt inp
                | O_OPTIONAL(Some d) -> aux f t d; aux2 rt inp
        | (None, o, t) :: rt ->
            match inp with
            | x :: xr -> 
                try
                    aux false t x
                    aux2 rt xr
                with
                | Tag_mismatch(u, v) when o<>O_REQUIRED && u=t && v=x ->
                    match o with
                    | O_OPTIONAL(None) -> aux2 rt inp
                    | O_OPTIONAL(Some d) -> aux false t d; aux2 rt inp
                    | O_REQUIRED -> failwith "Not possible"
            | [] ->
                match o with
                | O_OPTIONAL(None) -> aux2 rt inp
                | O_OPTIONAL(Some d) -> aux false t d; aux2 rt inp
                | O_REQUIRED -> raise (No_matching_option(t))
        | [] -> 
            match inp with
            | [] -> ()
            | x::_ -> raise (Unexpected_element x)
    and aux3 (t:list<asnval>) (v:asnval) =
        let (ct,cv) = v
        if not (List.exists (fun (ty,vl)->beq cv vl) t) then
            raise (Value_mismatch(t, v))
    aux false tpl input
    Parsed.value !res

(*
type asntag = option<int * bool> // false = explicit, true = implicit

| TPL_CHOICE of string * list<asntag * asntpl>                 // choice between tag-unambiguous options
| TPL_SEQ of bool * list<asntag * asnoption * asntpl> // fixed sequencing; flag ? SET : SEQUENCE 
| TPL_SEQOF of string * bool * (int * int) * asntpl   // unknown, homogeneous sequence, with min and max numbers of elements matching the template
| TPL_DEFINEDBY of string * list<asnval * asntpl>     // One of multiple templates based on a previous value
| TPL_ENCAPSULATED of bool * asntpl                   // flag ? Bitstring : Octet 
| TPL_CONSTANT of asnval
| TPL_VARIABLE of string * asntype * list<asnval>
*)