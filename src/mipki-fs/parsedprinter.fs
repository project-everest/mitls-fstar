module Parsedprinter

open Parsed

let parsed_print (p:parsed) =
    let rec aux pad = function
    | (k,v) :: t ->
        let x =
            match v with
            | B_VALUE(ty, b) ->
                Asn1print.asn1_print (Asn1.A_CST(ty,b))
            | B_FRAME(l) ->
                List.map (aux (pad+"  ")) l
                |> String.concat (pad + " }, {\n")
                |> fun x->"[\n" + pad + " {\n" + x + pad + " }\n" + pad + "]"
        pad + k + " : " + x + (if t=[] then "" else ",") + "\n" + (aux pad t)
    | [] -> ""
    "{\n" + (aux " " p) + "}\n"