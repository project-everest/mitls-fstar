module Asn1print

open SBA
open Asn1

let asn1_print (x:asn1) =
    let rec aux (pad:string) (x:asn1) =
        match x with
        | A_SEQ(f, l) ->
            let e = List.map (aux (pad + " ")) l
            pad + (if f then "set" else "seq") + " {\n" + (String.concat ";\n" e) + (if e=[] then "" else ";\n") + pad + "}"
        | A_ENC(f, x) ->
            pad + (if f then "bitstring" else "octet string") + ":\n" + (aux (pad + " ") x)
        | A_TAG(n, x) ->
            pad + "[" + (string n) + "]\n" + (aux (pad + " ") x)
        | A_CST(typ, b) ->
            pad +
            match typ with
            | C_BOOL -> (match b2list b with [255uy] -> "true" | _ -> "false")
            | C_INT -> (b2int b) + "L"
            | C_STR(x) ->
                match x with
                | S_UTF8 -> "u\"" + (b2str b) + "\""
                | S_PRINT -> "p\"" + (b2str b) + "\""
                | S_TELETEX -> "t\"" + (b2str b) + "\""
                | S_IA5 -> "\"" + (b2str b) + "\""
                | S_UNIV -> "u\"" + (b2str b) + "\" as universal"
                | S_BMP -> "\"" + (b2str b) + "\" as bmp"
                | S_OCTET -> "0x" + (b2hex b)
                | S_BIT -> "0x" + (b2hex b) + " as bitstring" 
            | C_OID -> "O" + (b2oid b)
            | C_TIME(k) -> "\"" + (b2str b) + "\" as " + (if k=T_UTC then "utc date" else "gen date")
            | C_NULL -> "null"
            | C_CUSTOM(n) ->
                if isPrintable b then "\"" + (b2str b) + "\" as [" + (string n) + "]"
                else "0x" + (b2hex b) + " as [" + (string n) + "]"
    aux "" x