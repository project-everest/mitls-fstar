module Asn1encode

open SBA
open Asn1

// DER serialization (sort SET elements in lexicographic order)

let asn1_serialize (x:asn1) : byte[] =
    let enc_len = function
    | n when n<128 -> [byte n]
    | n when n<256 -> [129uy ; byte n]
    | n when n<65535 -> [130uy ; byte (n/256) ; byte (n &&& 255)]
    | n -> [131uy ; byte (n/65536); byte ((n/256) &&& 255) ; byte (n &&& 255)]

    let rec aux = function
    | A_SEQ(f, l) ->
        let l = List.map aux l |> (if f then List.sort else fun x->x) |> List.concat
        let len = l |> List.length |> enc_len
        let t = if f then 0x31uy else 0x30uy
        t :: len @ l
    | A_TAG(n, t) ->
        let r = aux t
        let t = if n>31 then failwith "Invalid tag" else 160uy + (byte n)
        let len = List.length r |> enc_len
        t :: len @ r
    | A_ENC(f, t) ->
        let r = aux t |> (if f then fun r->0uy::r else fun r->r)
        let t = if f then 3uy else 4uy
        let len = List.length r |> enc_len
        t :: len @ r
    | A_CST(t, b) ->
        let r = b2list b
        let t = tagof t
        let len = List.length r |> enc_len
        t :: len @ r

    aux x |> List.toArray

