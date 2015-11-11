module Asn1decode

open SBA
open Asn1

exception Unused_bytes
exception Invalid_header
exception Length_overflow
exception Invalid_tag
exception Invalid_length
exception Invalid_int
exception Invalid_oid
exception Invalid_bool
exception Invalid_date
exception Invalid_string
exception Invalid_bitstring

let asn1_decode (ba:byte[]) : asn1 =
    let b = create ba
    let rec aux cur =
        let mutable buf = cur
        let x,y =
            match peek buf 0 2 with
            | [x;y] -> x,y
            | _ -> raise Invalid_header

        buf <- sub buf 2 0
        let len =
            match y with
            | n when n < 128uy -> int n
            | n ->
                let ll = int (n-128uy)
                let lb = peek buf 0 ll
                buf <- sub buf ll 0
                match lb with
                | [x] -> int x
                | [x;y] -> 256*(int x) + int y
                | [x;y;z] -> 65536*(int x) + 256*(int y) + int z
                | _ -> raise Length_overflow

        if len > blen buf then raise Invalid_length
        let rest = sub buf len 0
        buf <- sub buf 0 len

        let r =
            match x with
            | 1uy ->
                if beq buf bTrue || beq buf bFalse then A_CST(C_BOOL, buf)
                else raise Invalid_bool
            | 2uy ->
                // Rules: minimum number of octets, 2 complement, 0-pad if positive and top bit is 1
                (match b2list buf with
                | 0uy :: x :: _ ->
                    if x < 128uy then raise Invalid_int
                | [] -> raise Invalid_int
                | _ -> ())
                A_CST(C_INT, buf)
            | 3uy ->
                (match b2list buf with
                | x :: t ->
                    (match List.rev t with
                    | y :: _ -> if x >= 8uy || (int y) % (1<<<(int x))<>0 then raise Invalid_bitstring
                    | _ -> raise Invalid_bitstring)
                | _ -> raise Invalid_bitstring)
                A_CST(C_STR(S_BIT), buf)
            | 4uy ->
                A_CST(C_STR(S_OCTET), buf)
            | 5uy ->
                if blen buf <> 0 then raise Invalid_length
                A_CST(C_NULL, buf)
            | 6uy ->
                try
                    let oid = List.tail (b2list buf)
                    if List.head (List.rev oid) >= 128uy then raise Invalid_oid
                with
                | _ -> raise Invalid_oid
                A_CST(C_OID, buf)
            | 12uy | 19uy | 20uy | 22uy | 28uy | 30uy ->
                let tmp = function
                | 12uy -> isUTF8, S_UTF8 | 19uy -> isPrintable, S_PRINT
                | 20uy -> isTeletex, S_TELETEX | 22uy -> isIA5, S_IA5
                | 28uy -> isUniv, S_UNIV | 30uy -> isBMP, S_BMP | _ -> raise Invalid_string
                let ver, tag = tmp x
                if not (ver buf) then
                    raise Invalid_string
                A_CST(C_STR(tag), buf)
            | 23uy | 24uy ->
                if (x=23uy && not (isDate buf)) || (x=24uy && not (isGenDate buf)) then
                    raise Invalid_date
                A_CST(C_TIME(if x=23uy then T_UTC else T_GEN), buf)
            | 48uy | 49uy ->
                let mutable elements = []
                while not (is_empty buf) do
                    let (r, extra) = aux buf
                    elements <- r::elements
                    buf <- extra
                done
                A_SEQ((x=49uy), List.rev elements)
            | n when n>=160uy && n<192uy -> // Constructed tagging
                let r, extra = aux buf
                if not (is_empty extra) then raise Unused_bytes
                A_TAG((int n) - 160, r)
            | n when n>=128uy && n<160uy -> // Implicit tagging
                A_CST(C_CUSTOM((int n)-128), buf)
            | _ ->
                A_CST(C_NULL, bEmpty)
        (r, rest)
    let (r, extra) = aux b
    if not (is_empty extra) then raise Unused_bytes
    else r