module Asn1

open SBA

type strkind =
| S_BIT
| S_OCTET
| S_IA5
| S_PRINT
| S_UTF8
| S_TELETEX
| S_UNIV
| S_BMP

type timekind =
| T_UTC
| T_GEN

type asntype =
| C_BOOL
| C_INT
| C_STR of strkind
| C_NULL
| C_OID
| C_TIME of timekind
| C_CUSTOM of int

type asnval = asntype * bytes

type asn1 =
| A_SEQ of bool * list<asn1> // false = seq, true = set
| A_ENC of bool * asn1       // false = octet string, true = bitstring
| A_TAG of int * asn1
| A_CST of asnval

let strtagof = function
| S_BIT -> 3uy
| S_OCTET -> 4uy
| S_IA5 -> 22uy
| S_PRINT -> 19uy
| S_UTF8 -> 12uy
| S_TELETEX -> 20uy
| S_UNIV -> 28uy
| S_BMP -> 30uy

let tagof = function
| C_BOOL -> 1uy
| C_INT -> 2uy
| C_STR(t) -> strtagof t
| C_NULL -> 5uy
| C_OID -> 6uy
| C_TIME(T_UTC) -> 23uy
| C_TIME(T_GEN) -> 24uy
| C_CUSTOM(n) -> byte (128+n)