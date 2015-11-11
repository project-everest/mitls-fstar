#light "off"

module ECGroup

open Bytes
open CoreKeys

type ec_curve =
| ECC_P256
| ECC_P384
| ECC_P521

type ec_all_curve =
| EC_CORE of ec_curve
| EC_UNKNOWN of int
| EC_EXPLICIT_PRIME
| EC_EXPLICIT_BINARY

type point_format =
| ECP_UNCOMPRESSED
| ECP_UNKNOWN of int

type point = ecpoint

val getParams : ec_curve -> ecdhparams
val parse_curve : bytes -> ecdhparams option
val curve_id : ecdhparams -> bytes
val serialize_point : ecdhparams -> point -> bytes
val parse_point : ecdhparams -> bytes -> point option
val checkElement: ecdhparams -> point -> point option