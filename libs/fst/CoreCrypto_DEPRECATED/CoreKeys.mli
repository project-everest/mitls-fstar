(* -------------------------------------------------------------------- *)
open Bytes

type modulus  = bytes
type exponent = bytes

type rsapkey = modulus * exponent
type rsaskey = modulus * exponent

type dsaparams = { p : bytes; q : bytes; g : bytes; }

type dsapkey = bytes * dsaparams
type dsaskey = bytes * dsaparams

type dhparams = { p : bytes; g : bytes; q:bytes option; }

type dhpbytes = bytes
type dhsbytes = bytes

type dhpkey = dhpbytes * dhparams
type dhskey = dhsbytes * dhparams
