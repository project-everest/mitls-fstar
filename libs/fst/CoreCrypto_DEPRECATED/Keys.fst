module CoreCrypto.Keys

open Platform.Bytes

type modulus  = bytes
type exponent = bytes

type rsapkey = modulus * exponent
type rsaskey = modulus * exponent

type dsaparams = { p : bytes; q : bytes; g : bytes; }

type dsapkey = bytes * dsaparams
type dsaskey = bytes * dsaparams

type dhparams = { dhp : bytes; dhg : bytes; dhq : bytes; safe_prime : bool }

type dhpkey = bytes
type dhskey = bytes

type ecprime = { ecp_prime : string; ecp_order : string; ecp_a : string; ecp_b : string; ecp_gx : string; ecp_gy : string; ecp_bytelen : int; ecp_id : bytes; }
type eccurve =
| EC_PRIME of ecprime

type ecpoint = { ecx : bytes; ecy : bytes; }
type ecdhparams = { curve: eccurve; compression: bool; }
type ecdhpkey = ecpoint
type ecdhskey = bytes
